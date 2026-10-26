import V185TrunkScan23Chunk1288

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7634451 : List Nat := [1, 1, 1, 2, 1, 6, 3, 2, 1, 2, 3]
def baseStart_7634451 : Nat := 118140960795 + 7634451 * 2 ^ 59
def prefixEnd_7634451 : Nat := 4983230072969 + 3 ^ 40 * 7634451 * 2
def baseEnd_7634451 : Nat := 3920142896198414909052305

theorem tailTrace_7634451 : CollatzResearch.WordTrace tailWord_7634451 prefixEnd_7634451 3920142896198414909052305 := by
  unfold tailWord_7634451
  simp only [CollatzResearch.WordTrace]
  refine ⟨278451303664695362270279207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185634202443130241513519471 278451303664695362270279207)
  ·
    refine ⟨417676955497043043405418811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278451303664695362270279207 417676955497043043405418811)
    ·
      refine ⟨626515433245564565108128217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417676955497043043405418811 626515433245564565108128217)
      ·
        refine ⟨469886574934173423831096163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626515433245564565108128217 469886574934173423831096163)
        ·
          refine ⟨704829862401260135746644245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469886574934173423831096163 704829862401260135746644245)
          ·
            refine ⟨33038899800059068863123949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 704829862401260135746644245 33038899800059068863123949)
            ·
              refine ⟨12389587425022150823671481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33038899800059068863123949 12389587425022150823671481)
              ·
                refine ⟨9292190568766613117753611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12389587425022150823671481 9292190568766613117753611)
                ·
                  refine ⟨13938285853149919676630417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9292190568766613117753611 13938285853149919676630417)
                  ·
                    refine ⟨10453714389862439757472813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13938285853149919676630417 10453714389862439757472813)
                    ·
                      refine ⟨3920142896198414909052305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10453714389862439757472813 3920142896198414909052305)
                      ·
                        rfl

theorem cell23_7634451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 2, 3].length) (baseStart_7634451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634451 prefixEnd_7634451 := by exact prefixLift 7634451
  have htrace : WordTrace (prefixWord ++ tailWord_7634451) baseStart_7634451 baseEnd_7634451 := by
    simpa [prefixWord, tailWord_7634451, baseEnd_7634451] using wordTrace_append hprefix tailTrace_7634451
  have hstable : (prefixWord ++ tailWord_7634451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634451).length < 2 ^ (prefixWord ++ tailWord_7634451).sum := by decide
  have hdescent : baseEnd_7634451 < baseStart_7634451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634544 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 7]
def baseStart_7634544 : Nat := 118140960795 + 7634544 * 2 ^ 59
def prefixEnd_7634544 : Nat := 4983230072969 + 3 ^ 40 * 7634544 * 2
def baseEnd_7634544 : Nat := 435576738877698116132153

theorem tailTrace_7634544 : CollatzResearch.WordTrace tailWord_7634544 prefixEnd_7634544 435576738877698116132153 := by
  unfold tailWord_7634544
  simp only [CollatzResearch.WordTrace]
  refine ⟨139227347826679219576707343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185636463768905626102276457 139227347826679219576707343)
  ·
    refine ⟨208841021740018829365061015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139227347826679219576707343 208841021740018829365061015)
    ·
      refine ⟨313261532610028244047591523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208841021740018829365061015 313261532610028244047591523)
      ·
        refine ⟨469892298915042366071387285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313261532610028244047591523 469892298915042366071387285)
        ·
          refine ⟨22026201511642610909596279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 469892298915042366071387285 22026201511642610909596279)
          ·
            refine ⟨33039302267463916364394419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22026201511642610909596279 33039302267463916364394419)
            ·
              refine ⟨49558953401195874546591629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33039302267463916364394419 49558953401195874546591629)
              ·
                refine ⟨18584607525448452954971861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49558953401195874546591629 18584607525448452954971861)
                ·
                  refine ⟨435576738877698116132153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18584607525448452954971861 435576738877698116132153)
                  ·
                    rfl

theorem cell23_7634544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 7].length) (baseStart_7634544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634544 prefixEnd_7634544 := by exact prefixLift 7634544
  have htrace : WordTrace (prefixWord ++ tailWord_7634544) baseStart_7634544 baseEnd_7634544 := by
    simpa [prefixWord, tailWord_7634544, baseEnd_7634544] using wordTrace_append hprefix tailTrace_7634544
  have hstable : (prefixWord ++ tailWord_7634544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634544).length < 2 ^ (prefixWord ++ tailWord_7634544).sum := by decide
  have hdescent : baseEnd_7634544 < baseStart_7634544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634554 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3]
def baseStart_7634554 : Nat := 118140960795 + 7634554 * 2 ^ 59
def prefixEnd_7634554 : Nat := 4983230072969 + 3 ^ 40 * 7634554 * 2
def baseEnd_7634554 : Nat := 3920195784705828006064331

theorem tailTrace_7634554 : CollatzResearch.WordTrace tailWord_7634554 prefixEnd_7634554 3920195784705828006064331 := by
  unfold tailWord_7634554
  simp only [CollatzResearch.WordTrace]
  refine ⟨69613765095830552715319679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185636706922214807240852477 69613765095830552715319679)
  ·
    refine ⟨104420647643745829072979519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69613765095830552715319679 104420647643745829072979519)
    ·
      refine ⟨156630971465618743609469279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104420647643745829072979519 156630971465618743609469279)
      ·
        refine ⟨234946457198428115414203919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156630971465618743609469279 234946457198428115414203919)
        ·
          refine ⟨352419685797642173121305879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234946457198428115414203919 352419685797642173121305879)
          ·
            refine ⟨528629528696463259681958819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352419685797642173121305879 528629528696463259681958819)
            ·
              refine ⟨792944293044694889522938229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528629528696463259681958819 792944293044694889522938229)
              ·
                refine ⟨74338527472940145892775459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 792944293044694889522938229 74338527472940145892775459)
                ·
                  refine ⟨111507791209410218839163189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74338527472940145892775459 111507791209410218839163189)
                  ·
                    refine ⟨10453855425882208016171549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111507791209410218839163189 10453855425882208016171549)
                    ·
                      refine ⟨3920195784705828006064331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10453855425882208016171549 3920195784705828006064331)
                      ·
                        rfl

theorem cell23_7634554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_7634554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634554 prefixEnd_7634554 := by exact prefixLift 7634554
  have htrace : WordTrace (prefixWord ++ tailWord_7634554) baseStart_7634554 baseEnd_7634554 := by
    simpa [prefixWord, tailWord_7634554, baseEnd_7634554] using wordTrace_append hprefix tailTrace_7634554
  have hstable : (prefixWord ++ tailWord_7634554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634554).length < 2 ^ (prefixWord ++ tailWord_7634554).sum := by decide
  have hdescent : baseEnd_7634554 < baseStart_7634554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634555 : List Nat := [1, 1, 1, 1, 1, 4, 7, 1, 2, 2, 2]
def baseStart_7634555 : Nat := 118140960795 + 7634555 * 2 ^ 59
def prefixEnd_7634555 : Nat := 4983230072969 + 3 ^ 40 * 7634555 * 2
def baseEnd_7634555 : Nat := 3920196298186482502151827

theorem tailTrace_7634555 : CollatzResearch.WordTrace tailWord_7634555 prefixEnd_7634555 3920196298186482502151827 := by
  unfold tailWord_7634555
  simp only [CollatzResearch.WordTrace]
  refine ⟨278455096856318588032065119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185636731237545725354710079 278455096856318588032065119)
  ·
    refine ⟨417682645284477882048097679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278455096856318588032065119 417682645284477882048097679)
    ·
      refine ⟨626523967926716823072146519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417682645284477882048097679 626523967926716823072146519)
      ·
        refine ⟨939785951890075234608219779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626523967926716823072146519 939785951890075234608219779)
        ·
          refine ⟨1409678927835112851912329669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939785951890075234608219779 1409678927835112851912329669)
          ·
            refine ⟨264314798969083659733561813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1409678927835112851912329669 264314798969083659733561813)
            ·
              refine ⟨6194878100837898275005355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 264314798969083659733561813 6194878100837898275005355)
              ·
                refine ⟨9292317151256847412508033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6194878100837898275005355 9292317151256847412508033)
                ·
                  refine ⟨6969237863442635559381025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9292317151256847412508033 6969237863442635559381025)
                  ·
                    refine ⟨5226928397581976669535769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6969237863442635559381025 5226928397581976669535769)
                    ·
                      refine ⟨3920196298186482502151827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5226928397581976669535769 3920196298186482502151827)
                      ·
                        rfl

theorem cell23_7634555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 2, 2, 2].length) (baseStart_7634555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634555 prefixEnd_7634555 := by exact prefixLift 7634555
  have htrace : WordTrace (prefixWord ++ tailWord_7634555) baseStart_7634555 baseEnd_7634555 := by
    simpa [prefixWord, tailWord_7634555, baseEnd_7634555] using wordTrace_append hprefix tailTrace_7634555
  have hstable : (prefixWord ++ tailWord_7634555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634555).length < 2 ^ (prefixWord ++ tailWord_7634555).sum := by decide
  have hdescent : baseEnd_7634555 < baseStart_7634555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634606 : List Nat := [4, 1, 4, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_7634606 : Nat := 118140960795 + 7634606 * 2 ^ 59
def prefixEnd_7634606 : Nat := 4983230072969 + 3 ^ 40 * 7634606 * 2
def baseEnd_7634606 : Nat := 3920222485699861802614093

theorem tailTrace_7634606 : CollatzResearch.WordTrace tailWord_7634606 prefixEnd_7634606 3920222485699861802614093 := by
  unfold tailWord_7634606
  simp only [CollatzResearch.WordTrace]
  refine ⟨34807119622391727967771459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185637971319422549161447781 34807119622391727967771459)
  ·
    refine ⟨52210679433587591951657189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34807119622391727967771459 52210679433587591951657189)
    ·
      refine ⟨9789502393797673490935723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52210679433587591951657189 9789502393797673490935723)
      ·
        refine ⟨14684253590696510236403585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9789502393797673490935723 14684253590696510236403585)
        ·
          refine ⟨11013190193022382677302689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14684253590696510236403585 11013190193022382677302689)
          ·
            refine ⟨8259892644766787007977017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11013190193022382677302689 8259892644766787007977017)
            ·
              refine ⟨6194919483575090255982763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8259892644766787007977017 6194919483575090255982763)
              ·
                refine ⟨9292379225362635383974145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6194919483575090255982763 9292379225362635383974145)
                ·
                  refine ⟨6969284419021976537980609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9292379225362635383974145 6969284419021976537980609)
                  ·
                    refine ⟨5226963314266482403485457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6969284419021976537980609 5226963314266482403485457)
                    ·
                      refine ⟨3920222485699861802614093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5226963314266482403485457 3920222485699861802614093)
                      ·
                        rfl

theorem cell23_7634606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_7634606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634606 prefixEnd_7634606 := by exact prefixLift 7634606
  have htrace : WordTrace (prefixWord ++ tailWord_7634606) baseStart_7634606 baseEnd_7634606 := by
    simpa [prefixWord, tailWord_7634606, baseEnd_7634606] using wordTrace_append hprefix tailTrace_7634606
  have hstable : (prefixWord ++ tailWord_7634606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634606).length < 2 ^ (prefixWord ++ tailWord_7634606).sum := by decide
  have hdescent : baseEnd_7634606 < baseStart_7634606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634611 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 1, 6, 2]
def baseStart_7634611 : Nat := 118140960795 + 7634611 * 2 ^ 59
def prefixEnd_7634611 : Nat := 4983230072969 + 3 ^ 40 * 7634611 * 2
def baseEnd_7634611 : Nat := 3920225053103134283051569

theorem tailTrace_7634611 : CollatzResearch.WordTrace tailWord_7634611 prefixEnd_7634611 3920225053103134283051569 := by
  unfold tailWord_7634611
  simp only [CollatzResearch.WordTrace]
  refine ⟨278457139344115709596103687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185638092896077139730735791 278457139344115709596103687)
  ·
    refine ⟨417685709016173564394155531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278457139344115709596103687 417685709016173564394155531)
    ·
      refine ⟨626528563524260346591233297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417685709016173564394155531 626528563524260346591233297)
      ·
        refine ⟨469896422643195259943424973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626528563524260346591233297 469896422643195259943424973)
        ·
          refine ⟨176211158491198222478784365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469896422643195259943424973 176211158491198222478784365)
          ·
            refine ⟨66079184434199333429544137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176211158491198222478784365 66079184434199333429544137)
            ·
              refine ⟨49559388325649500072158103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66079184434199333429544137 49559388325649500072158103)
              ·
                refine ⟨74339082488474250108237155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49559388325649500072158103 74339082488474250108237155)
                ·
                  refine ⟨111508623732711375162355733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74339082488474250108237155 111508623732711375162355733)
                  ·
                    refine ⟨5226966737470845710735425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111508623732711375162355733 5226966737470845710735425)
                    ·
                      refine ⟨3920225053103134283051569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5226966737470845710735425 3920225053103134283051569)
                      ·
                        rfl

theorem cell23_7634611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 6, 2].length) (baseStart_7634611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634611 prefixEnd_7634611 := by exact prefixLift 7634611
  have htrace : WordTrace (prefixWord ++ tailWord_7634611) baseStart_7634611 baseEnd_7634611 := by
    simpa [prefixWord, tailWord_7634611, baseEnd_7634611] using wordTrace_append hprefix tailTrace_7634611
  have hstable : (prefixWord ++ tailWord_7634611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634611).length < 2 ^ (prefixWord ++ tailWord_7634611).sum := by decide
  have hdescent : baseEnd_7634611 < baseStart_7634611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634621 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 5, 4]
def baseStart_7634621 : Nat := 118140960795 + 7634621 * 2 ^ 59
def prefixEnd_7634621 : Nat := 4983230072969 + 3 ^ 40 * 7634621 * 2
def baseEnd_7634621 : Nat := 1306743395969893081308841

theorem tailTrace_7634621 : CollatzResearch.WordTrace tailWord_7634621 prefixEnd_7634621 1306743395969893081308841 := by
  unfold tailWord_7634621
  simp only [CollatzResearch.WordTrace]
  refine ⟨278457504074079481303967717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185638336049386320869311811 278457504074079481303967717)
  ·
    refine ⟨52210782013889902744493947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278457504074079481303967717 52210782013889902744493947)
    ·
      refine ⟨78316173020834854116740921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52210782013889902744493947 78316173020834854116740921)
      ·
        refine ⟨58737129765626140587555691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78316173020834854116740921 58737129765626140587555691)
        ·
          refine ⟨88105694648439210881333537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58737129765626140587555691 88105694648439210881333537)
          ·
            refine ⟨66079270986329408161000153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88105694648439210881333537 66079270986329408161000153)
            ·
              refine ⟨49559453239747056120750115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66079270986329408161000153 49559453239747056120750115)
              ·
                refine ⟨74339179859620584181125173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49559453239747056120750115 74339179859620584181125173)
                ·
                  refine ⟨6969298111839429766980485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74339179859620584181125173 6969298111839429766980485)
                  ·
                    refine ⟨1306743395969893081308841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6969298111839429766980485 1306743395969893081308841)
                    ·
                      rfl

theorem cell23_7634621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_7634621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634621 prefixEnd_7634621 := by exact prefixLift 7634621
  have htrace : WordTrace (prefixWord ++ tailWord_7634621) baseStart_7634621 baseEnd_7634621 := by
    simpa [prefixWord, tailWord_7634621, baseEnd_7634621] using wordTrace_append hprefix tailTrace_7634621
  have hstable : (prefixWord ++ tailWord_7634621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634621).length < 2 ^ (prefixWord ++ tailWord_7634621).sum := by decide
  have hdescent : baseEnd_7634621 < baseStart_7634621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634628 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_7634628 : Nat := 118140960795 + 7634628 * 2 ^ 59
def prefixEnd_7634628 : Nat := 4983230072969 + 3 ^ 40 * 7634628 * 2
def baseEnd_7634628 : Nat := 3920233782274260716538991

theorem tailTrace_7634628 : CollatzResearch.WordTrace tailWord_7634628 prefixEnd_7634628 3920233782274260716538991 := by
  unfold tailWord_7634628
  simp only [CollatzResearch.WordTrace]
  refine ⟨139228879692527060749736269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185638506256702747666315025 139228879692527060749736269)
  ·
    refine ⟨52210829884697647781151101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139228879692527060749736269 52210829884697647781151101)
    ·
      refine ⟨19579061206761617917931663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52210829884697647781151101 19579061206761617917931663)
      ·
        refine ⟨29368591810142426876897495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19579061206761617917931663 29368591810142426876897495)
        ·
          refine ⟨44052887715213640315346243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29368591810142426876897495 44052887715213640315346243)
          ·
            refine ⟨66079331572820460473019365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44052887715213640315346243 66079331572820460473019365)
            ·
              refine ⟨12389874669903836338691131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66079331572820460473019365 12389874669903836338691131)
              ·
                refine ⟨18584812004855754508036697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12389874669903836338691131 18584812004855754508036697)
                ·
                  refine ⟨13938609003641815881027523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18584812004855754508036697 13938609003641815881027523)
                  ·
                    refine ⟨20907913505462723821541285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13938609003641815881027523 20907913505462723821541285)
                    ·
                      refine ⟨3920233782274260716538991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20907913505462723821541285 3920233782274260716538991)
                      ·
                        rfl

theorem cell23_7634628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_7634628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634628 prefixEnd_7634628 := by exact prefixLift 7634628
  have htrace : WordTrace (prefixWord ++ tailWord_7634628) baseStart_7634628 baseEnd_7634628 := by
    simpa [prefixWord, tailWord_7634628, baseEnd_7634628] using wordTrace_append hprefix tailTrace_7634628
  have hstable : (prefixWord ++ tailWord_7634628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634628).length < 2 ^ (prefixWord ++ tailWord_7634628).sum := by decide
  have hdescent : baseEnd_7634628 < baseStart_7634628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634646 : List Nat := [5, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_7634646 : Nat := 118140960795 + 7634646 * 2 ^ 59
def prefixEnd_7634646 : Nat := 4983230072969 + 3 ^ 40 * 7634646 * 2
def baseEnd_7634646 : Nat := 435582558325115738457101

theorem tailTrace_7634646 : CollatzResearch.WordTrace tailWord_7634646 prefixEnd_7634646 435582558325115738457101 := by
  unfold tailWord_7634646
  simp only [CollatzResearch.WordTrace]
  refine ⟨17403650993686806910851737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185638943932659273715751861 17403650993686806910851737)
  ·
    refine ⟨13052738245265105183138803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17403650993686806910851737 13052738245265105183138803)
    ·
      refine ⟨19579107367897657774708205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13052738245265105183138803 19579107367897657774708205)
      ·
        refine ⟨7342165262961621665515577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19579107367897657774708205 7342165262961621665515577)
        ·
          refine ⟨5506623947221216249136683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7342165262961621665515577 5506623947221216249136683)
          ·
            refine ⟨8259935920831824373705025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5506623947221216249136683 8259935920831824373705025)
            ·
              refine ⟨6194951940623868280278769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8259935920831824373705025 6194951940623868280278769)
              ·
                refine ⟨4646213955467901210209077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6194951940623868280278769 4646213955467901210209077)
                ·
                  refine ⟨435582558325115738457101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4646213955467901210209077 435582558325115738457101)
                  ·
                    rfl

theorem cell23_7634646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_7634646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634646 prefixEnd_7634646 := by exact prefixLift 7634646
  have htrace : WordTrace (prefixWord ++ tailWord_7634646) baseStart_7634646 baseEnd_7634646 := by
    simpa [prefixWord, tailWord_7634646, baseEnd_7634646] using wordTrace_append hprefix tailTrace_7634646
  have hstable : (prefixWord ++ tailWord_7634646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634646).length < 2 ^ (prefixWord ++ tailWord_7634646).sum := by decide
  have hdescent : baseEnd_7634646 < baseStart_7634646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634698 : List Nat := [3, 1, 2, 2, 1, 4, 1, 3, 1, 5]
def baseStart_7634698 : Nat := 118140960795 + 7634698 * 2 ^ 59
def prefixEnd_7634698 : Nat := 4983230072969 + 3 ^ 40 * 7634698 * 2
def baseEnd_7634698 : Nat := 1306756575306691814221223

theorem tailTrace_7634698 : CollatzResearch.WordTrace tailWord_7634698 prefixEnd_7634698 1306756575306691814221223 := by
  unfold tailWord_7634698
  simp only [CollatzResearch.WordTrace]
  refine ⟨69615078123700130863630187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185640208329867015636347165 69615078123700130863630187)
  ·
    refine ⟨104422617185550196295445281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69615078123700130863630187 104422617185550196295445281)
    ·
      refine ⟨78316962889162647221583961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104422617185550196295445281 78316962889162647221583961)
      ·
        refine ⟨58737722166871985416187971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78316962889162647221583961 58737722166871985416187971)
        ·
          refine ⟨88106583250307978124281957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58737722166871985416187971 88106583250307978124281957)
          ·
            refine ⟨16519984359432745898302867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88106583250307978124281957 16519984359432745898302867)
            ·
              refine ⟨24779976539149118847454301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16519984359432745898302867 24779976539149118847454301)
              ·
                refine ⟨9292491202180919567795363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24779976539149118847454301 9292491202180919567795363)
                ·
                  refine ⟨13938736803271379351693045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9292491202180919567795363 13938736803271379351693045)
                  ·
                    refine ⟨1306756575306691814221223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13938736803271379351693045 1306756575306691814221223)
                    ·
                      rfl

theorem cell23_7634698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_7634698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634698 prefixEnd_7634698 := by exact prefixLift 7634698
  have htrace : WordTrace (prefixWord ++ tailWord_7634698) baseStart_7634698 baseEnd_7634698 := by
    simpa [prefixWord, tailWord_7634698, baseEnd_7634698] using wordTrace_append hprefix tailTrace_7634698
  have hstable : (prefixWord ++ tailWord_7634698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634698).length < 2 ^ (prefixWord ++ tailWord_7634698).sum := by decide
  have hdescent : baseEnd_7634698 < baseStart_7634698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634721 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_7634721 : Nat := 118140960795 + 7634721 * 2 ^ 59
def prefixEnd_7634721 : Nat := 4983230072969 + 3 ^ 40 * 7634721 * 2
def baseEnd_7634721 : Nat := 3920281535975128852676063

theorem tailTrace_7634721 : CollatzResearch.WordTrace tailWord_7634721 prefixEnd_7634721 3920281535975128852676063 := by
  unfold tailWord_7634721
  simp only [CollatzResearch.WordTrace]
  refine ⟨278461151373717198382608017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185640767582478132255072011 278461151373717198382608017)
  ·
    refine ⟨208845863530287898786956013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278461151373717198382608017 208845863530287898786956013)
    ·
      refine ⟨78317198823857962045108505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208845863530287898786956013 78317198823857962045108505)
      ·
        refine ⟨58737899117893471533831379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78317198823857962045108505 58737899117893471533831379)
        ·
          refine ⟨88106848676840207300747069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58737899117893471533831379 88106848676840207300747069)
          ·
            refine ⟨33040068253815077737780151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88106848676840207300747069 33040068253815077737780151)
            ·
              refine ⟨49560102380722616606670227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33040068253815077737780151 49560102380722616606670227)
              ·
                refine ⟨74340153571083924910005341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49560102380722616606670227 74340153571083924910005341)
                ·
                  refine ⟨27877557589156471841252003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74340153571083924910005341 27877557589156471841252003)
                  ·
                    refine ⟨41816336383734707761878005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27877557589156471841252003 41816336383734707761878005)
                    ·
                      refine ⟨3920281535975128852676063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41816336383734707761878005 3920281535975128852676063)
                      ·
                        rfl

theorem cell23_7634721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_7634721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634721 prefixEnd_7634721 := by exact prefixLift 7634721
  have htrace : WordTrace (prefixWord ++ tailWord_7634721) baseStart_7634721 baseEnd_7634721 := by
    simpa [prefixWord, tailWord_7634721, baseEnd_7634721] using wordTrace_append hprefix tailTrace_7634721
  have hstable : (prefixWord ++ tailWord_7634721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634721).length < 2 ^ (prefixWord ++ tailWord_7634721).sum := by decide
  have hdescent : baseEnd_7634721 < baseStart_7634721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634728 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 1, 6]
def baseStart_7634728 : Nat := 118140960795 + 7634728 * 2 ^ 59
def prefixEnd_7634728 : Nat := 4983230072969 + 3 ^ 40 * 7634728 * 2
def baseEnd_7634728 : Nat := 1306761710113236775096177

theorem tailTrace_7634728 : CollatzResearch.WordTrace tailWord_7634728 prefixEnd_7634728 1306761710113236775096177 := by
  unfold tailWord_7634728
  simp only [CollatzResearch.WordTrace]
  refine ⟨139230703342345919289056419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185640937789794559052075225 139230703342345919289056419)
  ·
    refine ⟨208846055013518878933584629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139230703342345919289056419 208846055013518878933584629)
    ·
      refine ⟨19579317657517394900023559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208846055013518878933584629 19579317657517394900023559)
      ·
        refine ⟨29368976486276092350035339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19579317657517394900023559 29368976486276092350035339)
        ·
          refine ⟨44053464729414138525053009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29368976486276092350035339 44053464729414138525053009)
          ·
            refine ⟨33040098547060603893789757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44053464729414138525053009 33040098547060603893789757)
            ·
              refine ⟨12390036955147726460171159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33040098547060603893789757 12390036955147726460171159)
              ·
                refine ⟨18585055432721589690256739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12390036955147726460171159 18585055432721589690256739)
                ·
                  refine ⟨27877583149082384535385109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18585055432721589690256739 27877583149082384535385109)
                  ·
                    refine ⟨1306761710113236775096177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27877583149082384535385109 1306761710113236775096177)
                    ·
                      rfl

theorem cell23_7634728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_7634728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634728 prefixEnd_7634728 := by exact prefixLift 7634728
  have htrace : WordTrace (prefixWord ++ tailWord_7634728) baseStart_7634728 baseEnd_7634728 := by
    simpa [prefixWord, tailWord_7634728, baseEnd_7634728] using wordTrace_append hprefix tailTrace_7634728
  have hstable : (prefixWord ++ tailWord_7634728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634728).length < 2 ^ (prefixWord ++ tailWord_7634728).sum := by decide
  have hdescent : baseEnd_7634728 < baseStart_7634728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634785 : List Nat := [1, 2, 3, 1, 1, 1, 5, 3, 2, 1, 3]
def baseStart_7634785 : Nat := 118140960795 + 7634785 * 2 ^ 59
def prefixEnd_7634785 : Nat := 4983230072969 + 3 ^ 40 * 7634785 * 2
def baseEnd_7634785 : Nat := 3920314398737016602275769

theorem tailTrace_7634785 : CollatzResearch.WordTrace tailWord_7634785 prefixEnd_7634785 3920314398737016602275769 := by
  unfold tailWord_7634785
  simp only [CollatzResearch.WordTrace]
  refine ⟨278463485645485337312937809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185642323763656891541958539 278463485645485337312937809)
  ·
    refine ⟨208847614234114002984703357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278463485645485337312937809 208847614234114002984703357)
    ·
      refine ⟨78317855337792751119263759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208847614234114002984703357 78317855337792751119263759)
      ·
        refine ⟨117476783006689126678895639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78317855337792751119263759 117476783006689126678895639)
        ·
          refine ⟨176215174510033690018343459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117476783006689126678895639 176215174510033690018343459)
          ·
            refine ⟨264322761765050535027515189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176215174510033690018343459 264322761765050535027515189)
            ·
              refine ⟨24780258915473487658829549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264322761765050535027515189 24780258915473487658829549)
              ·
                refine ⟨9292597093302557872061081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24780258915473487658829549 9292597093302557872061081)
                ·
                  refine ⟨6969447819976918404045811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9292597093302557872061081 6969447819976918404045811)
                  ·
                    refine ⟨10454171729965377606068717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6969447819976918404045811 10454171729965377606068717)
                    ·
                      refine ⟨3920314398737016602275769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10454171729965377606068717 3920314398737016602275769)
                      ·
                        rfl

theorem cell23_7634785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_7634785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634785 prefixEnd_7634785 := by exact prefixLift 7634785
  have htrace : WordTrace (prefixWord ++ tailWord_7634785) baseStart_7634785 baseEnd_7634785 := by
    simpa [prefixWord, tailWord_7634785, baseEnd_7634785] using wordTrace_append hprefix tailTrace_7634785
  have hstable : (prefixWord ++ tailWord_7634785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634785).length < 2 ^ (prefixWord ++ tailWord_7634785).sum := by decide
  have hdescent : baseEnd_7634785 < baseStart_7634785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634842 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2]
def baseStart_7634842 : Nat := 118140960795 + 7634842 * 2 ^ 59
def prefixEnd_7634842 : Nat := 4983230072969 + 3 ^ 40 * 7634842 * 2
def baseEnd_7634842 : Nat := 3920343667134322879263007

theorem tailTrace_7634842 : CollatzResearch.WordTrace tailWord_7634842 prefixEnd_7634842 3920343667134322879263007 := by
  unfold tailWord_7634842
  simp only [CollatzResearch.WordTrace]
  refine ⟨69616391151569709011940695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185643709737519224031841853 69616391151569709011940695)
  ·
    refine ⟨104424586727354563517911043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69616391151569709011940695 104424586727354563517911043)
    ·
      refine ⟨156636880091031845276866565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104424586727354563517911043 156636880091031845276866565)
      ·
        refine ⟨29369415017068470989412481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156636880091031845276866565 29369415017068470989412481)
        ·
          refine ⟨22027061262801353242059361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29369415017068470989412481 22027061262801353242059361)
          ·
            refine ⟨16520295947101014931544521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22027061262801353242059361 16520295947101014931544521)
            ·
              refine ⟨12390221960325761198658391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16520295947101014931544521 12390221960325761198658391)
              ·
                refine ⟨18585332940488641797987587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12390221960325761198658391 18585332940488641797987587)
                ·
                  refine ⟨27877999410732962696981381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18585332940488641797987587 27877999410732962696981381)
                  ·
                    refine ⟨5227124889512430505684009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27877999410732962696981381 5227124889512430505684009)
                    ·
                      refine ⟨3920343667134322879263007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5227124889512430505684009 3920343667134322879263007)
                      ·
                        rfl

theorem cell23_7634842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_7634842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634842 prefixEnd_7634842 := by exact prefixLift 7634842
  have htrace : WordTrace (prefixWord ++ tailWord_7634842) baseStart_7634842 baseEnd_7634842 := by
    simpa [prefixWord, tailWord_7634842, baseEnd_7634842] using wordTrace_append hprefix tailTrace_7634842
  have hstable : (prefixWord ++ tailWord_7634842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634842).length < 2 ^ (prefixWord ++ tailWord_7634842).sum := by decide
  have hdescent : baseEnd_7634842 < baseStart_7634842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634865 : List Nat := [1, 2, 2, 4, 2, 1, 1, 5, 5]
def baseStart_7634865 : Nat := 118140960795 + 7634865 * 2 ^ 59
def prefixEnd_7634865 : Nat := 4983230072969 + 3 ^ 40 * 7634865 * 2
def baseEnd_7634865 : Nat := 435595053021041809919489

theorem tailTrace_7634865 : CollatzResearch.WordTrace tailWord_7634865 prefixEnd_7634865 435595053021041809919489 := by
  unfold tailWord_7634865
  simp only [CollatzResearch.WordTrace]
  refine ⟨278466403485195510975850049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185644268990130340650566699 278466403485195510975850049)
  ·
    refine ⟨208849802613896633231887537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278466403485195510975850049 208849802613896633231887537)
    ·
      refine ⟨156637351960422474923915653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208849802613896633231887537 156637351960422474923915653)
      ·
        refine ⟨29369503492579214048234185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156637351960422474923915653 29369503492579214048234185)
        ·
          refine ⟨22027127619434410536175639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29369503492579214048234185 22027127619434410536175639)
          ·
            refine ⟨33040691429151615804263459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22027127619434410536175639 33040691429151615804263459)
            ·
              refine ⟨49561037143727423706395189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33040691429151615804263459 49561037143727423706395189)
              ·
                refine ⟨4646347232224445972474549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49561037143727423706395189 4646347232224445972474549)
                ·
                  refine ⟨435595053021041809919489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4646347232224445972474549 435595053021041809919489)
                  ·
                    rfl

theorem cell23_7634865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 5].length) (baseStart_7634865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634865 prefixEnd_7634865 := by exact prefixLift 7634865
  have htrace : WordTrace (prefixWord ++ tailWord_7634865) baseStart_7634865 baseEnd_7634865 := by
    simpa [prefixWord, tailWord_7634865, baseEnd_7634865] using wordTrace_append hprefix tailTrace_7634865
  have hstable : (prefixWord ++ tailWord_7634865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634865).length < 2 ^ (prefixWord ++ tailWord_7634865).sum := by decide
  have hdescent : baseEnd_7634865 < baseStart_7634865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634992 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 2, 3, 2]
def baseStart_7634992 : Nat := 118140960795 + 7634992 * 2 ^ 59
def prefixEnd_7634992 : Nat := 4983230072969 + 3 ^ 40 * 7634992 * 2
def baseEnd_7634992 : Nat := 3920420689232497292387317

theorem tailTrace_7634992 : CollatzResearch.WordTrace tailWord_7634992 prefixEnd_7634992 3920420689232497292387317 := by
  unfold tailWord_7634992
  simp only [CollatzResearch.WordTrace]
  refine ⟨139235517777867705832861615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185647357037156941110482153 139235517777867705832861615)
  ·
    refine ⟨208853276666801558749292423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139235517777867705832861615 208853276666801558749292423)
    ·
      refine ⟨313279915000202338123938635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208853276666801558749292423 313279915000202338123938635)
      ·
        refine ⟨469919872500303507185907953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313279915000202338123938635 469919872500303507185907953)
        ·
          refine ⟨352439904375227630389430965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469919872500303507185907953 352439904375227630389430965)
          ·
            refine ⟨33041241035177590349009153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 352439904375227630389430965 33041241035177590349009153)
            ·
              refine ⟨24780930776383192761756865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33041241035177590349009153 24780930776383192761756865)
              ·
                refine ⟨18585698082287394571317649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24780930776383192761756865 18585698082287394571317649)
                ·
                  refine ⟨13939273561715545928488237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18585698082287394571317649 13939273561715545928488237)
                  ·
                    refine ⟨5227227585643329723183089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13939273561715545928488237 5227227585643329723183089)
                    ·
                      refine ⟨3920420689232497292387317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5227227585643329723183089 3920420689232497292387317)
                      ·
                        rfl

theorem cell23_7634992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 2, 3, 2].length) (baseStart_7634992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634992 prefixEnd_7634992 := by exact prefixLift 7634992
  have htrace : WordTrace (prefixWord ++ tailWord_7634992) baseStart_7634992 baseEnd_7634992 := by
    simpa [prefixWord, tailWord_7634992, baseEnd_7634992] using wordTrace_append hprefix tailTrace_7634992
  have hstable : (prefixWord ++ tailWord_7634992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634992).length < 2 ^ (prefixWord ++ tailWord_7634992).sum := by decide
  have hdescent : baseEnd_7634992 < baseStart_7634992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635005 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_7635005 : Nat := 118140960795 + 7635005 * 2 ^ 59
def prefixEnd_7635005 : Nat := 4983230072969 + 3 ^ 40 * 7635005 * 2
def baseEnd_7635005 : Nat := 3920427364481005741524757

theorem tailTrace_7635005 : CollatzResearch.WordTrace tailWord_7635005 prefixEnd_7635005 3920427364481005741524757 := by
  unfold tailWord_7635005
  simp only [CollatzResearch.WordTrace]
  refine ⟨278471509704688314885946469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185647673136458876590630979 278471509704688314885946469)
  ·
    refine ⟨52213408069629059041114963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278471509704688314885946469 52213408069629059041114963)
    ·
      refine ⟨78320112104443588561672445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52213408069629059041114963 78320112104443588561672445)
      ·
        refine ⟨29370042039166345710627167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78320112104443588561672445 29370042039166345710627167)
        ·
          refine ⟨44055063058749518565940751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29370042039166345710627167 44055063058749518565940751)
          ·
            refine ⟨66082594588124277848911127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44055063058749518565940751 66082594588124277848911127)
            ·
              refine ⟨99123891882186416773366691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66082594588124277848911127 99123891882186416773366691)
              ·
                refine ⟨148685837823279625160050037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99123891882186416773366691 148685837823279625160050037)
                ·
                  refine ⟨13939297295932464858754691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148685837823279625160050037 13939297295932464858754691)
                  ·
                    refine ⟨20908945943898697288132037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13939297295932464858754691 20908945943898697288132037)
                    ·
                      refine ⟨3920427364481005741524757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20908945943898697288132037 3920427364481005741524757)
                      ·
                        rfl

theorem cell23_7635005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_7635005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635005 prefixEnd_7635005 := by exact prefixLift 7635005
  have htrace : WordTrace (prefixWord ++ tailWord_7635005) baseStart_7635005 baseEnd_7635005 := by
    simpa [prefixWord, tailWord_7635005, baseEnd_7635005] using wordTrace_append hprefix tailTrace_7635005
  have hstable : (prefixWord ++ tailWord_7635005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635005).length < 2 ^ (prefixWord ++ tailWord_7635005).sum := by decide
  have hdescent : baseEnd_7635005 < baseStart_7635005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635015 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 1, 6]
def baseStart_7635015 : Nat := 118140960795 + 7635015 * 2 ^ 59
def prefixEnd_7635015 : Nat := 4983230072969 + 3 ^ 40 * 7635015 * 2
def baseEnd_7635015 : Nat := 1306810833095850234133237

theorem tailTrace_7635015 : CollatzResearch.WordTrace tailWord_7635015 prefixEnd_7635015 1306810833095850234133237 := by
  unfold tailWord_7635015
  simp only [CollatzResearch.WordTrace]
  refine ⟨278471874434652086593810499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185647916289768057729206999 278471874434652086593810499)
  ·
    refine ⟨417707811651978129890715749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278471874434652086593810499 417707811651978129890715749)
    ·
      refine ⟨78320214684745899354509203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417707811651978129890715749 78320214684745899354509203)
      ·
        refine ⟨117480322027118849031763805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78320214684745899354509203 117480322027118849031763805)
        ·
          refine ⟨44055120760169568386911427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117480322027118849031763805 44055120760169568386911427)
          ·
            refine ⟨66082681140254352580367141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44055120760169568386911427 66082681140254352580367141)
            ·
              refine ⟨12390502713797691108818839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66082681140254352580367141 12390502713797691108818839)
              ·
                refine ⟨18585754070696536663228259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12390502713797691108818839 18585754070696536663228259)
                ·
                  refine ⟨27878631106044804994842389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18585754070696536663228259 27878631106044804994842389)
                  ·
                    refine ⟨1306810833095850234133237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27878631106044804994842389 1306810833095850234133237)
                    ·
                      rfl

theorem cell23_7635015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_7635015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635015 prefixEnd_7635015 := by exact prefixLift 7635015
  have htrace : WordTrace (prefixWord ++ tailWord_7635015) baseStart_7635015 baseEnd_7635015 := by
    simpa [prefixWord, tailWord_7635015, baseEnd_7635015] using wordTrace_append hprefix tailTrace_7635015
  have hstable : (prefixWord ++ tailWord_7635015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635015).length < 2 ^ (prefixWord ++ tailWord_7635015).sum := by decide
  have hdescent : baseEnd_7635015 < baseStart_7635015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635026 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 2, 3, 2]
def baseStart_7635026 : Nat := 118140960795 + 7635026 * 2 ^ 59
def prefixEnd_7635026 : Nat := 4983230072969 + 3 ^ 40 * 7635026 * 2
def baseEnd_7635026 : Nat := 3920438147574750159362161

theorem tailTrace_7635026 : CollatzResearch.WordTrace tailWord_7635026 prefixEnd_7635026 3920438147574750159362161 := by
  unfold tailWord_7635026
  simp only [CollatzResearch.WordTrace]
  refine ⟨69618068909403058868115233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185648183758408156981640621 69618068909403058868115233)
  ·
    refine ⟨52213551682052294151086425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69618068909403058868115233 52213551682052294151086425)
    ·
      refine ⟨39160163761539220613314819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52213551682052294151086425 39160163761539220613314819)
      ·
        refine ⟨58740245642308830919972229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39160163761539220613314819 58740245642308830919972229)
        ·
          refine ⟨11013796057932905797494793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58740245642308830919972229 11013796057932905797494793)
          ·
            refine ⟨8260347043449679348121095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11013796057932905797494793 8260347043449679348121095)
            ·
              refine ⟨12390520565174519022181643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8260347043449679348121095 12390520565174519022181643)
              ·
                refine ⟨18585780847761778533272465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12390520565174519022181643 18585780847761778533272465)
                ·
                  refine ⟨13939335635821333899954349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18585780847761778533272465 13939335635821333899954349)
                  ·
                    refine ⟨5227250863433000212482881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13939335635821333899954349 5227250863433000212482881)
                    ·
                      refine ⟨3920438147574750159362161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5227250863433000212482881 3920438147574750159362161)
                      ·
                        rfl

theorem cell23_7635026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_7635026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635026 prefixEnd_7635026 := by exact prefixLift 7635026
  have htrace : WordTrace (prefixWord ++ tailWord_7635026) baseStart_7635026 baseEnd_7635026 := by
    simpa [prefixWord, tailWord_7635026, baseEnd_7635026] using wordTrace_append hprefix tailTrace_7635026
  have hstable : (prefixWord ++ tailWord_7635026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635026).length < 2 ^ (prefixWord ++ tailWord_7635026).sum := by decide
  have hdescent : baseEnd_7635026 < baseStart_7635026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635056 : List Nat := [2, 1, 1, 1, 5, 2, 2, 4, 1, 2, 2]
def baseStart_7635056 : Nat := 118140960795 + 7635056 * 2 ^ 59
def prefixEnd_7635056 : Nat := 4983230072969 + 3 ^ 40 * 7635056 * 2
def baseEnd_7635056 : Nat := 3920453551994385041987023

theorem tailTrace_7635056 : CollatzResearch.WordTrace tailWord_7635056 prefixEnd_7635056 3920453551994385041987023 := by
  unfold tailWord_7635056
  simp only [CollatzResearch.WordTrace]
  refine ⟨139236684913751775298026511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185648913218335700397368681 139236684913751775298026511)
  ·
    refine ⟨208855027370627662947039767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139236684913751775298026511 208855027370627662947039767)
    ·
      refine ⟨313282541055941494420559651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208855027370627662947039767 313282541055941494420559651)
      ·
        refine ⟨469923811583912241630839477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313282541055941494420559651 469923811583912241630839477)
        ·
          refine ⟨44055357335991772652891201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 469923811583912241630839477 44055357335991772652891201)
          ·
            refine ⟨33041518001993829489668401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44055357335991772652891201 33041518001993829489668401)
            ·
              refine ⟨24781138501495372117251301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33041518001993829489668401 24781138501495372117251301)
              ·
                refine ⟨4646463469030382271984619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24781138501495372117251301 4646463469030382271984619)
                ·
                  refine ⟨6969695203545573407976929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4646463469030382271984619 6969695203545573407976929)
                  ·
                    refine ⟨5227271402659180055982697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6969695203545573407976929 5227271402659180055982697)
                    ·
                      refine ⟨3920453551994385041987023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5227271402659180055982697 3920453551994385041987023)
                      ·
                        rfl

theorem cell23_7635056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 1, 2, 2].length) (baseStart_7635056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635056 prefixEnd_7635056 := by exact prefixLift 7635056
  have htrace : WordTrace (prefixWord ++ tailWord_7635056) baseStart_7635056 baseEnd_7635056 := by
    simpa [prefixWord, tailWord_7635056, baseEnd_7635056] using wordTrace_append hprefix tailTrace_7635056
  have hstable : (prefixWord ++ tailWord_7635056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635056).length < 2 ^ (prefixWord ++ tailWord_7635056).sum := by decide
  have hdescent : baseEnd_7635056 < baseStart_7635056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635145 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 3, 5, 3]
def baseStart_7635145 : Nat := 118140960795 + 7635145 * 2 ^ 59
def prefixEnd_7635145 : Nat := 4983230072969 + 3 ^ 40 * 7635145 * 2
def baseEnd_7635145 : Nat := 3920499251772635193774113

theorem tailTrace_7635145 : CollatzResearch.WordTrace tailWord_7635145 prefixEnd_7635145 3920499251772635193774113 := by
  unfold tailWord_7635145
  simp only [CollatzResearch.WordTrace]
  refine ⟨278476615924181118796042889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185651077282787412530695259 278476615924181118796042889)
  ·
    refine ⟨208857461943135839097032167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278476615924181118796042889 208857461943135839097032167)
    ·
      refine ⟨313286192914703758645548251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208857461943135839097032167 313286192914703758645548251)
      ·
        refine ⟨469929289372055637968322377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313286192914703758645548251 469929289372055637968322377)
        ·
          refine ⟨352446967029041728476241783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469929289372055637968322377 352446967029041728476241783)
          ·
            refine ⟨528670450543562592714362675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352446967029041728476241783 528670450543562592714362675)
            ·
              refine ⟨793005675815343889071544013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528670450543562592714362675 793005675815343889071544013)
              ·
                refine ⟨297377128430753958401829005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 793005675815343889071544013 297377128430753958401829005)
                ·
                  refine ⟨111516423161532734400685877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297377128430753958401829005 111516423161532734400685877)
                  ·
                    refine ⟨10454664671393693850064301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111516423161532734400685877 10454664671393693850064301)
                    ·
                      refine ⟨3920499251772635193774113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10454664671393693850064301 3920499251772635193774113)
                      ·
                        rfl

theorem cell23_7635145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 5, 3].length) (baseStart_7635145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635145 prefixEnd_7635145 := by exact prefixLift 7635145
  have htrace : WordTrace (prefixWord ++ tailWord_7635145) baseStart_7635145 baseEnd_7635145 := by
    simpa [prefixWord, tailWord_7635145, baseEnd_7635145] using wordTrace_append hprefix tailTrace_7635145
  have hstable : (prefixWord ++ tailWord_7635145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635145).length < 2 ^ (prefixWord ++ tailWord_7635145).sum := by decide
  have hdescent : baseEnd_7635145 < baseStart_7635145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635205 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_7635205 : Nat := 118140960795 + 7635205 * 2 ^ 59
def prefixEnd_7635205 : Nat := 4983230072969 + 3 ^ 40 * 7635205 * 2
def baseEnd_7635205 : Nat := 3920530060611904959023837

theorem tailTrace_7635205 : CollatzResearch.WordTrace tailWord_7635205 prefixEnd_7635205 3920530060611904959023837 := by
  unfold tailWord_7635205
  simp only [CollatzResearch.WordTrace]
  refine ⟨278478804303963749043227069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185652536202642499362151379 278478804303963749043227069)
  ·
    refine ⟨104429551613986405891210151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278478804303963749043227069 104429551613986405891210151)
    ·
      refine ⟨156644327420979608836815227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104429551613986405891210151 156644327420979608836815227)
      ·
        refine ⟨234966491131469413255222841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156644327420979608836815227 234966491131469413255222841)
        ·
          refine ⟨176224868348602059941417131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234966491131469413255222841 176224868348602059941417131)
          ·
            refine ⟨264337302522903089912125697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176224868348602059941417131 264337302522903089912125697)
            ·
              refine ⟨198252976892177317434094273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264337302522903089912125697 198252976892177317434094273)
              ·
                refine ⟨148689732669132988075570705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198252976892177317434094273 148689732669132988075570705)
                ·
                  refine ⟨111517299501849741056678029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148689732669132988075570705 111517299501849741056678029)
                  ·
                    refine ⟨41818987313193652896254261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111517299501849741056678029 41818987313193652896254261)
                    ·
                      refine ⟨3920530060611904959023837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41818987313193652896254261 3920530060611904959023837)
                      ·
                        rfl

theorem cell23_7635205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_7635205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635205 prefixEnd_7635205 := by exact prefixLift 7635205
  have htrace : WordTrace (prefixWord ++ tailWord_7635205) baseStart_7635205 baseEnd_7635205 := by
    simpa [prefixWord, tailWord_7635205, baseEnd_7635205] using wordTrace_append hprefix tailTrace_7635205
  have hstable : (prefixWord ++ tailWord_7635205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635205).length < 2 ^ (prefixWord ++ tailWord_7635205).sum := by decide
  have hdescent : baseEnd_7635205 < baseStart_7635205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635212 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 5, 4]
def baseStart_7635212 : Nat := 118140960795 + 7635212 * 2 ^ 59
def prefixEnd_7635212 : Nat := 4983230072969 + 3 ^ 40 * 7635212 * 2
def baseEnd_7635212 : Nat := 1306844551658828810545435

theorem tailTrace_7635212 : CollatzResearch.WordTrace tailWord_7635212 prefixEnd_7635212 1306844551658828810545435 := by
  unfold tailWord_7635212
  simp only [CollatzResearch.WordTrace]
  refine ⟨139239529807469194619365945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185652706409958926159154593 139239529807469194619365945)
  ·
    refine ⟨104429647355601895964524459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139239529807469194619365945 104429647355601895964524459)
    ·
      refine ⟨156644471033402843946786689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104429647355601895964524459 156644471033402843946786689)
      ·
        refine ⟨117483353275052132960090017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156644471033402843946786689 117483353275052132960090017)
        ·
          refine ⟨88112514956289099720067513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117483353275052132960090017 88112514956289099720067513)
          ·
            refine ⟨66084386217216824790050635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88112514956289099720067513 66084386217216824790050635)
            ·
              refine ⟨99126579325825237185075953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66084386217216824790050635 99126579325825237185075953)
              ·
                refine ⟨74344934494368927888806965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99126579325825237185075953 74344934494368927888806965)
                ·
                  refine ⟨6969837608847086989575653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74344934494368927888806965 6969837608847086989575653)
                  ·
                    refine ⟨1306844551658828810545435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6969837608847086989575653 1306844551658828810545435)
                    ·
                      rfl

theorem cell23_7635212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_7635212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635212 prefixEnd_7635212 := by exact prefixLift 7635212
  have htrace : WordTrace (prefixWord ++ tailWord_7635212) baseStart_7635212 baseEnd_7635212 := by
    simpa [prefixWord, tailWord_7635212, baseEnd_7635212] using wordTrace_append hprefix tailTrace_7635212
  have hstable : (prefixWord ++ tailWord_7635212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635212).length < 2 ^ (prefixWord ++ tailWord_7635212).sum := by decide
  have hdescent : baseEnd_7635212 < baseStart_7635212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635215 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 4]
def baseStart_7635215 : Nat := 118140960795 + 7635215 * 2 ^ 59
def prefixEnd_7635215 : Nat := 4983230072969 + 3 ^ 40 * 7635215 * 2
def baseEnd_7635215 : Nat := 3920535195418449919898791

theorem tailTrace_7635215 : CollatzResearch.WordTrace tailWord_7635215 prefixEnd_7635215 3920535195418449919898791 := by
  unfold tailWord_7635215
  simp only [CollatzResearch.WordTrace]
  refine ⟨278479169033927520751091099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185652779355951680500727399 278479169033927520751091099)
  ·
    refine ⟨417718753550891281126636649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278479169033927520751091099 417718753550891281126636649)
    ·
      refine ⟨313289065163168460844977487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417718753550891281126636649 313289065163168460844977487)
      ·
        refine ⟨469933597744752691267466231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313289065163168460844977487 469933597744752691267466231)
        ·
          refine ⟨704900396617129036901199347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469933597744752691267466231 704900396617129036901199347)
          ·
            refine ⟨1057350594925693555351799021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704900396617129036901199347 1057350594925693555351799021)
            ·
              refine ⟨396506473097135083256924633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1057350594925693555351799021 396506473097135083256924633)
              ·
                refine ⟨297379854822851312442693475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396506473097135083256924633 297379854822851312442693475)
                ·
                  refine ⟨446069782234276968664040213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297379854822851312442693475 446069782234276968664040213)
                  ·
                    refine ⟨20909521042231732906126885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 446069782234276968664040213 20909521042231732906126885)
                    ·
                      refine ⟨3920535195418449919898791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20909521042231732906126885 3920535195418449919898791)
                      ·
                        rfl

theorem cell23_7635215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_7635215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635215 prefixEnd_7635215 := by exact prefixLift 7635215
  have htrace : WordTrace (prefixWord ++ tailWord_7635215) baseStart_7635215 baseEnd_7635215 := by
    simpa [prefixWord, tailWord_7635215, baseEnd_7635215] using wordTrace_append hprefix tailTrace_7635215
  have hstable : (prefixWord ++ tailWord_7635215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635215).length < 2 ^ (prefixWord ++ tailWord_7635215).sum := by decide
  have hdescent : baseEnd_7635215 < baseStart_7635215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635255 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 2, 9]
def baseStart_7635255 : Nat := 118140960795 + 7635255 * 2 ^ 59
def prefixEnd_7635255 : Nat := 4983230072969 + 3 ^ 40 * 7635255 * 2
def baseEnd_7635255 : Nat := 1306851911548209921132869

theorem tailTrace_7635255 : CollatzResearch.WordTrace tailWord_7635255 prefixEnd_7635255 1306851911548209921132869 := by
  unfold tailWord_7635255
  simp only [CollatzResearch.WordTrace]
  refine ⟨278480627953782607582547219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185653751969188405055031479 278480627953782607582547219)
  ·
    refine ⟨417720941930673911373820829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278480627953782607582547219 417720941930673911373820829)
    ·
      refine ⟨156645353224002716765182811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417720941930673911373820829 156645353224002716765182811)
      ·
        refine ⟨234968029836004075147774217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156645353224002716765182811 234968029836004075147774217)
        ·
          refine ⟨176226022377003056360830663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234968029836004075147774217 176226022377003056360830663)
          ·
            refine ⟨264339033565504584541245995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176226022377003056360830663 264339033565504584541245995)
            ·
              refine ⟨396508550348256876811868993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264339033565504584541245995 396508550348256876811868993)
              ·
                refine ⟨297381412761192657608901745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396508550348256876811868993 297381412761192657608901745)
                ·
                  refine ⟨223036059570894493206676309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297381412761192657608901745 223036059570894493206676309)
                  ·
                    refine ⟨1306851911548209921132869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 223036059570894493206676309 1306851911548209921132869)
                    ·
                      rfl

theorem cell23_7635255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_7635255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635255 prefixEnd_7635255 := by exact prefixLift 7635255
  have htrace : WordTrace (prefixWord ++ tailWord_7635255) baseStart_7635255 baseEnd_7635255 := by
    simpa [prefixWord, tailWord_7635255, baseEnd_7635255] using wordTrace_append hprefix tailTrace_7635255
  have hstable : (prefixWord ++ tailWord_7635255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635255).length < 2 ^ (prefixWord ++ tailWord_7635255).sum := by decide
  have hdescent : baseEnd_7635255 < baseStart_7635255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635306 : List Nat := [3, 1, 3, 3, 1, 1, 3, 2, 1, 5]
def baseStart_7635306 : Nat := 118140960795 + 7635306 * 2 ^ 59
def prefixEnd_7635306 : Nat := 4983230072969 + 3 ^ 40 * 7635306 * 2
def baseEnd_7635306 : Nat := 1306860640719336354620291

theorem tailTrace_7635306 : CollatzResearch.WordTrace tailWord_7635306 prefixEnd_7635306 1306860640719336354620291 := by
  unfold tailWord_7635306
  simp only [CollatzResearch.WordTrace]
  refine ⟨69620622019149460823163443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185654992051065228861769181 69620622019149460823163443)
  ·
    refine ⟨104430933028724191234745165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69620622019149460823163443 104430933028724191234745165)
    ·
      refine ⟨39161599885771571713029437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104430933028724191234745165 39161599885771571713029437)
      ·
        refine ⟨14685599957164339392386039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39161599885771571713029437 14685599957164339392386039)
        ·
          refine ⟨22028399935746509088579059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14685599957164339392386039 22028399935746509088579059)
          ·
            refine ⟨33042599903619763632868589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22028399935746509088579059 33042599903619763632868589)
            ·
              refine ⟨12390974963857411362325721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33042599903619763632868589 12390974963857411362325721)
              ·
                refine ⟨9293231222893058521744291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12390974963857411362325721 9293231222893058521744291)
                ·
                  refine ⟨13939846834339587782616437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9293231222893058521744291 13939846834339587782616437)
                  ·
                    refine ⟨1306860640719336354620291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13939846834339587782616437 1306860640719336354620291)
                    ·
                      rfl

theorem cell23_7635306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_7635306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635306 prefixEnd_7635306 := by exact prefixLift 7635306
  have htrace : WordTrace (prefixWord ++ tailWord_7635306) baseStart_7635306 baseEnd_7635306 := by
    simpa [prefixWord, tailWord_7635306, baseEnd_7635306] using wordTrace_append hprefix tailTrace_7635306
  have hstable : (prefixWord ++ tailWord_7635306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635306).length < 2 ^ (prefixWord ++ tailWord_7635306).sum := by decide
  have hdescent : baseEnd_7635306 < baseStart_7635306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635309 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_7635309 : Nat := 118140960795 + 7635309 * 2 ^ 59
def prefixEnd_7635309 : Nat := 4983230072969 + 3 ^ 40 * 7635309 * 2
def baseEnd_7635309 : Nat := 3920583462599972552123359

theorem tailTrace_7635309 : CollatzResearch.WordTrace tailWord_7635309 prefixEnd_7635309 3920583462599972552123359 := by
  unfold tailWord_7635309
  simp only [CollatzResearch.WordTrace]
  refine ⟨278482597495586974805012981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185655064997057983203341987 278482597495586974805012981)
  ·
    refine ⟨26107743515211278887969967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278482597495586974805012981 26107743515211278887969967)
    ·
      refine ⟨39161615272816918331954951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26107743515211278887969967 39161615272816918331954951)
      ·
        refine ⟨58742422909225377497932427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39161615272816918331954951 58742422909225377497932427)
        ·
          refine ⟨88113634363838066246898641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58742422909225377497932427 88113634363838066246898641)
          ·
            refine ⟨66085225772878549685173981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88113634363838066246898641 66085225772878549685173981)
            ·
              refine ⟨24781959664829456131940243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66085225772878549685173981 24781959664829456131940243)
              ·
                refine ⟨37172939497244184197910365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24781959664829456131940243 37172939497244184197910365)
                ·
                  refine ⟨13939852311466569074216387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37172939497244184197910365 13939852311466569074216387)
                  ·
                    refine ⟨20909778467199853611324581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13939852311466569074216387 20909778467199853611324581)
                    ·
                      refine ⟨3920583462599972552123359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20909778467199853611324581 3920583462599972552123359)
                      ·
                        rfl

theorem cell23_7635309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_7635309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635309 prefixEnd_7635309 := by exact prefixLift 7635309
  have htrace : WordTrace (prefixWord ++ tailWord_7635309) baseStart_7635309 baseEnd_7635309 := by
    simpa [prefixWord, tailWord_7635309, baseEnd_7635309] using wordTrace_append hprefix tailTrace_7635309
  have hstable : (prefixWord ++ tailWord_7635309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635309).length < 2 ^ (prefixWord ++ tailWord_7635309).sum := by decide
  have hdescent : baseEnd_7635309 < baseStart_7635309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635336 : List Nat := [2, 1, 3, 3, 1, 1, 4, 2, 2, 4]
def baseStart_7635336 : Nat := 118140960795 + 7635336 * 2 ^ 59
def prefixEnd_7635336 : Nat := 4983230072969 + 3 ^ 40 * 7635336 * 2
def baseEnd_7635336 : Nat := 1306865775525881315495245

theorem tailTrace_7635336 : CollatzResearch.WordTrace tailWord_7635336 prefixEnd_7635336 1306865775525881315495245 := by
  unfold tailWord_7635336
  simp only [CollatzResearch.WordTrace]
  refine ⟨139241791133244579208122931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185655721510992772277497241 139241791133244579208122931)
  ·
    refine ⟨208862686699866868812184397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139241791133244579208122931 208862686699866868812184397)
    ·
      refine ⟨78323507512450075804569149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208862686699866868812184397 78323507512450075804569149)
      ·
        refine ⟨29371315317168778426713431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78323507512450075804569149 29371315317168778426713431)
        ·
          refine ⟨44056972975753167640070147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29371315317168778426713431 44056972975753167640070147)
          ·
            refine ⟨66085459463629751460105221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44056972975753167640070147 66085459463629751460105221)
            ·
              refine ⟨12391023649430578398769729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66085459463629751460105221 12391023649430578398769729)
              ·
                refine ⟨9293267737072933799077297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12391023649430578398769729 9293267737072933799077297)
                ·
                  refine ⟨6969950802804700349307973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9293267737072933799077297 6969950802804700349307973)
                  ·
                    refine ⟨1306865775525881315495245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6969950802804700349307973 1306865775525881315495245)
                    ·
                      rfl

theorem cell23_7635336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_7635336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635336 prefixEnd_7635336 := by exact prefixLift 7635336
  have htrace : WordTrace (prefixWord ++ tailWord_7635336) baseStart_7635336 baseEnd_7635336 := by
    simpa [prefixWord, tailWord_7635336, baseEnd_7635336] using wordTrace_append hprefix tailTrace_7635336
  have hstable : (prefixWord ++ tailWord_7635336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635336).length < 2 ^ (prefixWord ++ tailWord_7635336).sum := by decide
  have hdescent : baseEnd_7635336 < baseStart_7635336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635372 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_7635372 : Nat := 118140960795 + 7635372 * 2 ^ 59
def prefixEnd_7635372 : Nat := 4983230072969 + 3 ^ 40 * 7635372 * 2
def baseEnd_7635372 : Nat := 3920615811881205805635569

theorem tailTrace_7635372 : CollatzResearch.WordTrace tailWord_7635372 prefixEnd_7635372 3920615811881205805635569 := by
  unfold tailWord_7635372
  simp only [CollatzResearch.WordTrace]
  refine ⟨139242447647179368282278185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185656596862905824376370913 139242447647179368282278185)
  ·
    refine ⟨104431835735384526211708639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139242447647179368282278185 104431835735384526211708639)
    ·
      refine ⟨156647753603076789317562959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104431835735384526211708639 156647753603076789317562959)
      ·
        refine ⟨234971630404615183976344439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156647753603076789317562959 234971630404615183976344439)
        ·
          refine ⟨352457445606922775964516659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234971630404615183976344439 352457445606922775964516659)
          ·
            refine ⟨528686168410384163946774989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352457445606922775964516659 528686168410384163946774989)
            ·
              refine ⟨198257313153894061480040621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 528686168410384163946774989 198257313153894061480040621)
              ·
                refine ⟨74346492432710273055015233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198257313153894061480040621 74346492432710273055015233)
                ·
                  refine ⟨55759869324532704791261425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74346492432710273055015233 55759869324532704791261425)
                  ·
                    refine ⟨41819901993399528593446069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55759869324532704791261425 41819901993399528593446069)
                    ·
                      refine ⟨3920615811881205805635569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41819901993399528593446069 3920615811881205805635569)
                      ·
                        rfl

theorem cell23_7635372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_7635372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635372 prefixEnd_7635372 := by exact prefixLift 7635372
  have htrace : WordTrace (prefixWord ++ tailWord_7635372) baseStart_7635372 baseEnd_7635372 := by
    simpa [prefixWord, tailWord_7635372, baseEnd_7635372] using wordTrace_append hprefix tailTrace_7635372
  have hstable : (prefixWord ++ tailWord_7635372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635372).length < 2 ^ (prefixWord ++ tailWord_7635372).sum := by decide
  have hdescent : baseEnd_7635372 < baseStart_7635372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635410 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_7635410 : Nat := 118140960795 + 7635410 * 2 ^ 59
def prefixEnd_7635410 : Nat := 4983230072969 + 3 ^ 40 * 7635410 * 2
def baseEnd_7635410 : Nat := 3920635324146076656960395

theorem tailTrace_7635410 : CollatzResearch.WordTrace tailWord_7635410 prefixEnd_7635410 3920635324146076656960395 := by
  unfold tailWord_7635410
  simp only [CollatzResearch.WordTrace]
  refine ⟨69621570317055267263609921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185657520845480712702959789 69621570317055267263609921)
  ·
    refine ⟨52216177737791450447707441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69621570317055267263609921 52216177737791450447707441)
    ·
      refine ⟨39162133303343587835780581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52216177737791450447707441 39162133303343587835780581)
      ·
        refine ⟨7342899994376922719208859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39162133303343587835780581 7342899994376922719208859)
        ·
          refine ⟨11014349991565384078813289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7342899994376922719208859 11014349991565384078813289)
          ·
            refine ⟨8260762493674038059109967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11014349991565384078813289 8260762493674038059109967)
            ·
              refine ⟨12391143740511057088664951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8260762493674038059109967 12391143740511057088664951)
              ·
                refine ⟨18586715610766585632997427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12391143740511057088664951 18586715610766585632997427)
                ·
                  refine ⟨27880073416149878449496141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18586715610766585632997427 27880073416149878449496141)
                  ·
                    refine ⟨10455027531056204418561053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27880073416149878449496141 10455027531056204418561053)
                    ·
                      refine ⟨3920635324146076656960395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10455027531056204418561053 3920635324146076656960395)
                      ·
                        rfl

theorem cell23_7635410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_7635410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635410 prefixEnd_7635410 := by exact prefixLift 7635410
  have htrace : WordTrace (prefixWord ++ tailWord_7635410) baseStart_7635410 baseEnd_7635410 := by
    simpa [prefixWord, tailWord_7635410, baseEnd_7635410] using wordTrace_append hprefix tailTrace_7635410
  have hstable : (prefixWord ++ tailWord_7635410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635410).length < 2 ^ (prefixWord ++ tailWord_7635410).sum := by decide
  have hdescent : baseEnd_7635410 < baseStart_7635410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635449 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 4, 3, 3]
def baseStart_7635449 : Nat := 118140960795 + 7635449 * 2 ^ 59
def prefixEnd_7635449 : Nat := 4983230072969 + 3 ^ 40 * 7635449 * 2
def baseEnd_7635449 : Nat := 3920655349891602004372715

theorem tailTrace_7635449 : CollatzResearch.WordTrace tailWord_7635449 prefixEnd_7635449 3920655349891602004372715 := by
  unfold tailWord_7635449
  simp only [CollatzResearch.WordTrace]
  refine ⟨278487703715079778715109401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185658469143386519143406267 278487703715079778715109401)
  ·
    refine ⟨208865777786309834036332051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278487703715079778715109401 208865777786309834036332051)
    ·
      refine ⟨313298666679464751054498077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208865777786309834036332051 313298666679464751054498077)
      ·
        refine ⟨117487000004799281645436779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313298666679464751054498077 117487000004799281645436779)
        ·
          refine ⟨176230500007198922468155169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117487000004799281645436779 176230500007198922468155169)
          ·
            refine ⟨132172875005399191851116377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176230500007198922468155169 132172875005399191851116377)
            ·
              refine ⟨99129656254049393888337283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132172875005399191851116377 99129656254049393888337283)
              ·
                refine ⟨148694484381074090832505925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99129656254049393888337283 148694484381074090832505925)
                ·
                  refine ⟨27880215821451392031094861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148694484381074090832505925 27880215821451392031094861)
                  ·
                    refine ⟨10455080933044272011660573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27880215821451392031094861 10455080933044272011660573)
                    ·
                      refine ⟨3920655349891602004372715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10455080933044272011660573 3920655349891602004372715)
                      ·
                        rfl

theorem cell23_7635449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_7635449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635449 prefixEnd_7635449 := by exact prefixLift 7635449
  have htrace : WordTrace (prefixWord ++ tailWord_7635449) baseStart_7635449 baseEnd_7635449 := by
    simpa [prefixWord, tailWord_7635449, baseEnd_7635449] using wordTrace_append hprefix tailTrace_7635449
  have hstable : (prefixWord ++ tailWord_7635449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635449).length < 2 ^ (prefixWord ++ tailWord_7635449).sum := by decide
  have hdescent : baseEnd_7635449 < baseStart_7635449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635467 : List Nat := [1, 1, 1, 1, 7, 3, 2, 1, 2, 2, 2]
def baseStart_7635467 : Nat := 118140960795 + 7635467 * 2 ^ 59
def prefixEnd_7635467 : Nat := 4983230072969 + 3 ^ 40 * 7635467 * 2
def baseEnd_7635467 : Nat := 3920664592543382933947633

theorem tailTrace_7635467 : CollatzResearch.WordTrace tailWord_7635467 prefixEnd_7635467 3920664592543382933947633 := by
  unfold tailWord_7635467
  simp only [CollatzResearch.WordTrace]
  refine ⟨278488360229014567789264655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185658906819343045192843103 278488360229014567789264655)
  ·
    refine ⟨417732540343521851683896983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278488360229014567789264655 417732540343521851683896983)
    ·
      refine ⟨626598810515282777525845475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417732540343521851683896983 626598810515282777525845475)
      ·
        refine ⟨939898215772924166288768213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626598810515282777525845475 939898215772924166288768213)
        ·
          refine ⟨22028864432177910147393005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 939898215772924166288768213 22028864432177910147393005)
          ·
            refine ⟨8260824162066716305272377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22028864432177910147393005 8260824162066716305272377)
            ·
              refine ⟨6195618121550037228954283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8260824162066716305272377 6195618121550037228954283)
              ·
                refine ⟨9293427182325055843431425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6195618121550037228954283 9293427182325055843431425)
                ·
                  refine ⟨6970070386743791882573569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9293427182325055843431425 6970070386743791882573569)
                  ·
                    refine ⟨5227552790057843911930177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6970070386743791882573569 5227552790057843911930177)
                    ·
                      refine ⟨3920664592543382933947633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5227552790057843911930177 3920664592543382933947633)
                      ·
                        rfl

theorem cell23_7635467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 2, 2, 2].length) (baseStart_7635467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635467 prefixEnd_7635467 := by exact prefixLift 7635467
  have htrace : WordTrace (prefixWord ++ tailWord_7635467) baseStart_7635467 baseEnd_7635467 := by
    simpa [prefixWord, tailWord_7635467, baseEnd_7635467] using wordTrace_append hprefix tailTrace_7635467
  have hstable : (prefixWord ++ tailWord_7635467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635467).length < 2 ^ (prefixWord ++ tailWord_7635467).sum := by decide
  have hdescent : baseEnd_7635467 < baseStart_7635467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635496 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_7635496 : Nat := 118140960795 + 7635496 * 2 ^ 59
def prefixEnd_7635496 : Nat := 4983230072969 + 3 ^ 40 * 7635496 * 2
def baseEnd_7635496 : Nat := 3920679483482363320484999

theorem tailTrace_7635496 : CollatzResearch.WordTrace tailWord_7635496 prefixEnd_7635496 3920679483482363320484999 := by
  unfold tailWord_7635496
  simp only [CollatzResearch.WordTrace]
  refine ⟨139244708972954752871035171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185659611963939670494713561 139244708972954752871035171)
  ·
    refine ⟨208867063459432129306552757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139244708972954752871035171 208867063459432129306552757)
    ·
      refine ⟨19581287199321762122489321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208867063459432129306552757 19581287199321762122489321)
      ·
        refine ⟨14685965399491321591866991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19581287199321762122489321 14685965399491321591866991)
        ·
          refine ⟨22028948099236982387800487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14685965399491321591866991 22028948099236982387800487)
          ·
            refine ⟨33043422148855473581700731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22028948099236982387800487 33043422148855473581700731)
            ·
              refine ⟨49565133223283210372551097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33043422148855473581700731 49565133223283210372551097)
              ·
                refine ⟨37173849917462407779413323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49565133223283210372551097 37173849917462407779413323)
                ·
                  refine ⟨55760774876193611669119985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37173849917462407779413323 55760774876193611669119985)
                  ·
                    refine ⟨41820581157145208751839989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55760774876193611669119985 41820581157145208751839989)
                    ·
                      refine ⟨3920679483482363320484999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41820581157145208751839989 3920679483482363320484999)
                      ·
                        rfl

theorem cell23_7635496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_7635496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635496 prefixEnd_7635496 := by exact prefixLift 7635496
  have htrace : WordTrace (prefixWord ++ tailWord_7635496) baseStart_7635496 baseEnd_7635496 := by
    simpa [prefixWord, tailWord_7635496, baseEnd_7635496] using wordTrace_append hprefix tailTrace_7635496
  have hstable : (prefixWord ++ tailWord_7635496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635496).length < 2 ^ (prefixWord ++ tailWord_7635496).sum := by decide
  have hdescent : baseEnd_7635496 < baseStart_7635496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635501 : List Nat := [1, 5, 4, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_7635501 : Nat := 118140960795 + 7635501 * 2 ^ 59
def prefixEnd_7635501 : Nat := 4983230072969 + 3 ^ 40 * 7635501 * 2
def baseEnd_7635501 : Nat := 3920682050885635800922477

theorem tailTrace_7635501 : CollatzResearch.WordTrace tailWord_7635501 prefixEnd_7635501 3920682050885635800922477 := by
  unfold tailWord_7635501
  simp only [CollatzResearch.WordTrace]
  refine ⟨278489600310891391596002357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185659733540594261064001571 278489600310891391596002357)
  ·
    refine ⟨26108400029146067962125221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278489600310891391596002357 26108400029146067962125221)
    ·
      refine ⟨4895325005464887742898479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26108400029146067962125221 4895325005464887742898479)
      ·
        refine ⟨7342987508197331614347719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4895325005464887742898479 7342987508197331614347719)
        ·
          refine ⟨11014481262295997421521579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7342987508197331614347719 11014481262295997421521579)
          ·
            refine ⟨16521721893443996132282369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11014481262295997421521579 16521721893443996132282369)
            ·
              refine ⟨12391291420082997099211777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16521721893443996132282369 12391291420082997099211777)
              ·
                refine ⟨9293468565062247824408833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12391291420082997099211777 9293468565062247824408833)
                ·
                  refine ⟨6970101423796685868306625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9293468565062247824408833 6970101423796685868306625)
                  ·
                    refine ⟨5227576067847514401229969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6970101423796685868306625 5227576067847514401229969)
                    ·
                      refine ⟨3920682050885635800922477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5227576067847514401229969 3920682050885635800922477)
                      ·
                        rfl

theorem cell23_7635501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_7635501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635501 prefixEnd_7635501 := by exact prefixLift 7635501
  have htrace : WordTrace (prefixWord ++ tailWord_7635501) baseStart_7635501 baseEnd_7635501 := by
    simpa [prefixWord, tailWord_7635501, baseEnd_7635501] using wordTrace_append hprefix tailTrace_7635501
  have hstable : (prefixWord ++ tailWord_7635501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635501).length < 2 ^ (prefixWord ++ tailWord_7635501).sum := by decide
  have hdescent : baseEnd_7635501 < baseStart_7635501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635506 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_7635506 : Nat := 118140960795 + 7635506 * 2 ^ 59
def prefixEnd_7635506 : Nat := 4983230072969 + 3 ^ 40 * 7635506 * 2
def baseEnd_7635506 : Nat := 3920684618288908281359953

theorem tailTrace_7635506 : CollatzResearch.WordTrace tailWord_7635506 prefixEnd_7635506 3920684618288908281359953 := by
  unfold tailWord_7635506
  simp only [CollatzResearch.WordTrace]
  refine ⟨69622445668968319362483593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185659855117248851633289581 69622445668968319362483593)
  ·
    refine ⟨52216834251726239521862695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69622445668968319362483593 52216834251726239521862695)
    ·
      refine ⟨78325251377589359282794043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52216834251726239521862695 78325251377589359282794043)
      ·
        refine ⟨117487877066384038924191065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78325251377589359282794043 117487877066384038924191065)
        ·
          refine ⟨88115907799788029193143299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117487877066384038924191065 88115907799788029193143299)
          ·
            refine ⟨132173861699682043789714949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88115907799788029193143299 132173861699682043789714949)
            ·
              refine ⟨24782599068690383210571553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132173861699682043789714949 24782599068690383210571553)
              ·
                refine ⟨18586949301517787407928665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24782599068690383210571553 18586949301517787407928665)
                ·
                  refine ⟨13940211976138340555946499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18586949301517787407928665 13940211976138340555946499)
                  ·
                    refine ⟨20910317964207510833919749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13940211976138340555946499 20910317964207510833919749)
                    ·
                      refine ⟨3920684618288908281359953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20910317964207510833919749 3920684618288908281359953)
                      ·
                        rfl

theorem cell23_7635506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_7635506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635506 prefixEnd_7635506 := by exact prefixLift 7635506
  have htrace : WordTrace (prefixWord ++ tailWord_7635506) baseStart_7635506 baseEnd_7635506 := by
    simpa [prefixWord, tailWord_7635506, baseEnd_7635506] using wordTrace_append hprefix tailTrace_7635506
  have hstable : (prefixWord ++ tailWord_7635506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635506).length < 2 ^ (prefixWord ++ tailWord_7635506).sum := by decide
  have hdescent : baseEnd_7635506 < baseStart_7635506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635509 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_7635509 : Nat := 118140960795 + 7635509 * 2 ^ 59
def prefixEnd_7635509 : Nat := 4983230072969 + 3 ^ 40 * 7635509 * 2
def baseEnd_7635509 : Nat := 3920686158730871769622439

theorem tailTrace_7635509 : CollatzResearch.WordTrace tailWord_7635509 prefixEnd_7635509 3920686158730871769622439 := by
  unfold tailWord_7635509
  simp only [CollatzResearch.WordTrace]
  refine ⟨278489892094862408962293581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185659928063241605974862387 278489892094862408962293581)
  ·
    refine ⟨104433709535573403360860093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278489892094862408962293581 104433709535573403360860093)
    ·
      refine ⟨39162641075840026260322535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104433709535573403360860093 39162641075840026260322535)
      ·
        refine ⟨58743961613760039390483803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39162641075840026260322535 58743961613760039390483803)
        ·
          refine ⟨88115942420640059085725705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58743961613760039390483803 88115942420640059085725705)
          ·
            refine ⟨66086956815480044314294279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88115942420640059085725705 66086956815480044314294279)
            ·
              refine ⟨99130435223220066471441419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66086956815480044314294279 99130435223220066471441419)
              ·
                refine ⟨148695652834830099707162129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99130435223220066471441419 148695652834830099707162129)
                ·
                  refine ⟨111521739626122574780371597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148695652834830099707162129 111521739626122574780371597)
                  ·
                    refine ⟨41820652359795965542639349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111521739626122574780371597 41820652359795965542639349)
                    ·
                      refine ⟨3920686158730871769622439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41820652359795965542639349 3920686158730871769622439)
                      ·
                        rfl

theorem cell23_7635509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_7635509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635509 prefixEnd_7635509 := by exact prefixLift 7635509
  have htrace : WordTrace (prefixWord ++ tailWord_7635509) baseStart_7635509 baseEnd_7635509 := by
    simpa [prefixWord, tailWord_7635509, baseEnd_7635509] using wordTrace_append hprefix tailTrace_7635509
  have hstable : (prefixWord ++ tailWord_7635509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635509).length < 2 ^ (prefixWord ++ tailWord_7635509).sum := by decide
  have hdescent : baseEnd_7635509 < baseStart_7635509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635533 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_7635533 : Nat := 118140960795 + 7635533 * 2 ^ 59
def prefixEnd_7635533 : Nat := 4983230072969 + 3 ^ 40 * 7635533 * 2
def baseEnd_7635533 : Nat := 1306899494088859891907443

theorem tailTrace_7635533 : CollatzResearch.WordTrace tailWord_7635533 prefixEnd_7635533 1306899494088859891907443 := by
  unfold tailWord_7635533
  simp only [CollatzResearch.WordTrace]
  refine ⟨278490767446775461061167253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185660511631183640707444835 278490767446775461061167253)
  ·
    refine ⟨13054254724067599737242215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 278490767446775461061167253 13054254724067599737242215)
    ·
      refine ⟨19581382086101399605863323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13054254724067599737242215 19581382086101399605863323)
      ·
        refine ⟨29372073129152099408794985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19581382086101399605863323 29372073129152099408794985)
        ·
          refine ⟨22029054846864074556596239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29372073129152099408794985 22029054846864074556596239)
          ·
            refine ⟨33043582270296111834894359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22029054846864074556596239 33043582270296111834894359)
            ·
              refine ⟨49565373405444167752341539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33043582270296111834894359 49565373405444167752341539)
              ·
                refine ⟨74348060108166251628512309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49565373405444167752341539 74348060108166251628512309)
                ·
                  refine ⟨6970130635140586090173029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74348060108166251628512309 6970130635140586090173029)
                  ·
                    refine ⟨1306899494088859891907443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6970130635140586090173029 1306899494088859891907443)
                    ·
                      rfl

theorem cell23_7635533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_7635533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635533 prefixEnd_7635533 := by exact prefixLift 7635533
  have htrace : WordTrace (prefixWord ++ tailWord_7635533) baseStart_7635533 baseEnd_7635533 := by
    simpa [prefixWord, tailWord_7635533, baseEnd_7635533] using wordTrace_append hprefix tailTrace_7635533
  have hstable : (prefixWord ++ tailWord_7635533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635533).length < 2 ^ (prefixWord ++ tailWord_7635533).sum := by decide
  have hdescent : baseEnd_7635533 < baseStart_7635533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635566 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_7635566 : Nat := 118140960795 + 7635566 * 2 ^ 59
def prefixEnd_7635566 : Nat := 4983230072969 + 3 ^ 40 * 7635566 * 2
def baseEnd_7635566 : Nat := 3920715427128178046609677

theorem tailTrace_7635566 : CollatzResearch.WordTrace tailWord_7635566 prefixEnd_7635566 3920715427128178046609677 := by
  unfold tailWord_7635566
  simp only [CollatzResearch.WordTrace]
  refine ⟨34811496381956988462139819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185661314037103938464745701 34811496381956988462139819)
  ·
    refine ⟨52217244572935482693209729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34811496381956988462139819 52217244572935482693209729)
    ·
      refine ⟨39162933429701612019907297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52217244572935482693209729 39162933429701612019907297)
      ·
        refine ⟨29372200072276209014930473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39162933429701612019907297 29372200072276209014930473)
        ·
          refine ⟨22029150054207156761197855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29372200072276209014930473 22029150054207156761197855)
          ·
            refine ⟨33043725081310735141796783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22029150054207156761197855 33043725081310735141796783)
            ·
              refine ⟨49565587621966102712695175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33043725081310735141796783 49565587621966102712695175)
              ·
                refine ⟨74348381432949154069042763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49565587621966102712695175 74348381432949154069042763)
                ·
                  refine ⟨111522572149423731103564145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74348381432949154069042763 111522572149423731103564145)
                  ·
                    refine ⟨83641929112067798327673109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111522572149423731103564145 83641929112067798327673109)
                    ·
                      refine ⟨3920715427128178046609677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83641929112067798327673109 3920715427128178046609677)
                      ·
                        rfl

theorem cell23_7635566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_7635566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635566 prefixEnd_7635566 := by exact prefixLift 7635566
  have htrace : WordTrace (prefixWord ++ tailWord_7635566) baseStart_7635566 baseEnd_7635566 := by
    simpa [prefixWord, tailWord_7635566, baseEnd_7635566] using wordTrace_append hprefix tailTrace_7635566
  have hstable : (prefixWord ++ tailWord_7635566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635566).length < 2 ^ (prefixWord ++ tailWord_7635566).sum := by decide
  have hdescent : baseEnd_7635566 < baseStart_7635566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635579 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 4]
def baseStart_7635579 : Nat := 118140960795 + 7635579 * 2 ^ 59
def prefixEnd_7635579 : Nat := 4983230072969 + 3 ^ 40 * 7635579 * 2
def baseEnd_7635579 : Nat := 3920722102376686495747117

theorem tailTrace_7635579 : CollatzResearch.WordTrace tailWord_7635579 prefixEnd_7635579 3920722102376686495747117 := by
  unfold tailWord_7635579
  simp only [CollatzResearch.WordTrace]
  refine ⟨278492445204608810917341791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185661630136405873944894527 278492445204608810917341791)
  ·
    refine ⟨417738667806913216376012687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278492445204608810917341791 417738667806913216376012687)
    ·
      refine ⟨626608001710369824564019031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417738667806913216376012687 626608001710369824564019031)
      ·
        refine ⟨939912002565554736846028547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626608001710369824564019031 939912002565554736846028547)
        ·
          refine ⟨1409868003848332105269042821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939912002565554736846028547 1409868003848332105269042821)
          ·
            refine ⟨264350250721562269737945529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1409868003848332105269042821 264350250721562269737945529)
            ·
              refine ⟨198262688041171702303459147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264350250721562269737945529 198262688041171702303459147)
              ·
                refine ⟨297394032061757553455188721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198262688041171702303459147 297394032061757553455188721)
                ·
                  refine ⟨223045524046318165091391541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297394032061757553455188721 223045524046318165091391541)
                  ·
                    refine ⟨20910517879342327977317957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 223045524046318165091391541 20910517879342327977317957)
                    ·
                      refine ⟨3920722102376686495747117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20910517879342327977317957 3920722102376686495747117)
                      ·
                        rfl

theorem cell23_7635579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 4].length) (baseStart_7635579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635579 prefixEnd_7635579 := by exact prefixLift 7635579
  have htrace : WordTrace (prefixWord ++ tailWord_7635579) baseStart_7635579 baseEnd_7635579 := by
    simpa [prefixWord, tailWord_7635579, baseEnd_7635579] using wordTrace_append hprefix tailTrace_7635579
  have hstable : (prefixWord ++ tailWord_7635579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635579).length < 2 ^ (prefixWord ++ tailWord_7635579).sum := by decide
  have hdescent : baseEnd_7635579 < baseStart_7635579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635613 : List Nat := [1, 4, 2, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_7635613 : Nat := 118140960795 + 7635613 * 2 ^ 59
def prefixEnd_7635613 : Nat := 4983230072969 + 3 ^ 40 * 7635613 * 2
def baseEnd_7635613 : Nat := 3920739560718939362721961

theorem tailTrace_7635613 : CollatzResearch.WordTrace tailWord_7635613 prefixEnd_7635613 3920739560718939362721961 := by
  unfold tailWord_7635613
  simp only [CollatzResearch.WordTrace]
  refine ⟨278493685286485634724079493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185662456857657089816052995 278493685286485634724079493)
  ·
    refine ⟨52217565991216056510764905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278493685286485634724079493 52217565991216056510764905)
    ·
      refine ⟨39163174493412042383073679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52217565991216056510764905 39163174493412042383073679)
      ·
        refine ⟨58744761740118063574610519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39163174493412042383073679 58744761740118063574610519)
        ·
          refine ⟨88117142610177095361915779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58744761740118063574610519 88117142610177095361915779)
          ·
            refine ⟨132175713915265643042873669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88117142610177095361915779 132175713915265643042873669)
            ·
              refine ⟨24782946359112308070538813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132175713915265643042873669 24782946359112308070538813)
              ·
                refine ⟨9293604884667115526452055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24782946359112308070538813 9293604884667115526452055)
                ·
                  refine ⟨13940407327000673289678083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9293604884667115526452055 13940407327000673289678083)
                  ·
                    refine ⟨20910610990501009934517125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13940407327000673289678083 20910610990501009934517125)
                    ·
                      refine ⟨3920739560718939362721961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20910610990501009934517125 3920739560718939362721961)
                      ·
                        rfl

theorem cell23_7635613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_7635613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635613 prefixEnd_7635613 := by exact prefixLift 7635613
  have htrace : WordTrace (prefixWord ++ tailWord_7635613) baseStart_7635613 baseEnd_7635613 := by
    simpa [prefixWord, tailWord_7635613, baseEnd_7635613] using wordTrace_append hprefix tailTrace_7635613
  have hstable : (prefixWord ++ tailWord_7635613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635613).length < 2 ^ (prefixWord ++ tailWord_7635613).sum := by decide
  have hdescent : baseEnd_7635613 < baseStart_7635613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635681 : List Nat := [1, 2, 3, 1, 4, 3, 2, 2, 1, 2, 2]
def baseStart_7635681 : Nat := 118140960795 + 7635681 * 2 ^ 59
def prefixEnd_7635681 : Nat := 4983230072969 + 3 ^ 40 * 7635681 * 2
def baseEnd_7635681 : Nat := 3920774477403445096671649

theorem tailTrace_7635681 : CollatzResearch.WordTrace tailWord_7635681 prefixEnd_7635681 3920774477403445096671649 := by
  unfold tailWord_7635681
  simp only [CollatzResearch.WordTrace]
  refine ⟨278496165450239282337554897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185664110300159521558369931 278496165450239282337554897)
  ·
    refine ⟨208872124087679461753166173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278496165450239282337554897 208872124087679461753166173)
    ·
      refine ⟨78327046532879798157437315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208872124087679461753166173 78327046532879798157437315)
      ·
        refine ⟨117490569799319697236155973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78327046532879798157437315 117490569799319697236155973)
        ·
          refine ⟨22029481837372443231779245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117490569799319697236155973 22029481837372443231779245)
          ·
            refine ⟨8261055689014666211917217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22029481837372443231779245 8261055689014666211917217)
            ·
              refine ⟨6195791766760999658937913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8261055689014666211917217 6195791766760999658937913)
              ·
                refine ⟨4646843825070749744203435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6195791766760999658937913 4646843825070749744203435)
                ·
                  refine ⟨6970265737606124616305153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4646843825070749744203435 6970265737606124616305153)
                  ·
                    refine ⟨5227699303204593462228865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6970265737606124616305153 5227699303204593462228865)
                    ·
                      refine ⟨3920774477403445096671649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5227699303204593462228865 3920774477403445096671649)
                      ·
                        rfl

theorem cell23_7635681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_7635681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635681 prefixEnd_7635681 := by exact prefixLift 7635681
  have htrace : WordTrace (prefixWord ++ tailWord_7635681) baseStart_7635681 baseEnd_7635681 := by
    simpa [prefixWord, tailWord_7635681, baseEnd_7635681] using wordTrace_append hprefix tailTrace_7635681
  have hstable : (prefixWord ++ tailWord_7635681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635681).length < 2 ^ (prefixWord ++ tailWord_7635681).sum := by decide
  have hdescent : baseEnd_7635681 < baseStart_7635681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635696 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 2, 6]
def baseStart_7635696 : Nat := 118140960795 + 7635696 * 2 ^ 59
def prefixEnd_7635696 : Nat := 4983230072969 + 3 ^ 40 * 7635696 * 2
def baseEnd_7635696 : Nat := 1306927393204420845994693

theorem tailTrace_7635696 : CollatzResearch.WordTrace tailWord_7635696 prefixEnd_7635696 1306927393204420845994693 := by
  unfold tailWord_7635696
  simp only [CollatzResearch.WordTrace]
  refine ⟨139248356272592469949675471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185664475030123293266233961 139248356272592469949675471)
  ·
    refine ⟨208872534408888704924513207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139248356272592469949675471 208872534408888704924513207)
    ·
      refine ⟨313308801613333057386769811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208872534408888704924513207 313308801613333057386769811)
      ·
        refine ⟨469963202419999586080154717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313308801613333057386769811 469963202419999586080154717)
        ·
          refine ⟨176236200907499844780058019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469963202419999586080154717 176236200907499844780058019)
          ·
            refine ⟨264354301361249767170087029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176236200907499844780058019 264354301361249767170087029)
            ·
              refine ⟨24783215752617165672195659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264354301361249767170087029 24783215752617165672195659)
              ·
                refine ⟨37174823628925748508293489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24783215752617165672195659 37174823628925748508293489)
                ·
                  refine ⟨27881117721694311381220117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37174823628925748508293489 27881117721694311381220117)
                  ·
                    refine ⟨1306927393204420845994693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27881117721694311381220117 1306927393204420845994693)
                    ·
                      rfl

theorem cell23_7635696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 2, 6].length) (baseStart_7635696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635696 prefixEnd_7635696 := by exact prefixLift 7635696
  have htrace : WordTrace (prefixWord ++ tailWord_7635696) baseStart_7635696 baseEnd_7635696 := by
    simpa [prefixWord, tailWord_7635696, baseEnd_7635696] using wordTrace_append hprefix tailTrace_7635696
  have hstable : (prefixWord ++ tailWord_7635696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635696).length < 2 ^ (prefixWord ++ tailWord_7635696).sum := by decide
  have hdescent : baseEnd_7635696 < baseStart_7635696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635706 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5]
def baseStart_7635706 : Nat := 118140960795 + 7635706 * 2 ^ 59
def prefixEnd_7635706 : Nat := 4983230072969 + 3 ^ 40 * 7635706 * 2
def baseEnd_7635706 : Nat := 3920787314419807498859033

theorem tailTrace_7635706 : CollatzResearch.WordTrace tailWord_7635706 prefixEnd_7635706 3920787314419807498859033 := by
  unfold tailWord_7635706
  simp only [CollatzResearch.WordTrace]
  refine ⟨69624269318787177901803743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185664718183432474404809981 69624269318787177901803743)
  ·
    refine ⟨104436403978180766852705615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69624269318787177901803743 104436403978180766852705615)
    ·
      refine ⟨156654605967271150279058423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104436403978180766852705615 156654605967271150279058423)
      ·
        refine ⟨234981908950906725418587635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156654605967271150279058423 234981908950906725418587635)
        ·
          refine ⟨352472863426360088127881453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234981908950906725418587635 352472863426360088127881453)
          ·
            refine ⟨132177323784885033047955545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352472863426360088127881453 132177323784885033047955545)
            ·
              refine ⟨99132992838663774785966659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132177323784885033047955545 99132992838663774785966659)
              ·
                refine ⟨148699489257995662178949989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99132992838663774785966659 148699489257995662178949989)
                ·
                  refine ⟨27881154235874186658553123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148699489257995662178949989 27881154235874186658553123)
                  ·
                    refine ⟨41821731353811279987829685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27881154235874186658553123 41821731353811279987829685)
                    ·
                      refine ⟨3920787314419807498859033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41821731353811279987829685 3920787314419807498859033)
                      ·
                        rfl

theorem cell23_7635706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_7635706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635706 prefixEnd_7635706 := by exact prefixLift 7635706
  have htrace : WordTrace (prefixWord ++ tailWord_7635706) baseStart_7635706 baseEnd_7635706 := by
    simpa [prefixWord, tailWord_7635706, baseEnd_7635706] using wordTrace_append hprefix tailTrace_7635706
  have hstable : (prefixWord ++ tailWord_7635706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635706).length < 2 ^ (prefixWord ++ tailWord_7635706).sum := by decide
  have hdescent : baseEnd_7635706 < baseStart_7635706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635720 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 1, 4, 2]
def baseStart_7635720 : Nat := 118140960795 + 7635720 * 2 ^ 59
def prefixEnd_7635720 : Nat := 4983230072969 + 3 ^ 40 * 7635720 * 2
def baseEnd_7635720 : Nat := 3920794503148970444083969

theorem tailTrace_7635720 : CollatzResearch.WordTrace tailWord_7635720 prefixEnd_7635720 3920794503148970444083969 := by
  unfold tailWord_7635720
  simp only [CollatzResearch.WordTrace]
  refine ⟨139248793948548995999112307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185665058598065327998816409 139248793948548995999112307)
  ·
    refine ⟨208873190922823493998668461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139248793948548995999112307 208873190922823493998668461)
    ·
      refine ⟨78327446596058810249500673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208873190922823493998668461 78327446596058810249500673)
      ·
        refine ⟨58745584947044107687125505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78327446596058810249500673 58745584947044107687125505)
        ·
          refine ⟨44059188710283080765344129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58745584947044107687125505 44059188710283080765344129)
          ·
            refine ⟨33044391532712310574008097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44059188710283080765344129 33044391532712310574008097)
            ·
              refine ⟨24783293649534232930506073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33044391532712310574008097 24783293649534232930506073)
              ·
                refine ⟨18587470237150674697879555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24783293649534232930506073 18587470237150674697879555)
                ·
                  refine ⟨27881205355726012046819333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18587470237150674697879555 27881205355726012046819333)
                  ·
                    refine ⟨5227726004198627258778625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27881205355726012046819333 5227726004198627258778625)
                    ·
                      refine ⟨3920794503148970444083969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5227726004198627258778625 3920794503148970444083969)
                      ·
                        rfl

theorem cell23_7635720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_7635720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635720 prefixEnd_7635720 := by exact prefixLift 7635720
  have htrace : WordTrace (prefixWord ++ tailWord_7635720) baseStart_7635720 baseEnd_7635720 := by
    simpa [prefixWord, tailWord_7635720, baseEnd_7635720] using wordTrace_append hprefix tailTrace_7635720
  have hstable : (prefixWord ++ tailWord_7635720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635720).length < 2 ^ (prefixWord ++ tailWord_7635720).sum := by decide
  have hdescent : baseEnd_7635720 < baseStart_7635720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635726 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 11]
def baseStart_7635726 : Nat := 118140960795 + 7635726 * 2 ^ 59
def prefixEnd_7635726 : Nat := 4983230072969 + 3 ^ 40 * 7635726 * 2
def baseEnd_7635726 : Nat := 435644176003655268956549

theorem tailTrace_7635726 : CollatzResearch.WordTrace tailWord_7635726 prefixEnd_7635726 435644176003655268956549 := by
  unfold tailWord_7635726
  simp only [CollatzResearch.WordTrace]
  refine ⟨34812225841884531877867879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185665204490050836681962021 34812225841884531877867879)
  ·
    refine ⟨52218338762826797816801819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34812225841884531877867879 52218338762826797816801819)
    ·
      refine ⟨78327508144240196725202729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52218338762826797816801819 78327508144240196725202729)
      ·
        refine ⟨58745631108180147543902047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78327508144240196725202729 58745631108180147543902047)
        ·
          refine ⟨88118446662270221315853071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58745631108180147543902047 88118446662270221315853071)
          ·
            refine ⟨132177669993405331973779607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88118446662270221315853071 132177669993405331973779607)
            ·
              refine ⟨198266504990107997960669411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132177669993405331973779607 198266504990107997960669411)
              ·
                refine ⟨297399757485161996941004117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198266504990107997960669411 297399757485161996941004117)
                ·
                  refine ⟨435644176003655268956549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 297399757485161996941004117 435644176003655268956549)
                  ·
                    rfl

theorem cell23_7635726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_7635726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635726 prefixEnd_7635726 := by exact prefixLift 7635726
  have htrace : WordTrace (prefixWord ++ tailWord_7635726) baseStart_7635726 baseEnd_7635726 := by
    simpa [prefixWord, tailWord_7635726, baseEnd_7635726] using wordTrace_append hprefix tailTrace_7635726
  have hstable : (prefixWord ++ tailWord_7635726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635726).length < 2 ^ (prefixWord ++ tailWord_7635726).sum := by decide
  have hdescent : baseEnd_7635726 < baseStart_7635726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635743 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 7]
def baseStart_7635743 : Nat := 118140960795 + 7635743 * 2 ^ 59
def prefixEnd_7635743 : Nat := 4983230072969 + 3 ^ 40 * 7635743 * 2
def baseEnd_7635743 : Nat := 435645145911558206010707

theorem tailTrace_7635743 : CollatzResearch.WordTrace tailWord_7635743 prefixEnd_7635743 435645145911558206010707 := by
  unfold tailWord_7635743
  simp only [CollatzResearch.WordTrace]
  refine ⟨278498426776014666926311883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185665617850676444617541255 278498426776014666926311883)
  ·
    refine ⟨417747640164022000389467825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278498426776014666926311883 417747640164022000389467825)
    ·
      refine ⟨313310730123016500292100869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417747640164022000389467825 313310730123016500292100869)
      ·
        refine ⟨58745761898065593804768913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313310730123016500292100869 58745761898065593804768913)
        ·
          refine ⟨44059321423549195353576685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58745761898065593804768913 44059321423549195353576685)
          ·
            refine ⟨16522245533830948257591257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44059321423549195353576685 16522245533830948257591257)
            ·
              refine ⟨12391684150373211193193443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16522245533830948257591257 12391684150373211193193443)
              ·
                refine ⟨18587526225559816789790165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12391684150373211193193443 18587526225559816789790165)
                ·
                  refine ⟨435645145911558206010707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18587526225559816789790165 435645145911558206010707)
                  ·
                    rfl

theorem cell23_7635743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 7].length) (baseStart_7635743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635743 prefixEnd_7635743 := by exact prefixLift 7635743
  have htrace : WordTrace (prefixWord ++ tailWord_7635743) baseStart_7635743 baseEnd_7635743 := by
    simpa [prefixWord, tailWord_7635743, baseEnd_7635743] using wordTrace_append hprefix tailTrace_7635743
  have hstable : (prefixWord ++ tailWord_7635743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635743).length < 2 ^ (prefixWord ++ tailWord_7635743).sum := by decide
  have hdescent : baseEnd_7635743 < baseStart_7635743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635756 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 3, 7]
def baseStart_7635756 : Nat := 118140960795 + 7635756 * 2 ^ 59
def prefixEnd_7635756 : Nat := 4983230072969 + 3 ^ 40 * 7635756 * 2
def baseEnd_7635756 : Nat := 1306937662817510767744601

theorem tailTrace_7635756 : CollatzResearch.WordTrace tailWord_7635756 prefixEnd_7635756 1306937662817510767744601 := by
  unfold tailWord_7635756
  simp only [CollatzResearch.WordTrace]
  refine ⟨139249450462483785073267561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185665933949978380097690081 139249450462483785073267561)
  ·
    refine ⟨104437087846862838804950671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139249450462483785073267561 104437087846862838804950671)
    ·
      refine ⟨156655631770294258207426007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104437087846862838804950671 156655631770294258207426007)
      ·
        refine ⟨234983447655441387311139011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156655631770294258207426007 234983447655441387311139011)
        ·
          refine ⟨352475171483162080966708517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234983447655441387311139011 352475171483162080966708517)
          ·
            refine ⟨66089094653092890181257847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352475171483162080966708517 66089094653092890181257847)
            ·
              refine ⟨99133641979639335271886771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66089094653092890181257847 99133641979639335271886771)
              ·
                refine ⟨148700462969459002907830157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99133641979639335271886771 148700462969459002907830157)
                ·
                  refine ⟨55762673613547126090436309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148700462969459002907830157 55762673613547126090436309)
                  ·
                    refine ⟨1306937662817510767744601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55762673613547126090436309 1306937662817510767744601)
                    ·
                      rfl

theorem cell23_7635756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_7635756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635756 prefixEnd_7635756 := by exact prefixLift 7635756
  have htrace : WordTrace (prefixWord ++ tailWord_7635756) baseStart_7635756 baseEnd_7635756 := by
    simpa [prefixWord, tailWord_7635756, baseEnd_7635756] using wordTrace_append hprefix tailTrace_7635756
  have hstable : (prefixWord ++ tailWord_7635756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635756).length < 2 ^ (prefixWord ++ tailWord_7635756).sum := by decide
  have hdescent : baseEnd_7635756 < baseStart_7635756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635813 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 3, 4, 3]
def baseStart_7635813 : Nat := 118140960795 + 7635813 * 2 ^ 59
def prefixEnd_7635813 : Nat := 4983230072969 + 3 ^ 40 * 7635813 * 2
def baseEnd_7635813 : Nat := 3920842256849838580221041

theorem tailTrace_7635813 : CollatzResearch.WordTrace tailWord_7635813 prefixEnd_7635813 3920842256849838580221041 := by
  unfold tailWord_7635813
  simp only [CollatzResearch.WordTrace]
  refine ⟨278500979885761068881360093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185667319923840712587573395 278500979885761068881360093)
  ·
    refine ⟨104437867457160400830510035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278500979885761068881360093 104437867457160400830510035)
    ·
      refine ⟨156656801185740601245765053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104437867457160400830510035 156656801185740601245765053)
      ·
        refine ⟨58746300444652725467161895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156656801185740601245765053 58746300444652725467161895)
        ·
          refine ⟨88119450666979088200742843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58746300444652725467161895 88119450666979088200742843)
          ·
            refine ⟨132179176000468632301114265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88119450666979088200742843 132179176000468632301114265)
            ·
              refine ⟨99134382000351474225835699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132179176000468632301114265 99134382000351474225835699)
              ·
                refine ⟨148701573000527211338753549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99134382000351474225835699 148701573000527211338753549)
                ·
                  refine ⟨55763089875197704252032581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148701573000527211338753549 55763089875197704252032581)
                  ·
                    refine ⟨10455579351599569547256109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55763089875197704252032581 10455579351599569547256109)
                    ·
                      refine ⟨3920842256849838580221041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10455579351599569547256109 3920842256849838580221041)
                      ·
                        rfl

theorem cell23_7635813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_7635813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635813 prefixEnd_7635813 := by exact prefixLift 7635813
  have htrace : WordTrace (prefixWord ++ tailWord_7635813) baseStart_7635813 baseEnd_7635813 := by
    simpa [prefixWord, tailWord_7635813, baseEnd_7635813] using wordTrace_append hprefix tailTrace_7635813
  have hstable : (prefixWord ++ tailWord_7635813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635813).length < 2 ^ (prefixWord ++ tailWord_7635813).sum := by decide
  have hdescent : baseEnd_7635813 < baseStart_7635813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635850 : List Nat := [3, 1, 2, 4, 1, 1, 1, 4, 6]
def baseStart_7635850 : Nat := 118140960795 + 7635850 * 2 ^ 59
def prefixEnd_7635850 : Nat := 4983230072969 + 3 ^ 40 * 7635850 * 2
def baseEnd_7635850 : Nat := 435651250626006103939819

theorem tailTrace_7635850 : CollatzResearch.WordTrace tailWord_7635850 prefixEnd_7635850 435651250626006103939819 := by
  unfold tailWord_7635850
  simp only [CollatzResearch.WordTrace]
  refine ⟨69625582346656756050114251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185668219591084682800304669 69625582346656756050114251)
  ·
    refine ⟨104438373519985134075171377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69625582346656756050114251 104438373519985134075171377)
    ·
      refine ⟨78328780139988850556378533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104438373519985134075171377 78328780139988850556378533)
      ·
        refine ⟨14686646276247909479320975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78328780139988850556378533 14686646276247909479320975)
        ·
          refine ⟨22029969414371864218981463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14686646276247909479320975 22029969414371864218981463)
          ·
            refine ⟨33044954121557796328472195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22029969414371864218981463 33044954121557796328472195)
            ·
              refine ⟨49567431182336694492708293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33044954121557796328472195 49567431182336694492708293)
              ·
                refine ⟨9293893346688130217382805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49567431182336694492708293 9293893346688130217382805)
                ·
                  refine ⟨435651250626006103939819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9293893346688130217382805 435651250626006103939819)
                  ·
                    rfl

theorem cell23_7635850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 6].length) (baseStart_7635850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635850 prefixEnd_7635850 := by exact prefixLift 7635850
  have htrace : WordTrace (prefixWord ++ tailWord_7635850) baseStart_7635850 baseEnd_7635850 := by
    simpa [prefixWord, tailWord_7635850, baseEnd_7635850] using wordTrace_append hprefix tailTrace_7635850
  have hstable : (prefixWord ++ tailWord_7635850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635850).length < 2 ^ (prefixWord ++ tailWord_7635850).sum := by decide
  have hdescent : baseEnd_7635850 < baseStart_7635850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635863 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 5, 5]
def baseStart_7635863 : Nat := 118140960795 + 7635863 * 2 ^ 59
def prefixEnd_7635863 : Nat := 4983230072969 + 3 ^ 40 * 7635863 * 2
def baseEnd_7635863 : Nat := 1306955976960854461531937

theorem tailTrace_7635863 : CollatzResearch.WordTrace tailWord_7635863 prefixEnd_7635863 1306955976960854461531937 := by
  unfold tailWord_7635863
  simp only [CollatzResearch.WordTrace]
  refine ⟨278502803535579927420680243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185668535690386618280453495 278502803535579927420680243)
  ·
    refine ⟨417754205303369891131020365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278502803535579927420680243 417754205303369891131020365)
    ·
      refine ⟨156657826988763709174132637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417754205303369891131020365 156657826988763709174132637)
      ·
        refine ⟨58746685120786390940299739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156657826988763709174132637 58746685120786390940299739)
        ·
          refine ⟨88120027681179586410449609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58746685120786390940299739 88120027681179586410449609)
          ·
            refine ⟨66090020760884689807837207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88120027681179586410449609 66090020760884689807837207)
            ·
              refine ⟨99135031141327034711755811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66090020760884689807837207 99135031141327034711755811)
              ·
                refine ⟨148702546711990552067633717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99135031141327034711755811 148702546711990552067633717)
                ·
                  refine ⟨13940863754249114256340661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148702546711990552067633717 13940863754249114256340661)
                  ·
                    refine ⟨1306955976960854461531937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13940863754249114256340661 1306955976960854461531937)
                    ·
                      rfl

theorem cell23_7635863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_7635863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635863 prefixEnd_7635863 := by exact prefixLift 7635863
  have htrace : WordTrace (prefixWord ++ tailWord_7635863) baseStart_7635863 baseEnd_7635863 := by
    simpa [prefixWord, tailWord_7635863, baseEnd_7635863] using wordTrace_append hprefix tailTrace_7635863
  have hstable : (prefixWord ++ tailWord_7635863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635863).length < 2 ^ (prefixWord ++ tailWord_7635863).sum := by decide
  have hdescent : baseEnd_7635863 < baseStart_7635863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635897 : List Nat := [1, 2, 1, 4, 2, 2, 4, 1, 1, 5]
def baseStart_7635897 : Nat := 118140960795 + 7635897 * 2 ^ 59
def prefixEnd_7635897 : Nat := 4983230072969 + 3 ^ 40 * 7635897 * 2
def baseEnd_7635897 : Nat := 1306961796408272083856885

theorem tailTrace_7635897 : CollatzResearch.WordTrace tailWord_7635897 prefixEnd_7635897 1306961796408272083856885 := by
  unfold tailWord_7635897
  simp only [CollatzResearch.WordTrace]
  refine ⟨278504043617456751227417945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185669362411637834151611963 278504043617456751227417945)
  ·
    refine ⟨208878032713092563420563459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278504043617456751227417945 208878032713092563420563459)
    ·
      refine ⟨313317049069638845130845189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208878032713092563420563459 313317049069638845130845189)
      ·
        refine ⟨58746946700557283462033473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313317049069638845130845189 58746946700557283462033473)
        ·
          refine ⟨44060210025417962596525105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58746946700557283462033473 44060210025417962596525105)
          ·
            refine ⟨33045157519063471947393829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44060210025417962596525105 33045157519063471947393829)
            ·
              refine ⟨6195967034824400990136343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33045157519063471947393829 6195967034824400990136343)
              ·
                refine ⟨9293950552236601485204515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6195967034824400990136343 9293950552236601485204515)
                ·
                  refine ⟨13940925828354902227806773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9293950552236601485204515 13940925828354902227806773)
                  ·
                    refine ⟨1306961796408272083856885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13940925828354902227806773 1306961796408272083856885)
                    ·
                      rfl

theorem cell23_7635897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 1, 5].length) (baseStart_7635897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635897 prefixEnd_7635897 := by exact prefixLift 7635897
  have htrace : WordTrace (prefixWord ++ tailWord_7635897) baseStart_7635897 baseEnd_7635897 := by
    simpa [prefixWord, tailWord_7635897, baseEnd_7635897] using wordTrace_append hprefix tailTrace_7635897
  have hstable : (prefixWord ++ tailWord_7635897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635897).length < 2 ^ (prefixWord ++ tailWord_7635897).sum := by decide
  have hdescent : baseEnd_7635897 < baseStart_7635897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635930 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6]
def baseStart_7635930 : Nat := 118140960795 + 7635930 * 2 ^ 59
def prefixEnd_7635930 : Nat := 4983230072969 + 3 ^ 40 * 7635930 * 2
def baseEnd_7635930 : Nat := 3920902334086414622458003

theorem tailTrace_7635930 : CollatzResearch.WordTrace tailWord_7635930 prefixEnd_7635930 3920902334086414622458003 := by
  unfold tailWord_7635930
  simp only [CollatzResearch.WordTrace]
  refine ⟨69626311806584299465842311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185670164817558131908912829 69626311806584299465842311)
  ·
    refine ⟨104439467709876449198763467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69626311806584299465842311 104439467709876449198763467)
    ·
      refine ⟨156659201564814673798145201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104439467709876449198763467 156659201564814673798145201)
      ·
        refine ⟨117494401173611005348608901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156659201564814673798145201 117494401173611005348608901)
        ·
          refine ⟨22030200220052063502864169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117494401173611005348608901 22030200220052063502864169)
          ·
            refine ⟨16522650165039047627148127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22030200220052063502864169 16522650165039047627148127)
            ·
              refine ⟨24783975247558571440722191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16522650165039047627148127 24783975247558571440722191)
              ·
                refine ⟨37175962871337857161083287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24783975247558571440722191 37175962871337857161083287)
                ·
                  refine ⟨55763944307006785741624931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37175962871337857161083287 55763944307006785741624931)
                  ·
                    refine ⟨83645916460510178612437397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55763944307006785741624931 83645916460510178612437397)
                    ·
                      refine ⟨3920902334086414622458003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83645916460510178612437397 3920902334086414622458003)
                      ·
                        rfl

theorem cell23_7635930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_7635930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635930 prefixEnd_7635930 := by exact prefixLift 7635930
  have htrace : WordTrace (prefixWord ++ tailWord_7635930) baseStart_7635930 baseEnd_7635930 := by
    simpa [prefixWord, tailWord_7635930, baseEnd_7635930] using wordTrace_append hprefix tailTrace_7635930
  have hstable : (prefixWord ++ tailWord_7635930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635930).length < 2 ^ (prefixWord ++ tailWord_7635930).sum := by decide
  have hdescent : baseEnd_7635930 < baseStart_7635930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635951 : List Nat := [1, 1, 2, 1, 4, 3, 3, 3, 1, 2, 2]
def baseStart_7635951 : Nat := 118140960795 + 7635951 * 2 ^ 59
def prefixEnd_7635951 : Nat := 4983230072969 + 3 ^ 40 * 7635951 * 2
def baseEnd_7635951 : Nat := 3920913117180159040295407

theorem tailTrace_7635951 : CollatzResearch.WordTrace tailWord_7635951 prefixEnd_7635951 3920913117180159040295407 := by
  unfold tailWord_7635951
  simp only [CollatzResearch.WordTrace]
  refine ⟨278506013159261118449883707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185670675439507412299922471 278506013159261118449883707)
  ·
    refine ⟨417759019738891677674825561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278506013159261118449883707 417759019738891677674825561)
    ·
      refine ⟨313319264804168758256119171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417759019738891677674825561 313319264804168758256119171)
      ·
        refine ⟨469978897206253137384178757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313319264804168758256119171 469978897206253137384178757)
        ·
          refine ⟨88121043226172463259533517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 469978897206253137384178757 88121043226172463259533517)
          ·
            refine ⟨33045391209814673722325069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88121043226172463259533517 33045391209814673722325069)
            ·
              refine ⟨12392021703680502645871901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33045391209814673722325069 12392021703680502645871901)
              ·
                refine ⟨4647008138880188492201963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12392021703680502645871901 4647008138880188492201963)
                ·
                  refine ⟨6970512208320282738302945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4647008138880188492201963 6970512208320282738302945)
                  ·
                    refine ⟨5227884156240212053727209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6970512208320282738302945 5227884156240212053727209)
                    ·
                      refine ⟨3920913117180159040295407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5227884156240212053727209 3920913117180159040295407)
                      ·
                        rfl

theorem cell23_7635951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 1, 2, 2].length) (baseStart_7635951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635951 prefixEnd_7635951 := by exact prefixLift 7635951
  have htrace : WordTrace (prefixWord ++ tailWord_7635951) baseStart_7635951 baseEnd_7635951 := by
    simpa [prefixWord, tailWord_7635951, baseEnd_7635951] using wordTrace_append hprefix tailTrace_7635951
  have hstable : (prefixWord ++ tailWord_7635951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635951).length < 2 ^ (prefixWord ++ tailWord_7635951).sum := by decide
  have hdescent : baseEnd_7635951 < baseStart_7635951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635954 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 1, 1, 5]
def baseStart_7635954 : Nat := 118140960795 + 7635954 * 2 ^ 59
def prefixEnd_7635954 : Nat := 4983230072969 + 3 ^ 40 * 7635954 * 2
def baseEnd_7635954 : Nat := 3920914657622122528557893

theorem tailTrace_7635954 : CollatzResearch.WordTrace tailWord_7635954 prefixEnd_7635954 3920914657622122528557893 := by
  unfold tailWord_7635954
  simp only [CollatzResearch.WordTrace]
  refine ⟨69626530644562562490560729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185670748385500166641495277 69626530644562562490560729)
  ·
    refine ⟨52219897983421921867920547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69626530644562562490560729 52219897983421921867920547)
    ·
      refine ⟨78329846975132882801880821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52219897983421921867920547 78329846975132882801880821)
      ·
        refine ⟨7343423153918707762676327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78329846975132882801880821 7343423153918707762676327)
        ·
          refine ⟨11015134730878061644014491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7343423153918707762676327 11015134730878061644014491)
          ·
            refine ⟨16522702096317092466021737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11015134730878061644014491 16522702096317092466021737)
            ·
              refine ⟨12392026572237819349516303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16522702096317092466021737 12392026572237819349516303)
              ·
                refine ⟨18588039858356729024274455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12392026572237819349516303 18588039858356729024274455)
                ·
                  refine ⟨27882059787535093536411683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18588039858356729024274455 27882059787535093536411683)
                  ·
                    refine ⟨41823089681302640304617525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27882059787535093536411683 41823089681302640304617525)
                    ·
                      refine ⟨3920914657622122528557893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41823089681302640304617525 3920914657622122528557893)
                      ·
                        rfl

theorem cell23_7635954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_7635954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635954 prefixEnd_7635954 := by exact prefixLift 7635954
  have htrace : WordTrace (prefixWord ++ tailWord_7635954) baseStart_7635954 baseEnd_7635954 := by
    simpa [prefixWord, tailWord_7635954, baseEnd_7635954] using wordTrace_append hprefix tailTrace_7635954
  have hstable : (prefixWord ++ tailWord_7635954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635954).length < 2 ^ (prefixWord ++ tailWord_7635954).sum := by decide
  have hdescent : baseEnd_7635954 < baseStart_7635954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7635963 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 5]
def baseStart_7635963 : Nat := 118140960795 + 7635963 * 2 ^ 59
def prefixEnd_7635963 : Nat := 4983230072969 + 3 ^ 40 * 7635963 * 2
def baseEnd_7635963 : Nat := 3920919278948012993345351

theorem tailTrace_7635963 : CollatzResearch.WordTrace tailWord_7635963 prefixEnd_7635963 3920919278948012993345351 := by
  unfold tailWord_7635963
  simp only [CollatzResearch.WordTrace]
  refine ⟨278506450835217644499320543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185670967223478429666213695 278506450835217644499320543)
  ·
    refine ⟨417759676252826466748980815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278506450835217644499320543 417759676252826466748980815)
    ·
      refine ⟨626639514379239700123471223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417759676252826466748980815 626639514379239700123471223)
      ·
        refine ⟨939959271568859550185206835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626639514379239700123471223 939959271568859550185206835)
        ·
          refine ⟨1409938907353289325277810253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939959271568859550185206835 1409938907353289325277810253)
          ·
            refine ⟨528727090257483496979178845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1409938907353289325277810253 528727090257483496979178845)
            ·
              refine ⟨198272658846556311367192067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 528727090257483496979178845 198272658846556311367192067)
              ·
                refine ⟨297408988269834467050788101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198272658846556311367192067 297408988269834467050788101)
                ·
                  refine ⟨55764185300593962572022769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297408988269834467050788101 55764185300593962572022769)
                  ·
                    refine ⟨41823138975445471929017077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55764185300593962572022769 41823138975445471929017077)
                    ·
                      refine ⟨3920919278948012993345351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41823138975445471929017077 3920919278948012993345351)
                      ·
                        rfl

theorem cell23_7635963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 5].length) (baseStart_7635963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7635963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7635963 prefixEnd_7635963 := by exact prefixLift 7635963
  have htrace : WordTrace (prefixWord ++ tailWord_7635963) baseStart_7635963 baseEnd_7635963 := by
    simpa [prefixWord, tailWord_7635963, baseEnd_7635963] using wordTrace_append hprefix tailTrace_7635963
  have hstable : (prefixWord ++ tailWord_7635963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7635963).length < 2 ^ (prefixWord ++ tailWord_7635963).sum := by decide
  have hdescent : baseEnd_7635963 < baseStart_7635963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7635963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636062 : List Nat := [4, 4, 1, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_7636062 : Nat := 118140960795 + 7636062 * 2 ^ 59
def prefixEnd_7636062 : Nat := 4983230072969 + 3 ^ 40 * 7636062 * 2
def baseEnd_7636062 : Nat := 3920970113532808106007397

theorem tailTrace_7636062 : CollatzResearch.WordTrace tailWord_7636062 prefixEnd_7636062 3920970113532808106007397 := by
  unfold tailWord_7636062
  simp only [CollatzResearch.WordTrace]
  refine ⟨34813757707732373050896805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185673374441239322938116293 34813757707732373050896805)
  ·
    refine ⟨6527579570199819947043151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34813757707732373050896805 6527579570199819947043151)
    ·
      refine ⟨9791369355299729920564727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6527579570199819947043151 9791369355299729920564727)
      ·
        refine ⟨14687054032949594880847091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9791369355299729920564727 14687054032949594880847091)
        ·
          refine ⟨22030581049424392321270637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14687054032949594880847091 22030581049424392321270637)
          ·
            refine ⟨8261467893534147120476489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22030581049424392321270637 8261467893534147120476489)
            ·
              refine ⟨6196100920150610340357367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8261467893534147120476489 6196100920150610340357367)
              ·
                refine ⟨9294151380225915510536051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6196100920150610340357367 9294151380225915510536051)
                ·
                  refine ⟨13941227070338873265804077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9294151380225915510536051 13941227070338873265804077)
                  ·
                    refine ⟨5227960151377077474676529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13941227070338873265804077 5227960151377077474676529)
                    ·
                      refine ⟨3920970113532808106007397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5227960151377077474676529 3920970113532808106007397)
                      ·
                        rfl

theorem cell23_7636062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_7636062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636062 prefixEnd_7636062 := by exact prefixLift 7636062
  have htrace : WordTrace (prefixWord ++ tailWord_7636062) baseStart_7636062 baseEnd_7636062 := by
    simpa [prefixWord, tailWord_7636062, baseEnd_7636062] using wordTrace_append hprefix tailTrace_7636062
  have hstable : (prefixWord ++ tailWord_7636062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636062).length < 2 ^ (prefixWord ++ tailWord_7636062).sum := by decide
  have hdescent : baseEnd_7636062 < baseStart_7636062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636097 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_7636097 : Nat := 118140960795 + 7636097 * 2 ^ 59
def prefixEnd_7636097 : Nat := 4983230072969 + 3 ^ 40 * 7636097 * 2
def baseEnd_7636097 : Nat := 3920988085355715469069735

theorem tailTrace_7636097 : CollatzResearch.WordTrace tailWord_7636097 prefixEnd_7636097 3920988085355715469069735 := by
  unfold tailWord_7636097
  simp only [CollatzResearch.WordTrace]
  refine ⟨278511338216732185384698545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185674225477821456923132363 278511338216732185384698545)
  ·
    refine ⟨208883503662549139038523909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278511338216732185384698545 208883503662549139038523909)
    ·
      refine ⟨39165656936727963569723233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208883503662549139038523909 39165656936727963569723233)
      ·
        refine ⟨29374242702545972677292425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39165656936727963569723233 29374242702545972677292425)
        ·
          refine ⟨22030682026909479507969319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29374242702545972677292425 22030682026909479507969319)
          ·
            refine ⟨33046023040364219261953979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22030682026909479507969319 33046023040364219261953979)
            ·
              refine ⟨49569034560546328892930969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33046023040364219261953979 49569034560546328892930969)
              ·
                refine ⟨37176775920409746669698227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49569034560546328892930969 37176775920409746669698227)
                ·
                  refine ⟨55765163880614620004547341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37176775920409746669698227 55765163880614620004547341)
                  ·
                    refine ⟨20911936455230482501705253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55765163880614620004547341 20911936455230482501705253)
                    ·
                      refine ⟨3920988085355715469069735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20911936455230482501705253 3920988085355715469069735)
                      ·
                        rfl

theorem cell23_7636097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_7636097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636097 prefixEnd_7636097 := by exact prefixLift 7636097
  have htrace : WordTrace (prefixWord ++ tailWord_7636097) baseStart_7636097 baseEnd_7636097 := by
    simpa [prefixWord, tailWord_7636097, baseEnd_7636097] using wordTrace_append hprefix tailTrace_7636097
  have hstable : (prefixWord ++ tailWord_7636097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636097).length < 2 ^ (prefixWord ++ tailWord_7636097).sum := by decide
  have hdescent : baseEnd_7636097 < baseStart_7636097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636140 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_7636140 : Nat := 118140960795 + 7636140 * 2 ^ 59
def prefixEnd_7636140 : Nat := 4983230072969 + 3 ^ 40 * 7636140 * 2
def baseEnd_7636140 : Nat := 3921010165023858800832037

theorem tailTrace_7636140 : CollatzResearch.WordTrace tailWord_7636140 prefixEnd_7636140 3921010165023858800832037 := by
  unfold tailWord_7636140
  simp only [CollatzResearch.WordTrace]
  refine ⟨139256453277788201864256937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185675271037050935819009249 139256453277788201864256937)
  ·
    refine ⟨104442339958341151398192703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139256453277788201864256937 104442339958341151398192703)
    ·
      refine ⟨156663509937511727097289055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104442339958341151398192703 156663509937511727097289055)
      ·
        refine ⟨234995264906267590645933583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156663509937511727097289055 234995264906267590645933583)
        ·
          refine ⟨352492897359401385968900375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234995264906267590645933583 352492897359401385968900375)
          ·
            refine ⟨528739346039102078953350563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352492897359401385968900375 528739346039102078953350563)
            ·
              refine ⟨793109019058653118430025845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528739346039102078953350563 793109019058653118430025845)
              ·
                refine ⟨74353970536748729852814923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 793109019058653118430025845 74353970536748729852814923)
                ·
                  refine ⟨111530955805123094779222385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74353970536748729852814923 111530955805123094779222385)
                  ·
                    refine ⟨83648216853842321084416789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111530955805123094779222385 83648216853842321084416789)
                    ·
                      refine ⟨3921010165023858800832037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83648216853842321084416789 3921010165023858800832037)
                      ·
                        rfl

theorem cell23_7636140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_7636140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636140 prefixEnd_7636140 := by exact prefixLift 7636140
  have htrace : WordTrace (prefixWord ++ tailWord_7636140) baseStart_7636140 baseEnd_7636140 := by
    simpa [prefixWord, tailWord_7636140, baseEnd_7636140] using wordTrace_append hprefix tailTrace_7636140
  have hstable : (prefixWord ++ tailWord_7636140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636140).length < 2 ^ (prefixWord ++ tailWord_7636140).sum := by decide
  have hdescent : baseEnd_7636140 < baseStart_7636140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636214 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_7636214 : Nat := 118140960795 + 7636214 * 2 ^ 59
def prefixEnd_7636214 : Nat := 4983230072969 + 3 ^ 40 * 7636214 * 2
def baseEnd_7636214 : Nat := 1307016054197430503768899

theorem tailTrace_7636214 : CollatzResearch.WordTrace tailWord_7636214 prefixEnd_7636214 1307016054197430503768899 := by
  unfold tailWord_7636214
  simp only [CollatzResearch.WordTrace]
  refine ⟨17407225347331769647919231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185677070371538876244471797 17407225347331769647919231)
  ·
    refine ⟨26110838020997654471878847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17407225347331769647919231 26110838020997654471878847)
    ·
      refine ⟨39166257031496481707818271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26110838020997654471878847 39166257031496481707818271)
      ·
        refine ⟨58749385547244722561727407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39166257031496481707818271 58749385547244722561727407)
        ·
          refine ⟨88124078320867083842591111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58749385547244722561727407 88124078320867083842591111)
          ·
            refine ⟨132186117481300625763886667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88124078320867083842591111 132186117481300625763886667)
            ·
              refine ⟨198279176221950938645830001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132186117481300625763886667 198279176221950938645830001)
              ·
                refine ⟨148709382166463203984372501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198279176221950938645830001 148709382166463203984372501)
                ·
                  refine ⟨6970752289052962686767461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148709382166463203984372501 6970752289052962686767461)
                  ·
                    refine ⟨1307016054197430503768899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6970752289052962686767461 1307016054197430503768899)
                    ·
                      rfl

theorem cell23_7636214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_7636214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636214 prefixEnd_7636214 := by exact prefixLift 7636214
  have htrace : WordTrace (prefixWord ++ tailWord_7636214) baseStart_7636214 baseEnd_7636214 := by
    simpa [prefixWord, tailWord_7636214, baseEnd_7636214] using wordTrace_append hprefix tailTrace_7636214
  have hstable : (prefixWord ++ tailWord_7636214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636214).length < 2 ^ (prefixWord ++ tailWord_7636214).sum := by decide
  have hdescent : baseEnd_7636214 < baseStart_7636214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636224 : List Nat := [2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 3]
def baseStart_7636224 : Nat := 118140960795 + 7636224 * 2 ^ 59
def prefixEnd_7636224 : Nat := 4983230072969 + 3 ^ 40 * 7636224 * 2
def baseEnd_7636224 : Nat := 3921053297398836472181651

theorem tailTrace_7636224 : CollatzResearch.WordTrace tailWord_7636224 prefixEnd_7636224 3921053297398836472181651 := by
  unfold tailWord_7636224
  simp only [CollatzResearch.WordTrace]
  refine ⟨139257985143636043037285863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185677313524848057383047817 139257985143636043037285863)
  ·
    refine ⟨208886977715454064555928795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139257985143636043037285863 208886977715454064555928795)
    ·
      refine ⟨313330466573181096833893193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208886977715454064555928795 313330466573181096833893193)
      ·
        refine ⟨234997849929885822625419895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313330466573181096833893193 234997849929885822625419895)
        ·
          refine ⟨352496774894828733938129843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234997849929885822625419895 352496774894828733938129843)
          ·
            refine ⟨528745162342243100907194765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352496774894828733938129843 528745162342243100907194765)
            ·
              refine ⟨198279435878341162840198037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 528745162342243100907194765 198279435878341162840198037)
              ·
                refine ⟨9294348556797242008134283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 198279435878341162840198037 9294348556797242008134283)
                ·
                  refine ⟨13941522835195863012201425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9294348556797242008134283 13941522835195863012201425)
                  ·
                    refine ⟨10456142126396897259151069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13941522835195863012201425 10456142126396897259151069)
                    ·
                      refine ⟨3921053297398836472181651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10456142126396897259151069 3921053297398836472181651)
                      ·
                        rfl

theorem cell23_7636224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_7636224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636224 prefixEnd_7636224 := by exact prefixLift 7636224
  have htrace : WordTrace (prefixWord ++ tailWord_7636224) baseStart_7636224 baseEnd_7636224 := by
    simpa [prefixWord, tailWord_7636224, baseEnd_7636224] using wordTrace_append hprefix tailTrace_7636224
  have hstable : (prefixWord ++ tailWord_7636224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636224).length < 2 ^ (prefixWord ++ tailWord_7636224).sum := by decide
  have hdescent : baseEnd_7636224 < baseStart_7636224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636238 : List Nat := [4, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4]
def baseStart_7636238 : Nat := 118140960795 + 7636238 * 2 ^ 59
def prefixEnd_7636238 : Nat := 4983230072969 + 3 ^ 40 * 7636238 * 2
def baseEnd_7636238 : Nat := 3921060486127999417406587

theorem tailTrace_7636238 : CollatzResearch.WordTrace tailWord_7636238 prefixEnd_7636238 3921060486127999417406587 := by
  unfold tailWord_7636238
  simp only [CollatzResearch.WordTrace]
  refine ⟨34814560113652670808197671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185677653939480910977054245 34814560113652670808197671)
  ·
    refine ⟨52221840170479006212296507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34814560113652670808197671 52221840170479006212296507)
    ·
      refine ⟨78332760255718509318444761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52221840170479006212296507 78332760255718509318444761)
      ·
        refine ⟨58749570191788881988833571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78332760255718509318444761 58749570191788881988833571)
        ·
          refine ⟨88124355287683322983250357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58749570191788881988833571 88124355287683322983250357)
          ·
            refine ⟨8261658308220311529679721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88124355287683322983250357 8261658308220311529679721)
            ·
              refine ⟨6196243731165233647259791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8261658308220311529679721 6196243731165233647259791)
              ·
                refine ⟨9294365596747850470889687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6196243731165233647259791 9294365596747850470889687)
                ·
                  refine ⟨13941548395121775706334531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9294365596747850470889687 13941548395121775706334531)
                  ·
                    refine ⟨20912322592682663559501797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13941548395121775706334531 20912322592682663559501797)
                    ·
                      refine ⟨3921060486127999417406587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20912322592682663559501797 3921060486127999417406587)
                      ·
                        rfl

theorem cell23_7636238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_7636238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636238 prefixEnd_7636238 := by exact prefixLift 7636238
  have htrace : WordTrace (prefixWord ++ tailWord_7636238) baseStart_7636238 baseEnd_7636238 := by
    simpa [prefixWord, tailWord_7636238, baseEnd_7636238] using wordTrace_append hprefix tailTrace_7636238
  have hstable : (prefixWord ++ tailWord_7636238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636238).length < 2 ^ (prefixWord ++ tailWord_7636238).sum := by decide
  have hdescent : baseEnd_7636238 < baseStart_7636238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636297 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 1, 3, 5]
def baseStart_7636297 : Nat := 118140960795 + 7636297 * 2 ^ 59
def prefixEnd_7636297 : Nat := 4983230072969 + 3 ^ 40 * 7636297 * 2
def baseEnd_7636297 : Nat := 3921090781486614686568815

theorem tailTrace_7636297 : CollatzResearch.WordTrace tailWord_7636297 prefixEnd_7636297 3921090781486614686568815 := by
  unfold tailWord_7636297
  simp only [CollatzResearch.WordTrace]
  refine ⟨278518632816007619541979145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185679088544005079694652763 278518632816007619541979145)
  ·
    refine ⟨208888974612005714656484359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278518632816007619541979145 208888974612005714656484359)
    ·
      refine ⟨313333461918008571984726539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208888974612005714656484359 313333461918008571984726539)
      ·
        refine ⟨470000192877012857977089809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313333461918008571984726539 470000192877012857977089809)
        ·
          refine ⟨352500144657759643482817357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470000192877012857977089809 352500144657759643482817357)
          ·
            refine ⟨132187554246659866306056509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352500144657759643482817357 132187554246659866306056509)
            ·
              refine ⟨49570332842497449864771191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132187554246659866306056509 49570332842497449864771191)
              ·
                refine ⟨74355499263746174797156787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49570332842497449864771191 74355499263746174797156787)
                ·
                  refine ⟨111533248895619262195735181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74355499263746174797156787 111533248895619262195735181)
                  ·
                    refine ⟨41824968335857223323400693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111533248895619262195735181 41824968335857223323400693)
                    ·
                      refine ⟨3921090781486614686568815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41824968335857223323400693 3921090781486614686568815)
                      ·
                        rfl

theorem cell23_7636297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_7636297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636297 prefixEnd_7636297 := by exact prefixLift 7636297
  have htrace : WordTrace (prefixWord ++ tailWord_7636297) baseStart_7636297 baseEnd_7636297 := by
    simpa [prefixWord, tailWord_7636297, baseEnd_7636297] using wordTrace_append hprefix tailTrace_7636297
  have hstable : (prefixWord ++ tailWord_7636297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636297).length < 2 ^ (prefixWord ++ tailWord_7636297).sum := by decide
  have hdescent : baseEnd_7636297 < baseStart_7636297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636364 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 2, 5]
def baseStart_7636364 : Nat := 118140960795 + 7636364 * 2 ^ 59
def prefixEnd_7636364 : Nat := 4983230072969 + 3 ^ 40 * 7636364 * 2
def baseEnd_7636364 : Nat := 1307041728230155308143669

theorem tailTrace_7636364 : CollatzResearch.WordTrace tailWord_7636364 prefixEnd_7636364 1307041728230155308143669 := by
  unfold tailWord_7636364
  simp only [CollatzResearch.WordTrace]
  refine ⟨139260538253382444992334073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185680717671176593323112097 139260538253382444992334073)
  ·
    refine ⟨104445403690036833744250555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139260538253382444992334073 104445403690036833744250555)
    ·
      refine ⟨156668105535055250616375833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104445403690036833744250555 156668105535055250616375833)
      ·
        refine ⟨117501079151291437962281875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156668105535055250616375833 117501079151291437962281875)
        ·
          refine ⟨176251618726937156943422813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117501079151291437962281875 176251618726937156943422813)
          ·
            refine ⟨66094357022601433853783555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176251618726937156943422813 66094357022601433853783555)
            ·
              refine ⟨99141535533902150780675333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66094357022601433853783555 99141535533902150780675333)
              ·
                refine ⟨18589037912606653271376625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99141535533902150780675333 18589037912606653271376625)
                ·
                  refine ⟨13941778434454989953532469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18589037912606653271376625 13941778434454989953532469)
                  ·
                    refine ⟨1307041728230155308143669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13941778434454989953532469 1307041728230155308143669)
                    ·
                      rfl

theorem cell23_7636364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_7636364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636364 prefixEnd_7636364 := by exact prefixLift 7636364
  have htrace : WordTrace (prefixWord ++ tailWord_7636364) baseStart_7636364 baseEnd_7636364 := by
    simpa [prefixWord, tailWord_7636364, baseEnd_7636364] using wordTrace_append hprefix tailTrace_7636364
  have hstable : (prefixWord ++ tailWord_7636364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636364).length < 2 ^ (prefixWord ++ tailWord_7636364).sum := by decide
  have hdescent : baseEnd_7636364 < baseStart_7636364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636384 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 4]
def baseStart_7636384 : Nat := 118140960795 + 7636384 * 2 ^ 59
def prefixEnd_7636384 : Nat := 4983230072969 + 3 ^ 40 * 7636384 * 2
def baseEnd_7636384 : Nat := 3921135454303555846180915

theorem tailTrace_7636384 : CollatzResearch.WordTrace tailWord_7636384 prefixEnd_7636384 3921135454303555846180915 := by
  unfold tailWord_7636384
  simp only [CollatzResearch.WordTrace]
  refine ⟨139260902983346216700198103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185681203977794955600264137 139260902983346216700198103)
  ·
    refine ⟨208891354475019325050297155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139260902983346216700198103 208891354475019325050297155)
    ·
      refine ⟨313337031712528987575445733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208891354475019325050297155 313337031712528987575445733)
      ·
        refine ⟨58750693446099185170396075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313337031712528987575445733 58750693446099185170396075)
        ·
          refine ⟨88126040169148777755594113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58750693446099185170396075 88126040169148777755594113)
          ·
            refine ⟨66094530126861583316695585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88126040169148777755594113 66094530126861583316695585)
            ·
              refine ⟨49570897595146187487521689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66094530126861583316695585 49570897595146187487521689)
              ·
                refine ⟨37178173196359640615641267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49570897595146187487521689 37178173196359640615641267)
                ·
                  refine ⟨55767259794539460923461901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37178173196359640615641267 55767259794539460923461901)
                  ·
                    refine ⟨20912722422952297846298213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55767259794539460923461901 20912722422952297846298213)
                    ·
                      refine ⟨3921135454303555846180915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20912722422952297846298213 3921135454303555846180915)
                      ·
                        rfl

theorem cell23_7636384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_7636384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636384 prefixEnd_7636384 := by exact prefixLift 7636384
  have htrace : WordTrace (prefixWord ++ tailWord_7636384) baseStart_7636384 baseEnd_7636384 := by
    simpa [prefixWord, tailWord_7636384, baseEnd_7636384] using wordTrace_append hprefix tailTrace_7636384
  have hstable : (prefixWord ++ tailWord_7636384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636384).length < 2 ^ (prefixWord ++ tailWord_7636384).sum := by decide
  have hdescent : baseEnd_7636384 < baseStart_7636384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636401 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 1, 6, 2]
def baseStart_7636401 : Nat := 118140960795 + 7636401 * 2 ^ 59
def prefixEnd_7636401 : Nat := 4983230072969 + 3 ^ 40 * 7636401 * 2
def baseEnd_7636401 : Nat := 3921144183474682279668337

theorem tailTrace_7636401 : CollatzResearch.WordTrace tailWord_7636401 prefixEnd_7636401 3921144183474682279668337 := by
  unfold tailWord_7636401
  simp only [CollatzResearch.WordTrace]
  refine ⟨278522426007630845303765057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185681617338420563535843371 278522426007630845303765057)
  ·
    refine ⟨208891819505723133977823793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278522426007630845303765057 208891819505723133977823793)
    ·
      refine ⟨156668864629292350483367845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208891819505723133977823793 156668864629292350483367845)
      ·
        refine ⟨29375412117992315715631471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156668864629292350483367845 29375412117992315715631471)
        ·
          refine ⟨44063118176988473573447207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29375412117992315715631471 44063118176988473573447207)
          ·
            refine ⟨66094677265482710360170811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44063118176988473573447207 66094677265482710360170811)
            ·
              refine ⟨99142015898224065540256217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66094677265482710360170811 99142015898224065540256217)
              ·
                refine ⟨74356511923668049155192163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99142015898224065540256217 74356511923668049155192163)
                ·
                  refine ⟨111534767885502073732788245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74356511923668049155192163 111534767885502073732788245)
                  ·
                    refine ⟨5228192244632909706224449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111534767885502073732788245 5228192244632909706224449)
                    ·
                      refine ⟨3921144183474682279668337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5228192244632909706224449 3921144183474682279668337)
                      ·
                        rfl

theorem cell23_7636401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_7636401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636401 prefixEnd_7636401 := by exact prefixLift 7636401
  have htrace : WordTrace (prefixWord ++ tailWord_7636401) baseStart_7636401 baseEnd_7636401 := by
    simpa [prefixWord, tailWord_7636401, baseEnd_7636401] using wordTrace_append hprefix tailTrace_7636401
  have hstable : (prefixWord ++ tailWord_7636401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636401).length < 2 ^ (prefixWord ++ tailWord_7636401).sum := by decide
  have hdescent : baseEnd_7636401 < baseStart_7636401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636424 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 8]
def baseStart_7636424 : Nat := 118140960795 + 7636424 * 2 ^ 59
def prefixEnd_7636424 : Nat := 4983230072969 + 3 ^ 40 * 7636424 * 2
def baseEnd_7636424 : Nat := 435683999281081743297859

theorem tailTrace_7636424 : CollatzResearch.WordTrace tailWord_7636424 prefixEnd_7636424 435683999281081743297859 := by
  unfold tailWord_7636424
  simp only [CollatzResearch.WordTrace]
  refine ⟨139261632443273760115926163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185682176591031680154568217 139261632443273760115926163)
  ·
    refine ⟨208892448664910640173889245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139261632443273760115926163 208892448664910640173889245)
    ·
      refine ⟨78334668249341490065208467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208892448664910640173889245 78334668249341490065208467)
      ·
        refine ⟨117502002374012235097812701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78334668249341490065208467 117502002374012235097812701)
        ·
          refine ⟨44063250890254588161679763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117502002374012235097812701 44063250890254588161679763)
          ·
            refine ⟨66094876335381882242519645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44063250890254588161679763 66094876335381882242519645)
            ·
              refine ⟨24785578625768205840944867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66094876335381882242519645 24785578625768205840944867)
              ·
                refine ⟨37178367938652308761417301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24785578625768205840944867 37178367938652308761417301)
                ·
                  refine ⟨435683999281081743297859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37178367938652308761417301 435683999281081743297859)
                  ·
                    rfl

theorem cell23_7636424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 8].length) (baseStart_7636424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636424 prefixEnd_7636424 := by exact prefixLift 7636424
  have htrace : WordTrace (prefixWord ++ tailWord_7636424) baseStart_7636424 baseEnd_7636424 := by
    simpa [prefixWord, tailWord_7636424, baseEnd_7636424] using wordTrace_append hprefix tailTrace_7636424
  have hstable : (prefixWord ++ tailWord_7636424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636424).length < 2 ^ (prefixWord ++ tailWord_7636424).sum := by decide
  have hdescent : baseEnd_7636424 < baseStart_7636424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636428 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 3, 4]
def baseStart_7636428 : Nat := 118140960795 + 7636428 * 2 ^ 59
def prefixEnd_7636428 : Nat := 4983230072969 + 3 ^ 40 * 7636428 * 2
def baseEnd_7636428 : Nat := 1307052682484117891343571

theorem tailTrace_7636428 : CollatzResearch.WordTrace tailWord_7636428 prefixEnd_7636428 1307052682484117891343571 := by
  unfold tailWord_7636428
  simp only [CollatzResearch.WordTrace]
  refine ⟨139261705389266514457498969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185682273852355352609998625 139261705389266514457498969)
  ·
    refine ⟨104446279041949885843124227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139261705389266514457498969 104446279041949885843124227)
    ·
      refine ⟨156669418562924828764686341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104446279041949885843124227 156669418562924828764686341)
      ·
        refine ⟨29375515980548405393378689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156669418562924828764686341 29375515980548405393378689)
        ·
          refine ⟨22031636985411304045034017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29375515980548405393378689 22031636985411304045034017)
          ·
            refine ⟨16523727739058478033775513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22031636985411304045034017 16523727739058478033775513)
            ·
              refine ⟨12392795804293858525331635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16523727739058478033775513 12392795804293858525331635)
              ·
                refine ⟨18589193706440787787997453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12392795804293858525331635 18589193706440787787997453)
                ·
                  refine ⟨6970947639915295420499045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18589193706440787787997453 6970947639915295420499045)
                  ·
                    refine ⟨1307052682484117891343571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6970947639915295420499045 1307052682484117891343571)
                    ·
                      rfl

theorem cell23_7636428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_7636428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636428 prefixEnd_7636428 := by exact prefixLift 7636428
  have htrace : WordTrace (prefixWord ++ tailWord_7636428) baseStart_7636428 baseEnd_7636428 := by
    simpa [prefixWord, tailWord_7636428, baseEnd_7636428] using wordTrace_append hprefix tailTrace_7636428
  have hstable : (prefixWord ++ tailWord_7636428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636428).length < 2 ^ (prefixWord ++ tailWord_7636428).sum := by decide
  have hdescent : baseEnd_7636428 < baseStart_7636428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636438 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_7636438 : Nat := 118140960795 + 7636438 * 2 ^ 59
def prefixEnd_7636438 : Nat := 4983230072969 + 3 ^ 40 * 7636438 * 2
def baseEnd_7636438 : Nat := 3921163182258898634905667

theorem tailTrace_7636438 : CollatzResearch.WordTrace tailWord_7636438 prefixEnd_7636438 3921163182258898634905667 := by
  unfold tailWord_7636438
  simp only [CollatzResearch.WordTrace]
  refine ⟨17407735969281050038928873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185682517005664533748574645 17407735969281050038928873)
  ·
    refine ⟨13055801976960787529196655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17407735969281050038928873 13055801976960787529196655)
    ·
      refine ⟨19583702965441181293794983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13055801976960787529196655 19583702965441181293794983)
      ·
        refine ⟨29375554448161771940692475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19583702965441181293794983 29375554448161771940692475)
        ·
          refine ⟨44063331672242657911038713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29375554448161771940692475 44063331672242657911038713)
          ·
            refine ⟨33047498754181993433279035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44063331672242657911038713 33047498754181993433279035)
            ·
              refine ⟨49571248131272990149918553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33047498754181993433279035 49571248131272990149918553)
              ·
                refine ⟨37178436098454742612438915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49571248131272990149918553 37178436098454742612438915)
                ·
                  refine ⟨55767654147682113918658373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37178436098454742612438915 55767654147682113918658373)
                  ·
                    refine ⟨10456435152690396359748445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55767654147682113918658373 10456435152690396359748445)
                    ·
                      refine ⟨3921163182258898634905667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10456435152690396359748445 3921163182258898634905667)
                      ·
                        rfl

theorem cell23_7636438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_7636438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636438 prefixEnd_7636438 := by exact prefixLift 7636438
  have htrace : WordTrace (prefixWord ++ tailWord_7636438) baseStart_7636438 baseEnd_7636438 := by
    simpa [prefixWord, tailWord_7636438, baseEnd_7636438] using wordTrace_append hprefix tailTrace_7636438
  have hstable : (prefixWord ++ tailWord_7636438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636438).length < 2 ^ (prefixWord ++ tailWord_7636438).sum := by decide
  have hdescent : baseEnd_7636438 < baseStart_7636438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636558 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3]
def baseStart_7636558 : Nat := 118140960795 + 7636558 * 2 ^ 59
def prefixEnd_7636558 : Nat := 4983230072969 + 3 ^ 40 * 7636558 * 2
def baseEnd_7636558 : Nat := 3921224799937438165405115

theorem tailTrace_7636558 : CollatzResearch.WordTrace tailWord_7636558 prefixEnd_7636558 3921224799937438165405115 := by
  unfold tailWord_7636558
  simp only [CollatzResearch.WordTrace]
  refine ⟨34816019033507757639653791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185685434845374707411486885 34816019033507757639653791)
  ·
    refine ⟨52224028550261636459480687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34816019033507757639653791 52224028550261636459480687)
    ·
      refine ⟨78336042825392454689221031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52224028550261636459480687 78336042825392454689221031)
      ·
        refine ⟨117504064238088682033831547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78336042825392454689221031 117504064238088682033831547)
        ·
          refine ⟨176256096357133023050747321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117504064238088682033831547 176256096357133023050747321)
          ·
            refine ⟨132192072267849767288060491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176256096357133023050747321 132192072267849767288060491)
            ·
              refine ⟨198288108401774650932090737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132192072267849767288060491 198288108401774650932090737)
              ·
                refine ⟨148716081301330988199068053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198288108401774650932090737 148716081301330988199068053)
                ·
                  refine ⟨6971066310999890071831315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148716081301330988199068053 6971066310999890071831315)
                  ·
                    refine ⟨10456599466499835107746973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6971066310999890071831315 10456599466499835107746973)
                    ·
                      refine ⟨3921224799937438165405115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10456599466499835107746973 3921224799937438165405115)
                      ·
                        rfl

theorem cell23_7636558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_7636558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636558 prefixEnd_7636558 := by exact prefixLift 7636558
  have htrace : WordTrace (prefixWord ++ tailWord_7636558) baseStart_7636558 baseEnd_7636558 := by
    simpa [prefixWord, tailWord_7636558, baseEnd_7636558] using wordTrace_append hprefix tailTrace_7636558
  have hstable : (prefixWord ++ tailWord_7636558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636558).length < 2 ^ (prefixWord ++ tailWord_7636558).sum := by decide
  have hdescent : baseEnd_7636558 < baseStart_7636558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636592 : List Nat := [2, 1, 1, 1, 6, 3, 1, 2, 2, 1, 3]
def baseStart_7636592 : Nat := 118140960795 + 7636592 * 2 ^ 59
def prefixEnd_7636592 : Nat := 4983230072969 + 3 ^ 40 * 7636592 * 2
def baseEnd_7636592 : Nat := 3921242258279691032379959

theorem tailTrace_7636592 : CollatzResearch.WordTrace tailWord_7636592 prefixEnd_7636592 3921242258279691032379959 := by
  unfold tailWord_7636592
  simp only [CollatzResearch.WordTrace]
  refine ⟨139264696174969442461984015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185686261566625923282645353 139264696174969442461984015)
  ·
    refine ⟨208897044262454163692976023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139264696174969442461984015 208897044262454163692976023)
    ·
      refine ⟨313345566393681245539464035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208897044262454163692976023 313345566393681245539464035)
      ·
        refine ⟨470018349590521868309196053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313345566393681245539464035 470018349590521868309196053)
        ·
          refine ⟨22032110137055712576993565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 470018349590521868309196053 22032110137055712576993565)
          ·
            refine ⟨8262041301395892216372587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22032110137055712576993565 8262041301395892216372587)
            ·
              refine ⟨12393061952093838324558881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8262041301395892216372587 12393061952093838324558881)
              ·
                refine ⟨9294796464070378743419161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12393061952093838324558881 9294796464070378743419161)
                ·
                  refine ⟨6971097348052784057564371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9294796464070378743419161 6971097348052784057564371)
                  ·
                    refine ⟨10456646022079176086346557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6971097348052784057564371 10456646022079176086346557)
                    ·
                      refine ⟨3921242258279691032379959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10456646022079176086346557 3921242258279691032379959)
                      ·
                        rfl

theorem cell23_7636592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 2, 1, 3].length) (baseStart_7636592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636592 prefixEnd_7636592 := by exact prefixLift 7636592
  have htrace : WordTrace (prefixWord ++ tailWord_7636592) baseStart_7636592 baseEnd_7636592 := by
    simpa [prefixWord, tailWord_7636592, baseEnd_7636592] using wordTrace_append hprefix tailTrace_7636592
  have hstable : (prefixWord ++ tailWord_7636592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636592).length < 2 ^ (prefixWord ++ tailWord_7636592).sum := by decide
  have hdescent : baseEnd_7636592 < baseStart_7636592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636615 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 1, 4, 2]
def baseStart_7636615 : Nat := 118140960795 + 7636615 * 2 ^ 59
def prefixEnd_7636615 : Nat := 4983230072969 + 3 ^ 40 * 7636615 * 2
def baseEnd_7636615 : Nat := 3921254068334744442392353

theorem tailTrace_7636615 : CollatzResearch.WordTrace tailWord_7636615 prefixEnd_7636615 3921254068334744442392353 := by
  unfold tailWord_7636615
  simp only [CollatzResearch.WordTrace]
  refine ⟨278530231228855559852055299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185686820819237039901370199 278530231228855559852055299)
  ·
    refine ⟨417795346843283339778082949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278530231228855559852055299 417795346843283339778082949)
    ·
      refine ⟨78336627533115626208390553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417795346843283339778082949 78336627533115626208390553)
      ·
        refine ⟨58752470649836719656292915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78336627533115626208390553 58752470649836719656292915)
        ·
          refine ⟨88128705974755079484439373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58752470649836719656292915 88128705974755079484439373)
          ·
            refine ⟨33048264740533154806664765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88128705974755079484439373 33048264740533154806664765)
            ·
              refine ⟨12393099277699933052499287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33048264740533154806664765 12393099277699933052499287)
              ·
                refine ⟨18589648916549899578748931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12393099277699933052499287 18589648916549899578748931)
                ·
                  refine ⟨27884473374824849368123397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18589648916549899578748931 27884473374824849368123397)
                  ·
                    refine ⟨5228338757779659256523137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27884473374824849368123397 5228338757779659256523137)
                    ·
                      refine ⟨3921254068334744442392353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5228338757779659256523137 3921254068334744442392353)
                      ·
                        rfl

theorem cell23_7636615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_7636615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636615 prefixEnd_7636615 := by exact prefixLift 7636615
  have htrace : WordTrace (prefixWord ++ tailWord_7636615) baseStart_7636615 baseEnd_7636615 := by
    simpa [prefixWord, tailWord_7636615, baseEnd_7636615] using wordTrace_append hprefix tailTrace_7636615
  have hstable : (prefixWord ++ tailWord_7636615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636615).length < 2 ^ (prefixWord ++ tailWord_7636615).sum := by decide
  have hdescent : baseEnd_7636615 < baseStart_7636615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636655 : List Nat := [1, 1, 2, 1, 2, 4, 5, 2, 5]
def baseStart_7636655 : Nat := 118140960795 + 7636655 * 2 ^ 59
def prefixEnd_7636655 : Nat := 4983230072969 + 3 ^ 40 * 7636655 * 2
def baseEnd_7636655 : Nat := 435697178617880476210241

theorem tailTrace_7636655 : CollatzResearch.WordTrace tailWord_7636655 prefixEnd_7636655 435697178617880476210241 := by
  unfold tailWord_7636655
  simp only [CollatzResearch.WordTrace]
  refine ⟨278531690148710646683511419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185687793432473764455674279 278531690148710646683511419)
  ·
    refine ⟨417797535223065970025267129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278531690148710646683511419 417797535223065970025267129)
    ·
      refine ⟨313348151417299477518950347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417797535223065970025267129 313348151417299477518950347)
      ·
        refine ⟨470022227125949216278425521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313348151417299477518950347 470022227125949216278425521)
        ·
          refine ⟨352516670344461912208819141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470022227125949216278425521 352516670344461912208819141)
          ·
            refine ⟨66096875689586608539153589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352516670344461912208819141 66096875689586608539153589)
            ·
              refine ⟨6196582095898744550545649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66096875689586608539153589 6196582095898744550545649)
              ·
                refine ⟨4647436571924058412909237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6196582095898744550545649 4647436571924058412909237)
                ·
                  refine ⟨435697178617880476210241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4647436571924058412909237 435697178617880476210241)
                  ·
                    rfl

theorem cell23_7636655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 5].length) (baseStart_7636655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636655 prefixEnd_7636655 := by exact prefixLift 7636655
  have htrace : WordTrace (prefixWord ++ tailWord_7636655) baseStart_7636655 baseEnd_7636655 := by
    simpa [prefixWord, tailWord_7636655, baseEnd_7636655] using wordTrace_append hprefix tailTrace_7636655
  have hstable : (prefixWord ++ tailWord_7636655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636655).length < 2 ^ (prefixWord ++ tailWord_7636655).sum := by decide
  have hdescent : baseEnd_7636655 < baseStart_7636655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636688 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 3, 6, 2]
def baseStart_7636688 : Nat := 118140960795 + 7636688 * 2 ^ 59
def prefixEnd_7636688 : Nat := 4983230072969 + 3 ^ 40 * 7636688 * 2
def baseEnd_7636688 : Nat := 3921291552422522656779517

theorem tailTrace_7636688 : CollatzResearch.WordTrace tailWord_7636688 prefixEnd_7636688 3921291552422522656779517 := by
  unfold tailWord_7636688
  simp only [CollatzResearch.WordTrace]
  refine ⟨139266446878795546659731359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185688595838394062212975145 139266446878795546659731359)
  ·
    refine ⟨208899670318193319989597039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139266446878795546659731359 208899670318193319989597039)
    ·
      refine ⟨313349505477289979984395559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208899670318193319989597039 313349505477289979984395559)
      ·
        refine ⟨470024258215934969976593339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313349505477289979984395559 470024258215934969976593339)
        ·
          refine ⟨705036387323902454964890009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470024258215934969976593339 705036387323902454964890009)
          ·
            refine ⟨528777290492926841223667507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705036387323902454964890009 528777290492926841223667507)
            ·
              refine ⟨793165935739390261835501261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528777290492926841223667507 793165935739390261835501261)
              ·
                refine ⟨297437225902271348188312973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 793165935739390261835501261 297437225902271348188312973)
                ·
                  refine ⟨111538959713351755570617365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297437225902271348188312973 111538959713351755570617365)
                  ·
                    refine ⟨5228388736563363542372689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111538959713351755570617365 5228388736563363542372689)
                    ·
                      refine ⟨3921291552422522656779517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5228388736563363542372689 3921291552422522656779517)
                      ·
                        rfl

theorem cell23_7636688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 6, 2].length) (baseStart_7636688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636688 prefixEnd_7636688 := by exact prefixLift 7636688
  have htrace : WordTrace (prefixWord ++ tailWord_7636688) baseStart_7636688 baseEnd_7636688 := by
    simpa [prefixWord, tailWord_7636688, baseEnd_7636688] using wordTrace_append hprefix tailTrace_7636688
  have hstable : (prefixWord ++ tailWord_7636688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636688).length < 2 ^ (prefixWord ++ tailWord_7636688).sum := by decide
  have hdescent : baseEnd_7636688 < baseStart_7636688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636731 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 6]
def baseStart_7636731 : Nat := 118140960795 + 7636731 * 2 ^ 59
def prefixEnd_7636731 : Nat := 4983230072969 + 3 ^ 40 * 7636731 * 2
def baseEnd_7636731 : Nat := 3921313632090665988541819

theorem tailTrace_7636731 : CollatzResearch.WordTrace tailWord_7636731 prefixEnd_7636731 3921313632090665988541819 := by
  unfold tailWord_7636731
  simp only [CollatzResearch.WordTrace]
  refine ⟨278534462096435311663278047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185689641397623541108852031 278534462096435311663278047)
  ·
    refine ⟨417801693144652967494917071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278534462096435311663278047 417801693144652967494917071)
    ·
      refine ⟨626702539716979451242375607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417801693144652967494917071 626702539716979451242375607)
      ·
        refine ⟨940053809575469176863563411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626702539716979451242375607 940053809575469176863563411)
        ·
          refine ⟨1410080714363203765295345117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940053809575469176863563411 1410080714363203765295345117)
          ·
            refine ⟨528780267886201411985754419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1410080714363203765295345117 528780267886201411985754419)
            ·
              refine ⟨793170401829302117978631629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528780267886201411985754419 793170401829302117978631629)
              ·
                refine ⟨297438900685988294241986861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 793170401829302117978631629 297438900685988294241986861)
                ·
                  refine ⟨111539587757245610340745073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297438900685988294241986861 111539587757245610340745073)
                  ·
                    refine ⟨83654690817934207755558805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111539587757245610340745073 83654690817934207755558805)
                    ·
                      refine ⟨3921313632090665988541819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83654690817934207755558805 3921313632090665988541819)
                      ·
                        rfl

theorem cell23_7636731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 6].length) (baseStart_7636731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636731 prefixEnd_7636731 := by exact prefixLift 7636731
  have htrace : WordTrace (prefixWord ++ tailWord_7636731) baseStart_7636731 baseEnd_7636731 := by
    simpa [prefixWord, tailWord_7636731, baseEnd_7636731] using wordTrace_append hprefix tailTrace_7636731
  have hstable : (prefixWord ++ tailWord_7636731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636731).length < 2 ^ (prefixWord ++ tailWord_7636731).sum := by decide
  have hdescent : baseEnd_7636731 < baseStart_7636731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636766 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_7636766 : Nat := 118140960795 + 7636766 * 2 ^ 59
def prefixEnd_7636766 : Nat := 4983230072969 + 3 ^ 40 * 7636766 * 2
def baseEnd_7636766 : Nat := 1307110534637857783868053

theorem tailTrace_7636766 : CollatzResearch.WordTrace tailWord_7636766 prefixEnd_7636766 1307110534637857783868053 := by
  unfold tailWord_7636766
  simp only [CollatzResearch.WordTrace]
  refine ⟨34816967331413564080100269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185690492434205675093868101 34816967331413564080100269)
  ·
    refine ⟨13056362749280086530037601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34816967331413564080100269 13056362749280086530037601)
    ·
      refine ⟨9792272061960064897528201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13056362749280086530037601 9792272061960064897528201)
      ·
        refine ⟨7344204046470048673146151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9792272061960064897528201 7344204046470048673146151)
        ·
          refine ⟨11016306069705073009719227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7344204046470048673146151 11016306069705073009719227)
          ·
            refine ⟨16524459104557609514578841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11016306069705073009719227 16524459104557609514578841)
            ·
              refine ⟨12393344328418207135934131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16524459104557609514578841 12393344328418207135934131)
              ·
                refine ⟨18590016492627310703901197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12393344328418207135934131 18590016492627310703901197)
                ·
                  refine ⟨6971256184735241513962949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18590016492627310703901197 6971256184735241513962949)
                  ·
                    refine ⟨1307110534637857783868053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6971256184735241513962949 1307110534637857783868053)
                    ·
                      rfl

theorem cell23_7636766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_7636766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636766 prefixEnd_7636766 := by exact prefixLift 7636766
  have htrace : WordTrace (prefixWord ++ tailWord_7636766) baseStart_7636766 baseEnd_7636766 := by
    simpa [prefixWord, tailWord_7636766, baseEnd_7636766] using wordTrace_append hprefix tailTrace_7636766
  have hstable : (prefixWord ++ tailWord_7636766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636766).length < 2 ^ (prefixWord ++ tailWord_7636766).sum := by decide
  have hdescent : baseEnd_7636766 < baseStart_7636766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636772 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 3, 1, 3]
def baseStart_7636772 : Nat := 118140960795 + 7636772 * 2 ^ 59
def prefixEnd_7636772 : Nat := 4983230072969 + 3 ^ 40 * 7636772 * 2
def baseEnd_7636772 : Nat := 3921334684797500328129131

theorem tailTrace_7636772 : CollatzResearch.WordTrace tailWord_7636772 prefixEnd_7636772 3921334684797500328129131 := by
  unfold tailWord_7636772
  simp only [CollatzResearch.WordTrace]
  refine ⟨139267978744643387832760285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185690638326191183777013713 139267978744643387832760285)
  ·
    refine ⟨52225492029241270437285107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139267978744643387832760285 52225492029241270437285107)
    ·
      refine ⟨78338238043861905655927661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52225492029241270437285107 78338238043861905655927661)
      ·
        refine ⟨29376839266448214620972873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78338238043861905655927661 29376839266448214620972873)
        ·
          refine ⟨22032629449836160965729655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29376839266448214620972873 22032629449836160965729655)
          ·
            refine ⟨33048944174754241448594483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22032629449836160965729655 33048944174754241448594483)
            ·
              refine ⟨49573416262131362172891725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33048944174754241448594483 49573416262131362172891725)
              ·
                refine ⟨18590031098299260814834397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49573416262131362172891725 18590031098299260814834397)
                ·
                  refine ⟨6971261661862222805562899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18590031098299260814834397 6971261661862222805562899)
                  ·
                    refine ⟨10456892492793334208344349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6971261661862222805562899 10456892492793334208344349)
                    ·
                      refine ⟨3921334684797500328129131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10456892492793334208344349 3921334684797500328129131)
                      ·
                        rfl

theorem cell23_7636772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_7636772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636772 prefixEnd_7636772 := by exact prefixLift 7636772
  have htrace : WordTrace (prefixWord ++ tailWord_7636772) baseStart_7636772 baseEnd_7636772 := by
    simpa [prefixWord, tailWord_7636772, baseEnd_7636772] using wordTrace_append hprefix tailTrace_7636772
  have hstable : (prefixWord ++ tailWord_7636772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636772).length < 2 ^ (prefixWord ++ tailWord_7636772).sum := by decide
  have hdescent : baseEnd_7636772 < baseStart_7636772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636818 : List Nat := [3, 2, 2, 1, 1, 3, 11]
def baseStart_7636818 : Nat := 118140960795 + 7636818 * 2 ^ 59
def prefixEnd_7636818 : Nat := 4983230072969 + 3 ^ 40 * 7636818 * 2
def baseEnd_7636818 : Nat := 48411830924785273433999

theorem tailTrace_7636818 : CollatzResearch.WordTrace tailWord_7636818 prefixEnd_7636818 48411830924785273433999 := by
  unfold tailWord_7636818
  simp only [CollatzResearch.WordTrace]
  refine ⟨69634408811780031380423777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185691756831413417014463405 69634408811780031380423777)
  ·
    refine ⟨52225806608835023535317833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69634408811780031380423777 52225806608835023535317833)
    ·
      refine ⟨39169354956626267651488375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52225806608835023535317833 39169354956626267651488375)
      ·
        refine ⟨58754032434939401477232563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39169354956626267651488375 58754032434939401477232563)
        ·
          refine ⟨88131048652409102215848845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58754032434939401477232563 88131048652409102215848845)
          ·
            refine ⟨33049143244653413330943317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88131048652409102215848845 33049143244653413330943317)
            ·
              refine ⟨48411830924785273433999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33049143244653413330943317 48411830924785273433999)
              ·
                rfl

theorem cell23_7636818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 11].length) (baseStart_7636818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636818 prefixEnd_7636818 := by exact prefixLift 7636818
  have htrace : WordTrace (prefixWord ++ tailWord_7636818) baseStart_7636818 baseEnd_7636818 := by
    simpa [prefixWord, tailWord_7636818, baseEnd_7636818] using wordTrace_append hprefix tailTrace_7636818
  have hstable : (prefixWord ++ tailWord_7636818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636818).length < 2 ^ (prefixWord ++ tailWord_7636818).sum := by decide
  have hdescent : baseEnd_7636818 < baseStart_7636818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636835 : List Nat := [1, 1, 1, 5, 4, 1, 2, 8]
def baseStart_7636835 : Nat := 118140960795 + 7636835 * 2 ^ 59
def prefixEnd_7636835 : Nat := 4983230072969 + 3 ^ 40 * 7636835 * 2
def baseEnd_7636835 : Nat := 145235816076990132653383

theorem tailTrace_7636835 : CollatzResearch.WordTrace tailWord_7636835 prefixEnd_7636835 145235816076990132653383 := by
  unfold tailWord_7636835
  simp only [CollatzResearch.WordTrace]
  refine ⟨278538255288058537425063959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185692170192039024950042639 278538255288058537425063959)
  ·
    refine ⟨417807382932087806137595939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278538255288058537425063959 417807382932087806137595939)
    ·
      refine ⟨626711074398131709206393909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417807382932087806137595939 626711074398131709206393909)
      ·
        refine ⟨58754163224824847738099429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 626711074398131709206393909 58754163224824847738099429)
        ·
          refine ⟨11016405604654658950893643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58754163224824847738099429 11016405604654658950893643)
          ·
            refine ⟨16524608406981988426340465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11016405604654658950893643 16524608406981988426340465)
            ·
              refine ⟨12393456305236491319755349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16524608406981988426340465 12393456305236491319755349)
              ·
                refine ⟨145235816076990132653383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12393456305236491319755349 145235816076990132653383)
                ·
                  rfl

theorem cell23_7636835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 8].length) (baseStart_7636835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636835 prefixEnd_7636835 := by exact prefixLift 7636835
  have htrace : WordTrace (prefixWord ++ tailWord_7636835) baseStart_7636835 baseEnd_7636835 := by
    simpa [prefixWord, tailWord_7636835, baseEnd_7636835] using wordTrace_append hprefix tailTrace_7636835
  have hstable : (prefixWord ++ tailWord_7636835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636835).length < 2 ^ (prefixWord ++ tailWord_7636835).sum := by decide
  have hdescent : baseEnd_7636835 < baseStart_7636835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636858 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_7636858 : Nat := 118140960795 + 7636858 * 2 ^ 59
def prefixEnd_7636858 : Nat := 4983230072969 + 3 ^ 40 * 7636858 * 2
def baseEnd_7636858 : Nat := 3921378844133786991653735

theorem tailTrace_7636858 : CollatzResearch.WordTrace tailWord_7636858 prefixEnd_7636858 3921378844133786991653735 := by
  unfold tailWord_7636858
  simp only [CollatzResearch.WordTrace]
  refine ⟨69634773541743803088287807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185692729444650141568767485 69634773541743803088287807)
  ·
    refine ⟨104452160312615704632431711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69634773541743803088287807 104452160312615704632431711)
    ·
      refine ⟨156678240468923556948647567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104452160312615704632431711 156678240468923556948647567)
      ·
        refine ⟨235017360703385335422971351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156678240468923556948647567 235017360703385335422971351)
        ·
          refine ⟨352526041055078003134457027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235017360703385335422971351 352526041055078003134457027)
          ·
            refine ⟨528789061582617004701685541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352526041055078003134457027 528789061582617004701685541)
            ·
              refine ⟨99147949046740688381566039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 528789061582617004701685541 99147949046740688381566039)
              ·
                refine ⟨148721923570111032572349059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99147949046740688381566039 148721923570111032572349059)
                ·
                  refine ⟨223082885355166548858523589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148721923570111032572349059 223082885355166548858523589)
                  ·
                    refine ⟨41828041004093727910973173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 223082885355166548858523589 41828041004093727910973173)
                    ·
                      refine ⟨3921378844133786991653735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41828041004093727910973173 3921378844133786991653735)
                      ·
                        rfl

theorem cell23_7636858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_7636858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636858 prefixEnd_7636858 := by exact prefixLift 7636858
  have htrace : WordTrace (prefixWord ++ tailWord_7636858) baseStart_7636858 baseEnd_7636858 := by
    simpa [prefixWord, tailWord_7636858, baseEnd_7636858] using wordTrace_append hprefix tailTrace_7636858
  have hstable : (prefixWord ++ tailWord_7636858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636858).length < 2 ^ (prefixWord ++ tailWord_7636858).sum := by decide
  have hdescent : baseEnd_7636858 < baseStart_7636858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636886 : List Nat := [5, 3, 1, 1, 2, 2, 1, 8]
def baseStart_7636886 : Nat := 118140960795 + 7636886 * 2 ^ 59
def prefixEnd_7636886 : Nat := 4983230072969 + 3 ^ 40 * 7636886 * 2
def baseEnd_7636886 : Nat := 145236785984893069707541

theorem tailTrace_7636886 : CollatzResearch.WordTrace tailWord_7636886 prefixEnd_7636886 145236785984893069707541 := by
  unfold tailWord_7636886
  simp only [CollatzResearch.WordTrace]
  refine ⟨17408757213179610820948157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185693410273915848756780341 17408757213179610820948157)
  ·
    refine ⟨6528283954942354057855559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17408757213179610820948157 6528283954942354057855559)
    ·
      refine ⟨9792425932413531086783339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6528283954942354057855559 9792425932413531086783339)
      ·
        refine ⟨14688638898620296630175009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9792425932413531086783339 14688638898620296630175009)
        ·
          refine ⟨11016479173965222472631257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14688638898620296630175009 11016479173965222472631257)
          ·
            refine ⟨8262359380473916854473443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11016479173965222472631257 8262359380473916854473443)
            ·
              refine ⟨12393539070710875281710165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8262359380473916854473443 12393539070710875281710165)
              ·
                refine ⟨145236785984893069707541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12393539070710875281710165 145236785984893069707541)
                ·
                  rfl

theorem cell23_7636886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_7636886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636886 prefixEnd_7636886 := by exact prefixLift 7636886
  have htrace : WordTrace (prefixWord ++ tailWord_7636886) baseStart_7636886 baseEnd_7636886 := by
    simpa [prefixWord, tailWord_7636886, baseEnd_7636886] using wordTrace_append hprefix tailTrace_7636886
  have hstable : (prefixWord ++ tailWord_7636886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636886).length < 2 ^ (prefixWord ++ tailWord_7636886).sum := by decide
  have hdescent : baseEnd_7636886 < baseStart_7636886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636936 : List Nat := [2, 1, 3, 1, 4, 1, 3, 2, 2, 2, 2]
def baseStart_7636936 : Nat := 118140960795 + 7636936 * 2 ^ 59
def prefixEnd_7636936 : Nat := 4983230072969 + 3 ^ 40 * 7636936 * 2
def baseEnd_7636936 : Nat := 3921418895624837686478377

theorem tailTrace_7636936 : CollatzResearch.WordTrace tailWord_7636936 prefixEnd_7636936 3921418895624837686478377 := by
  unfold tailWord_7636936
  simp only [CollatzResearch.WordTrace]
  refine ⟨139270969530346315837245331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185694626040461754449660441 139270969530346315837245331)
  ·
    refine ⟨208906454295519473755867997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139270969530346315837245331 208906454295519473755867997)
    ·
      refine ⟨78339920360819802658450499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208906454295519473755867997 78339920360819802658450499)
      ·
        refine ⟨117509880541229703987675749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78339920360819802658450499 117509880541229703987675749)
        ·
          refine ⟨22033102601480569497689203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117509880541229703987675749 22033102601480569497689203)
          ·
            refine ⟨33049653902220854246533805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22033102601480569497689203 33049653902220854246533805)
            ·
              refine ⟨12393620213332820342450177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33049653902220854246533805 12393620213332820342450177)
              ·
                refine ⟨9295215159999615256837633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12393620213332820342450177 9295215159999615256837633)
                ·
                  refine ⟨6971411369999711442628225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9295215159999615256837633 6971411369999711442628225)
                  ·
                    refine ⟨5228558527499783581971169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6971411369999711442628225 5228558527499783581971169)
                    ·
                      refine ⟨3921418895624837686478377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5228558527499783581971169 3921418895624837686478377)
                      ·
                        rfl

theorem cell23_7636936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_7636936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636936 prefixEnd_7636936 := by exact prefixLift 7636936
  have htrace : WordTrace (prefixWord ++ tailWord_7636936) baseStart_7636936 baseEnd_7636936 := by
    simpa [prefixWord, tailWord_7636936, baseEnd_7636936] using wordTrace_append hprefix tailTrace_7636936
  have hstable : (prefixWord ++ tailWord_7636936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636936).length < 2 ^ (prefixWord ++ tailWord_7636936).sum := by decide
  have hdescent : baseEnd_7636936 < baseStart_7636936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636942 : List Nat := [4, 1, 1, 1, 2, 2, 1, 6, 5]
def baseStart_7636942 : Nat := 118140960795 + 7636942 * 2 ^ 59
def prefixEnd_7636942 : Nat := 4983230072969 + 3 ^ 40 * 7636942 * 2
def baseEnd_7636942 : Nat := 435713552945418295889261

theorem tailTrace_7636942 : CollatzResearch.WordTrace tailWord_7636942 prefixEnd_7636942 435713552945418295889261 := by
  unfold tailWord_7636942
  simp only [CollatzResearch.WordTrace]
  refine ⟨34817769737333861837401135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185694771932447263132806053 34817769737333861837401135)
  ·
    refine ⟨52226654606000792756101703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34817769737333861837401135 52226654606000792756101703)
    ·
      refine ⟨78339981909001189134152555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52226654606000792756101703 78339981909001189134152555)
      ·
        refine ⟨117509972863501783701228833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78339981909001189134152555 117509972863501783701228833)
        ·
          refine ⟨88132479647626337775921625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117509972863501783701228833 88132479647626337775921625)
          ·
            refine ⟨66099359735719753331941219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88132479647626337775921625 66099359735719753331941219)
            ·
              refine ⟨99149039603579629997911829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66099359735719753331941219 99149039603579629997911829)
              ·
                refine ⟨4647611231417795156152117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99149039603579629997911829 4647611231417795156152117)
                ·
                  refine ⟨435713552945418295889261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4647611231417795156152117 435713552945418295889261)
                  ·
                    rfl

theorem cell23_7636942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_7636942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636942 prefixEnd_7636942 := by exact prefixLift 7636942
  have htrace : WordTrace (prefixWord ++ tailWord_7636942) baseStart_7636942 baseEnd_7636942 := by
    simpa [prefixWord, tailWord_7636942, baseEnd_7636942] using wordTrace_append hprefix tailTrace_7636942
  have hstable : (prefixWord ++ tailWord_7636942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636942).length < 2 ^ (prefixWord ++ tailWord_7636942).sum := by decide
  have hdescent : baseEnd_7636942 < baseStart_7636942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636953 : List Nat := [1, 2, 1, 2, 6, 1, 3, 1, 2, 2, 2]
def baseStart_7636953 : Nat := 118140960795 + 7636953 * 2 ^ 59
def prefixEnd_7636953 : Nat := 4983230072969 + 3 ^ 40 * 7636953 * 2
def baseEnd_7636953 : Nat := 3921427624795964119965799

theorem tailTrace_7636953 : CollatzResearch.WordTrace tailWord_7636953 prefixEnd_7636953 3921427624795964119965799 := by
  unfold tailWord_7636953
  simp only [CollatzResearch.WordTrace]
  refine ⟨278542559101631043577859513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185695039401087362385239675 278542559101631043577859513)
  ·
    refine ⟨208906919326223282683394635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278542559101631043577859513 208906919326223282683394635)
    ·
      refine ⟨313360378989334924025091953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208906919326223282683394635 313360378989334924025091953)
      ·
        refine ⟨235020284242001193018818965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313360378989334924025091953 235020284242001193018818965)
        ·
          refine ⟨11016575823843805922757139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235020284242001193018818965 11016575823843805922757139)
          ·
            refine ⟨16524863735765708884135709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11016575823843805922757139 16524863735765708884135709)
            ·
              refine ⟨6196823900912140831550891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16524863735765708884135709 6196823900912140831550891)
              ·
                refine ⟨9295235851368211247326337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6196823900912140831550891 9295235851368211247326337)
                ·
                  refine ⟨6971426888526158435494753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9295235851368211247326337 6971426888526158435494753)
                  ·
                    refine ⟨5228570166394618826621065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6971426888526158435494753 5228570166394618826621065)
                    ·
                      refine ⟨3921427624795964119965799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5228570166394618826621065 3921427624795964119965799)
                      ·
                        rfl

theorem cell23_7636953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 2, 2, 2].length) (baseStart_7636953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636953 prefixEnd_7636953 := by exact prefixLift 7636953
  have htrace : WordTrace (prefixWord ++ tailWord_7636953) baseStart_7636953 baseEnd_7636953 := by
    simpa [prefixWord, tailWord_7636953, baseEnd_7636953] using wordTrace_append hprefix tailTrace_7636953
  have hstable : (prefixWord ++ tailWord_7636953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636953).length < 2 ^ (prefixWord ++ tailWord_7636953).sum := by decide
  have hdescent : baseEnd_7636953 < baseStart_7636953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636975 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 4]
def baseStart_7636975 : Nat := 118140960795 + 7636975 * 2 ^ 59
def prefixEnd_7636975 : Nat := 4983230072969 + 3 ^ 40 * 7636975 * 2
def baseEnd_7636975 : Nat := 3921438921370363033890697

theorem tailTrace_7636975 : CollatzResearch.WordTrace tailWord_7636975 prefixEnd_7636975 3921438921370363033890697 := by
  unfold tailWord_7636975
  simp only [CollatzResearch.WordTrace]
  refine ⟨278543361507551341335160379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185695574338367560890106919 278543361507551341335160379)
  ·
    refine ⟨417815042261327012002740569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278543361507551341335160379 417815042261327012002740569)
    ·
      refine ⟨313361281695995259002055427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417815042261327012002740569 313361281695995259002055427)
      ·
        refine ⟨470041922543992888503083141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313361281695995259002055427 470041922543992888503083141)
        ·
          refine ⟨88132860476998666594328089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 470041922543992888503083141 88132860476998666594328089)
          ·
            refine ⟨66099645357748999945746067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88132860476998666594328089 66099645357748999945746067)
            ·
              refine ⟨99149468036623499918619101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66099645357748999945746067 99149468036623499918619101)
              ·
                refine ⟨37181050513733812469482163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99149468036623499918619101 37181050513733812469482163)
                ·
                  refine ⟨55771575770600718704223245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37181050513733812469482163 55771575770600718704223245)
                  ·
                    refine ⟨20914340913975269514083717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55771575770600718704223245 20914340913975269514083717)
                    ·
                      refine ⟨3921438921370363033890697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20914340913975269514083717 3921438921370363033890697)
                      ·
                        rfl

theorem cell23_7636975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_7636975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636975 prefixEnd_7636975 := by exact prefixLift 7636975
  have htrace : WordTrace (prefixWord ++ tailWord_7636975) baseStart_7636975 baseEnd_7636975 := by
    simpa [prefixWord, tailWord_7636975, baseEnd_7636975] using wordTrace_append hprefix tailTrace_7636975
  have hstable : (prefixWord ++ tailWord_7636975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636975).length < 2 ^ (prefixWord ++ tailWord_7636975).sum := by decide
  have hdescent : baseEnd_7636975 < baseStart_7636975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7636992 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 2, 4, 2]
def baseStart_7636992 : Nat := 118140960795 + 7636992 * 2 ^ 59
def prefixEnd_7636992 : Nat := 4983230072969 + 3 ^ 40 * 7636992 * 2
def baseEnd_7636992 : Nat := 3921447650541489467378119

theorem tailTrace_7636992 : CollatzResearch.WordTrace tailWord_7636992 prefixEnd_7636992 3921447650541489467378119 := by
  unfold tailWord_7636992
  simp only [CollatzResearch.WordTrace]
  refine ⟨139271990774244876619264615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185695987698993168825686153 139271990774244876619264615)
  ·
    refine ⟨208907986161367314928896923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139271990774244876619264615 208907986161367314928896923)
    ·
      refine ⟨313361979242050972393345385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208907986161367314928896923 313361979242050972393345385)
      ·
        refine ⟨235021484431538229295009039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313361979242050972393345385 235021484431538229295009039)
        ·
          refine ⟨352532226647307343942513559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235021484431538229295009039 352532226647307343942513559)
          ·
            refine ⟨528798339970961015913770339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352532226647307343942513559 528798339970961015913770339)
            ·
              refine ⟨793197509956441523870655509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528798339970961015913770339 793197509956441523870655509)
              ·
                refine ⟨37181133279208196431436977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 793197509956441523870655509 37181133279208196431436977)
                ·
                  refine ⟨27885849959406147323577733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37181133279208196431436977 27885849959406147323577733)
                  ·
                    refine ⟨5228596867388652623170825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27885849959406147323577733 5228596867388652623170825)
                    ·
                      refine ⟨3921447650541489467378119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5228596867388652623170825 3921447650541489467378119)
                      ·
                        rfl

theorem cell23_7636992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2, 4, 2].length) (baseStart_7636992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7636992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7636992 prefixEnd_7636992 := by exact prefixLift 7636992
  have htrace : WordTrace (prefixWord ++ tailWord_7636992) baseStart_7636992 baseEnd_7636992 := by
    simpa [prefixWord, tailWord_7636992, baseEnd_7636992] using wordTrace_append hprefix tailTrace_7636992
  have hstable : (prefixWord ++ tailWord_7636992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7636992).length < 2 ^ (prefixWord ++ tailWord_7636992).sum := by decide
  have hdescent : baseEnd_7636992 < baseStart_7636992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7636992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637029 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 2, 2, 3]
def baseStart_7637029 : Nat := 118140960795 + 7637029 * 2 ^ 59
def prefixEnd_7637029 : Nat := 4983230072969 + 3 ^ 40 * 7637029 * 2
def baseEnd_7637029 : Nat := 3921466649325705822615449

theorem tailTrace_7637029 : CollatzResearch.WordTrace tailWord_7637029 prefixEnd_7637029 3921466649325705822615449 := by
  unfold tailWord_7637029
  simp only [CollatzResearch.WordTrace]
  refine ⟨278545331049355708557626141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185696887366237139038417427 278545331049355708557626141)
  ·
    refine ⟨104454499143508390709109803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278545331049355708557626141 104454499143508390709109803)
    ·
      refine ⟨156681748715262586063664705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104454499143508390709109803 156681748715262586063664705)
      ·
        refine ⟨117511311536446939547748529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156681748715262586063664705 117511311536446939547748529)
        ·
          refine ⟨88133483652335204660811397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117511311536446939547748529 88133483652335204660811397)
          ·
            refine ⟨16525028184812850873902137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88133483652335204660811397 16525028184812850873902137)
            ·
              refine ⟨12393771138609638155426603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16525028184812850873902137 12393771138609638155426603)
              ·
                refine ⟨18590656707914457233139905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12393771138609638155426603 18590656707914457233139905)
                ·
                  refine ⟨13942992530935842924854929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18590656707914457233139905 13942992530935842924854929)
                  ·
                    refine ⟨10457244398201882193641197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13942992530935842924854929 10457244398201882193641197)
                    ·
                      refine ⟨3921466649325705822615449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10457244398201882193641197 3921466649325705822615449)
                      ·
                        rfl

theorem cell23_7637029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_7637029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637029 prefixEnd_7637029 := by exact prefixLift 7637029
  have htrace : WordTrace (prefixWord ++ tailWord_7637029) baseStart_7637029 baseEnd_7637029 := by
    simpa [prefixWord, tailWord_7637029, baseEnd_7637029] using wordTrace_append hprefix tailTrace_7637029
  have hstable : (prefixWord ++ tailWord_7637029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637029).length < 2 ^ (prefixWord ++ tailWord_7637029).sum := by decide
  have hdescent : baseEnd_7637029 < baseStart_7637029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637049 : List Nat := [1, 2, 1, 5, 3, 1, 2, 2, 6]
def baseStart_7637049 : Nat := 118140960795 + 7637049 * 2 ^ 59
def prefixEnd_7637049 : Nat := 4983230072969 + 3 ^ 40 * 7637049 * 2
def baseEnd_7637049 : Nat := 435719657659866193818373

theorem tailTrace_7637049 : CollatzResearch.WordTrace tailWord_7637049 prefixEnd_7637049 435719657659866193818373 := by
  unfold tailWord_7637049
  simp only [CollatzResearch.WordTrace]
  refine ⟨278546060509283251973354201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185697373672855501315569467 278546060509283251973354201)
  ·
    refine ⟨208909545381962438980015651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278546060509283251973354201 208909545381962438980015651)
    ·
      refine ⟨313364318072943658470023477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208909545381962438980015651 313364318072943658470023477)
      ·
        refine ⟨29377904819338467981564701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 313364318072943658470023477 29377904819338467981564701)
        ·
          refine ⟨11016714307251925493086763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29377904819338467981564701 11016714307251925493086763)
          ·
            refine ⟨16525071460877888239630145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11016714307251925493086763 16525071460877888239630145)
            ·
              refine ⟨12393803595658416179722609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16525071460877888239630145 12393803595658416179722609)
              ·
                refine ⟨9295352696743812134791957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12393803595658416179722609 9295352696743812134791957)
                ·
                  refine ⟨435719657659866193818373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9295352696743812134791957 435719657659866193818373)
                  ·
                    rfl

theorem cell23_7637049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 6].length) (baseStart_7637049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637049 prefixEnd_7637049 := by exact prefixLift 7637049
  have htrace : WordTrace (prefixWord ++ tailWord_7637049) baseStart_7637049 baseEnd_7637049 := by
    simpa [prefixWord, tailWord_7637049, baseEnd_7637049] using wordTrace_append hprefix tailTrace_7637049
  have hstable : (prefixWord ++ tailWord_7637049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637049).length < 2 ^ (prefixWord ++ tailWord_7637049).sum := by decide
  have hdescent : baseEnd_7637049 < baseStart_7637049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637082 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4]
def baseStart_7637082 : Nat := 118140960795 + 7637082 * 2 ^ 59
def prefixEnd_7637082 : Nat := 4983230072969 + 3 ^ 40 * 7637082 * 2
def baseEnd_7637082 : Nat := 3921493863800394115252705

theorem tailTrace_7637082 : CollatzResearch.WordTrace tailWord_7637082 prefixEnd_7637082 3921493863800394115252705 := by
  unfold tailWord_7637082
  simp only [CollatzResearch.WordTrace]
  refine ⟨69636816029540924652326375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185698176078775799072870333 69636816029540924652326375)
  ·
    refine ⟨104455224044311386978489563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69636816029540924652326375 104455224044311386978489563)
    ·
      refine ⟨156682836066467080467734345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104455224044311386978489563 156682836066467080467734345)
      ·
        refine ⟨117512127049850310350800759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156682836066467080467734345 117512127049850310350800759)
        ·
          refine ⟨176268190574775465526201139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117512127049850310350800759 176268190574775465526201139)
          ·
            refine ⟨264402285862163198289301709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176268190574775465526201139 264402285862163198289301709)
            ·
              refine ⟨99150857198311199358488141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264402285862163198289301709 99150857198311199358488141)
              ·
                refine ⟨37181571449366699759433053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99150857198311199358488141 37181571449366699759433053)
                ·
                  refine ⟨13943089293512512409787395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37181571449366699759433053 13943089293512512409787395)
                  ·
                    refine ⟨20914633940268768614681093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13943089293512512409787395 20914633940268768614681093)
                    ·
                      refine ⟨3921493863800394115252705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20914633940268768614681093 3921493863800394115252705)
                      ·
                        rfl

theorem cell23_7637082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_7637082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637082 prefixEnd_7637082 := by exact prefixLift 7637082
  have htrace : WordTrace (prefixWord ++ tailWord_7637082) baseStart_7637082 baseEnd_7637082 := by
    simpa [prefixWord, tailWord_7637082, baseEnd_7637082] using wordTrace_append hprefix tailTrace_7637082
  have hstable : (prefixWord ++ tailWord_7637082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637082).length < 2 ^ (prefixWord ++ tailWord_7637082).sum := by decide
  have hdescent : baseEnd_7637082 < baseStart_7637082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637092 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_7637092 : Nat := 118140960795 + 7637092 * 2 ^ 59
def prefixEnd_7637092 : Nat := 4983230072969 + 3 ^ 40 * 7637092 * 2
def baseEnd_7637092 : Nat := 1307166332868979692042553

theorem tailTrace_7637092 : CollatzResearch.WordTrace tailWord_7637092 prefixEnd_7637092 1307166332868979692042553 := by
  unfold tailWord_7637092
  simp only [CollatzResearch.WordTrace]
  refine ⟨139273814424063735158584765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185698419232084980211446353 139273814424063735158584765)
  ·
    refine ⟨52227680409023900684469287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139273814424063735158584765 52227680409023900684469287)
    ·
      refine ⟨78341520613535851026703931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52227680409023900684469287 78341520613535851026703931)
      ·
        refine ⟨117512280920303776540055897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78341520613535851026703931 117512280920303776540055897)
        ·
          refine ⟨88134210690227832405041923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117512280920303776540055897 88134210690227832405041923)
          ·
            refine ⟨132201316035341748607562885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88134210690227832405041923 132201316035341748607562885)
            ·
              refine ⟨24787746756626577863918041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132201316035341748607562885 24787746756626577863918041)
              ·
                refine ⟨18590810067469933397938531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24787746756626577863918041 18590810067469933397938531)
                ·
                  refine ⟨27886215101204900096907797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18590810067469933397938531 27886215101204900096907797)
                  ·
                    refine ⟨1307166332868979692042553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27886215101204900096907797 1307166332868979692042553)
                    ·
                      rfl

theorem cell23_7637092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_7637092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637092 prefixEnd_7637092 := by exact prefixLift 7637092
  have htrace : WordTrace (prefixWord ++ tailWord_7637092) baseStart_7637092 baseEnd_7637092 := by
    simpa [prefixWord, tailWord_7637092, baseEnd_7637092] using wordTrace_append hprefix tailTrace_7637092
  have hstable : (prefixWord ++ tailWord_7637092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637092).length < 2 ^ (prefixWord ++ tailWord_7637092).sum := by decide
  have hdescent : baseEnd_7637092 < baseStart_7637092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637093 : List Nat := [1, 3, 1, 3, 2, 3, 2, 3, 1, 1, 3]
def baseStart_7637093 : Nat := 118140960795 + 7637093 * 2 ^ 59
def prefixEnd_7637093 : Nat := 4983230072969 + 3 ^ 40 * 7637093 * 2
def baseEnd_7637093 : Nat := 3921499512087593572215155

theorem tailTrace_7637093 : CollatzResearch.WordTrace tailWord_7637093 prefixEnd_7637093 3921499512087593572215155 := by
  unfold tailWord_7637093
  simp only [CollatzResearch.WordTrace]
  refine ⟨278547665321123847487955933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185698443547415898325303955 278547665321123847487955933)
  ·
    refine ⟨104455374495421442807983475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278547665321123847487955933 104455374495421442807983475)
    ·
      refine ⟨156683061743132164211975213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104455374495421442807983475 156683061743132164211975213)
      ·
        refine ⟨58756148153674561579490705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156683061743132164211975213 58756148153674561579490705)
        ·
          refine ⟨44067111115255921184618029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58756148153674561579490705 44067111115255921184618029)
          ·
            refine ⟨16525166668220970444231761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44067111115255921184618029 16525166668220970444231761)
            ·
              refine ⟨12393875001165727833173821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16525166668220970444231761 12393875001165727833173821)
              ·
                refine ⟨4647703125437147937440183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12393875001165727833173821 4647703125437147937440183)
                ·
                  refine ⟨6971554688155721906160275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4647703125437147937440183 6971554688155721906160275)
                  ·
                    refine ⟨10457332032233582859240413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6971554688155721906160275 10457332032233582859240413)
                    ·
                      refine ⟨3921499512087593572215155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10457332032233582859240413 3921499512087593572215155)
                      ·
                        rfl

theorem cell23_7637093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_7637093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637093 prefixEnd_7637093 := by exact prefixLift 7637093
  have htrace : WordTrace (prefixWord ++ tailWord_7637093) baseStart_7637093 baseEnd_7637093 := by
    simpa [prefixWord, tailWord_7637093, baseEnd_7637093] using wordTrace_append hprefix tailTrace_7637093
  have hstable : (prefixWord ++ tailWord_7637093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637093).length < 2 ^ (prefixWord ++ tailWord_7637093).sum := by decide
  have hdescent : baseEnd_7637093 < baseStart_7637093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637105 : List Nat := [1, 2, 2, 2, 1, 1, 14]
def baseStart_7637105 : Nat := 118140960795 + 7637105 * 2 ^ 59
def prefixEnd_7637105 : Nat := 4983230072969 + 3 ^ 40 * 7637105 * 2
def baseEnd_7637105 : Nat := 48413650294511697842779

theorem tailTrace_7637105 : CollatzResearch.WordTrace tailWord_7637105 prefixEnd_7637105 48413650294511697842779 := by
  unfold tailWord_7637105
  simp only [CollatzResearch.WordTrace]
  refine ⟨278548102997080373537392769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185698735331386915691595179 278548102997080373537392769)
  ·
    refine ⟨208911077247810280153044577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278548102997080373537392769 208911077247810280153044577)
    ·
      refine ⟨156683307935857710114783433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208911077247810280153044577 156683307935857710114783433)
      ·
        refine ⟨117512480951893282586087575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156683307935857710114783433 117512480951893282586087575)
        ·
          refine ⟨176268721427839923879131363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117512480951893282586087575 176268721427839923879131363)
          ·
            refine ⟨264403082141759885818697045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176268721427839923879131363 264403082141759885818697045)
            ·
              refine ⟨48413650294511697842779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 264403082141759885818697045 48413650294511697842779)
              ·
                rfl

theorem cell23_7637105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 14].length) (baseStart_7637105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637105 prefixEnd_7637105 := by exact prefixLift 7637105
  have htrace : WordTrace (prefixWord ++ tailWord_7637105) baseStart_7637105 baseEnd_7637105 := by
    simpa [prefixWord, tailWord_7637105, baseEnd_7637105] using wordTrace_append hprefix tailTrace_7637105
  have hstable : (prefixWord ++ tailWord_7637105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637105).length < 2 ^ (prefixWord ++ tailWord_7637105).sum := by decide
  have hdescent : baseEnd_7637105 < baseStart_7637105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637115 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 7]
def baseStart_7637115 : Nat := 118140960795 + 7637115 * 2 ^ 59
def prefixEnd_7637115 : Nat := 4983230072969 + 3 ^ 40 * 7637115 * 2
def baseEnd_7637115 : Nat := 3921510808661992486140053

theorem tailTrace_7637115 : CollatzResearch.WordTrace tailWord_7637115 prefixEnd_7637115 3921510808661992486140053 := by
  unfold tailWord_7637115
  simp only [CollatzResearch.WordTrace]
  refine ⟨278548467727044145245256799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185698978484696096830171199 278548467727044145245256799)
  ·
    refine ⟨417822701590566217867885199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278548467727044145245256799 417822701590566217867885199)
    ·
      refine ⟨626734052385849326801827799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417822701590566217867885199 626734052385849326801827799)
      ·
        refine ⟨940101078578773990202741699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626734052385849326801827799 940101078578773990202741699)
        ·
          refine ⟨1410151617868160985304112549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940101078578773990202741699 1410151617868160985304112549)
          ·
            refine ⟨264403428350280184744521103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1410151617868160985304112549 264403428350280184744521103)
            ·
              refine ⟨396605142525420277116781655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264403428350280184744521103 396605142525420277116781655)
              ·
                refine ⟨594907713788130415675172483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396605142525420277116781655 594907713788130415675172483)
                ·
                  refine ⟨892361570682195623512758725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594907713788130415675172483 892361570682195623512758725)
                  ·
                    refine ⟨167317794502911679408642261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 892361570682195623512758725 167317794502911679408642261)
                    ·
                      refine ⟨3921510808661992486140053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167317794502911679408642261 3921510808661992486140053)
                      ·
                        rfl

theorem cell23_7637115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 7].length) (baseStart_7637115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637115 prefixEnd_7637115 := by exact prefixLift 7637115
  have htrace : WordTrace (prefixWord ++ tailWord_7637115) baseStart_7637115 baseEnd_7637115 := by
    simpa [prefixWord, tailWord_7637115, baseEnd_7637115] using wordTrace_append hprefix tailTrace_7637115
  have hstable : (prefixWord ++ tailWord_7637115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637115).length < 2 ^ (prefixWord ++ tailWord_7637115).sum := by decide
  have hdescent : baseEnd_7637115 < baseStart_7637115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637116 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 3, 2, 2]
def baseStart_7637116 : Nat := 118140960795 + 7637116 * 2 ^ 59
def prefixEnd_7637116 : Nat := 4983230072969 + 3 ^ 40 * 7637116 * 2
def baseEnd_7637116 : Nat := 3921511322142646982227549

theorem tailTrace_7637116 : CollatzResearch.WordTrace tailWord_7637116 prefixEnd_7637116 3921511322142646982227549 := by
  unfold tailWord_7637116
  simp only [CollatzResearch.WordTrace]
  refine ⟨139274252100020261208021601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185699002800027014944028801 139274252100020261208021601)
  ·
    refine ⟨104455689075015195906016201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139274252100020261208021601 104455689075015195906016201)
    ·
      refine ⟨78341766806261396929512151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104455689075015195906016201 78341766806261396929512151)
      ·
        refine ⟨117512650209392095394268227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78341766806261396929512151 117512650209392095394268227)
        ·
          refine ⟨176268975314088143091402341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117512650209392095394268227 176268975314088143091402341)
          ·
            refine ⟨33050432871391526829637939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176268975314088143091402341 33050432871391526829637939)
            ·
              refine ⟨49575649307087290244456909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33050432871391526829637939 49575649307087290244456909)
              ·
                refine ⟨18590868490157733841671341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49575649307087290244456909 18590868490157733841671341)
                ·
                  refine ⟨6971575683809150190626753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18590868490157733841671341 6971575683809150190626753)
                  ·
                    refine ⟨5228681762856862642970065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6971575683809150190626753 5228681762856862642970065)
                    ·
                      refine ⟨3921511322142646982227549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5228681762856862642970065 3921511322142646982227549)
                      ·
                        rfl

theorem cell23_7637116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_7637116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637116 prefixEnd_7637116 := by exact prefixLift 7637116
  have htrace : WordTrace (prefixWord ++ tailWord_7637116) baseStart_7637116 baseEnd_7637116 := by
    simpa [prefixWord, tailWord_7637116, baseEnd_7637116] using wordTrace_append hprefix tailTrace_7637116
  have hstable : (prefixWord ++ tailWord_7637116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637116).length < 2 ^ (prefixWord ++ tailWord_7637116).sum := by decide
  have hdescent : baseEnd_7637116 < baseStart_7637116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637218 : List Nat := [3, 3, 4, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_7637218 : Nat := 118140960795 + 7637218 * 2 ^ 59
def prefixEnd_7637218 : Nat := 4983230072969 + 3 ^ 40 * 7637218 * 2
def baseEnd_7637218 : Nat := 3921563697169405583152081

theorem tailTrace_7637218 : CollatzResearch.WordTrace tailWord_7637218 prefixEnd_7637218 3921563697169405583152081 := by
  unfold tailWord_7637218
  simp only [CollatzResearch.WordTrace]
  refine ⟨69638056111417748459064077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185701482963780662557504205 69638056111417748459064077)
  ·
    refine ⟨26114271041781655672149029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69638056111417748459064077 26114271041781655672149029)
    ·
      refine ⟨4896425820334060438527943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26114271041781655672149029 4896425820334060438527943)
      ·
        refine ⟨7344638730501090657791915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4896425820334060438527943 7344638730501090657791915)
        ·
          refine ⟨11016958095751635986687873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7344638730501090657791915 11016958095751635986687873)
          ·
            refine ⟨8262718571813726990015905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11016958095751635986687873 8262718571813726990015905)
            ·
              refine ⟨6197038928860295242511929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8262718571813726990015905 6197038928860295242511929)
              ·
                refine ⟨4647779196645221431883947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6197038928860295242511929 4647779196645221431883947)
                ·
                  refine ⟨6971668794967832147825921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4647779196645221431883947 6971668794967832147825921)
                  ·
                    refine ⟨5228751596225874110869441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6971668794967832147825921 5228751596225874110869441)
                    ·
                      refine ⟨3921563697169405583152081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5228751596225874110869441 3921563697169405583152081)
                      ·
                        rfl

theorem cell23_7637218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_7637218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637218 prefixEnd_7637218 := by exact prefixLift 7637218
  have htrace : WordTrace (prefixWord ++ tailWord_7637218) baseStart_7637218 baseEnd_7637218 := by
    simpa [prefixWord, tailWord_7637218, baseEnd_7637218] using wordTrace_append hprefix tailTrace_7637218
  have hstable : (prefixWord ++ tailWord_7637218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637218).length < 2 ^ (prefixWord ++ tailWord_7637218).sum := by decide
  have hdescent : baseEnd_7637218 < baseStart_7637218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637299 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 3]
def baseStart_7637299 : Nat := 118140960795 + 7637299 * 2 ^ 59
def prefixEnd_7637299 : Nat := 4983230072969 + 3 ^ 40 * 7637299 * 2
def baseEnd_7637299 : Nat := 3921605289102419766239207

theorem tailTrace_7637299 : CollatzResearch.WordTrace tailWord_7637299 prefixEnd_7637299 3921605289102419766239207 := by
  unfold tailWord_7637299
  simp only [CollatzResearch.WordTrace]
  refine ⟨278555178758377544669954951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185703452505585029779969967 278555178758377544669954951)
  ·
    refine ⟨417832768137566317004932427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278555178758377544669954951 417832768137566317004932427)
    ·
      refine ⟨626749152206349475507398641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417832768137566317004932427 626749152206349475507398641)
      ·
        refine ⟨470061864154762106630548981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626749152206349475507398641 470061864154762106630548981)
        ·
          refine ⟨44068299764508947496613967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 470061864154762106630548981 44068299764508947496613967)
          ·
            refine ⟨66102449646763421244920951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44068299764508947496613967 66102449646763421244920951)
            ·
              refine ⟨99153674470145131867381427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66102449646763421244920951 99153674470145131867381427)
              ·
                refine ⟨148730511705217697801072141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99153674470145131867381427 148730511705217697801072141)
                ·
                  refine ⟨55773941889456636675402053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148730511705217697801072141 55773941889456636675402053)
                  ·
                    refine ⟨10457614104273119376637885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55773941889456636675402053 10457614104273119376637885)
                    ·
                      refine ⟨3921605289102419766239207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10457614104273119376637885 3921605289102419766239207)
                      ·
                        rfl

theorem cell23_7637299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 3].length) (baseStart_7637299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637299 prefixEnd_7637299 := by exact prefixLift 7637299
  have htrace : WordTrace (prefixWord ++ tailWord_7637299) baseStart_7637299 baseEnd_7637299 := by
    simpa [prefixWord, tailWord_7637299, baseEnd_7637299] using wordTrace_append hprefix tailTrace_7637299
  have hstable : (prefixWord ++ tailWord_7637299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637299).length < 2 ^ (prefixWord ++ tailWord_7637299).sum := by decide
  have hdescent : baseEnd_7637299 < baseStart_7637299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637306 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 3, 4]
def baseStart_7637306 : Nat := 118140960795 + 7637306 * 2 ^ 59
def prefixEnd_7637306 : Nat := 4983230072969 + 3 ^ 40 * 7637306 * 2
def baseEnd_7637306 : Nat := 1307202961155667079617225

theorem tailTrace_7637306 : CollatzResearch.WordTrace tailWord_7637306 prefixEnd_7637306 1307202961155667079617225 := by
  unfold tailWord_7637306
  simp only [CollatzResearch.WordTrace]
  refine ⟨69638858517338046216364943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185703622712901456576973181 69638858517338046216364943)
  ·
    refine ⟨104458287776007069324547415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69638858517338046216364943 104458287776007069324547415)
    ·
      refine ⟨156687431664010603986821123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104458287776007069324547415 156687431664010603986821123)
      ·
        refine ⟨235031147496015905980231685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156687431664010603986821123 235031147496015905980231685)
        ·
          refine ⟨44068340155502982371293441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235031147496015905980231685 44068340155502982371293441)
          ·
            refine ⟨33051255116627236778470081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44068340155502982371293441 33051255116627236778470081)
            ·
              refine ⟨24788441337470427583852561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33051255116627236778470081 24788441337470427583852561)
              ·
                refine ⟨18591331003102820687889421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24788441337470427583852561 18591331003102820687889421)
                ·
                  refine ⟨6971749126163557757958533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18591331003102820687889421 6971749126163557757958533)
                  ·
                    refine ⟨1307202961155667079617225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6971749126163557757958533 1307202961155667079617225)
                    ·
                      rfl

theorem cell23_7637306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_7637306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637306 prefixEnd_7637306 := by exact prefixLift 7637306
  have htrace : WordTrace (prefixWord ++ tailWord_7637306) baseStart_7637306 baseEnd_7637306 := by
    simpa [prefixWord, tailWord_7637306, baseEnd_7637306] using wordTrace_append hprefix tailTrace_7637306
  have hstable : (prefixWord ++ tailWord_7637306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637306).length < 2 ^ (prefixWord ++ tailWord_7637306).sum := by decide
  have hdescent : baseEnd_7637306 < baseStart_7637306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637333 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 2, 2, 3]
def baseStart_7637333 : Nat := 118140960795 + 7637333 * 2 ^ 59
def prefixEnd_7637333 : Nat := 4983230072969 + 3 ^ 40 * 7637333 * 2
def baseEnd_7637333 : Nat := 3921622747444672633214051

theorem tailTrace_7637333 : CollatzResearch.WordTrace tailWord_7637333 prefixEnd_7637333 3921622747444672633214051 := by
  unfold tailWord_7637333
  simp only [CollatzResearch.WordTrace]
  refine ⟨278556418840254368476692653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185704279226836245651128435 278556418840254368476692653)
  ·
    refine ⟨104458657065095388178759745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278556418840254368476692653 104458657065095388178759745)
    ·
      refine ⟨78343992798821541134069809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104458657065095388178759745 78343992798821541134069809)
      ·
        refine ⟨58757994599116155850552357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78343992798821541134069809 58757994599116155850552357)
        ·
          refine ⟨11017123987334279221978567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58757994599116155850552357 11017123987334279221978567)
          ·
            refine ⟨16525685981001418832967851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11017123987334279221978567 16525685981001418832967851)
            ·
              refine ⟨24788528971502128249451777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16525685981001418832967851 24788528971502128249451777)
              ·
                refine ⟨18591396728626596187088833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24788528971502128249451777 18591396728626596187088833)
                ·
                  refine ⟨13943547546469947140316625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18591396728626596187088833 13943547546469947140316625)
                  ·
                    refine ⟨10457660659852460355237469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13943547546469947140316625 10457660659852460355237469)
                    ·
                      refine ⟨3921622747444672633214051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10457660659852460355237469 3921622747444672633214051)
                      ·
                        rfl

theorem cell23_7637333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_7637333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637333 prefixEnd_7637333 := by exact prefixLift 7637333
  have htrace : WordTrace (prefixWord ++ tailWord_7637333) baseStart_7637333 baseEnd_7637333 := by
    simpa [prefixWord, tailWord_7637333, baseEnd_7637333] using wordTrace_append hprefix tailTrace_7637333
  have hstable : (prefixWord ++ tailWord_7637333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637333).length < 2 ^ (prefixWord ++ tailWord_7637333).sum := by decide
  have hdescent : baseEnd_7637333 < baseStart_7637333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637373 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 2, 3, 2]
def baseStart_7637373 : Nat := 118140960795 + 7637373 * 2 ^ 59
def prefixEnd_7637373 : Nat := 4983230072969 + 3 ^ 40 * 7637373 * 2
def baseEnd_7637373 : Nat := 3921643286670852476713867

theorem tailTrace_7637373 : CollatzResearch.WordTrace tailWord_7637373 prefixEnd_7637373 3921643286670852476713867 := by
  unfold tailWord_7637373
  simp only [CollatzResearch.WordTrace]
  refine ⟨278557877760109455308148773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185705251840072970205432515 278557877760109455308148773)
  ·
    refine ⟨52229602080020522870277895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278557877760109455308148773 52229602080020522870277895)
    ·
      refine ⟨78344403120030784305416843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52229602080020522870277895 78344403120030784305416843)
      ·
        refine ⟨117516604680046176458125265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78344403120030784305416843 117516604680046176458125265)
        ·
          refine ⟨88137453510034632343593949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117516604680046176458125265 88137453510034632343593949)
          ·
            refine ⟨33051545066262987128847731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88137453510034632343593949 33051545066262987128847731)
            ·
              refine ⟨49577317599394480693271597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33051545066262987128847731 49577317599394480693271597)
              ·
                refine ⟨18591494099772930259976849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49577317599394480693271597 18591494099772930259976849)
                ·
                  refine ⟨13943620574829697694982637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18591494099772930259976849 13943620574829697694982637)
                  ·
                    refine ⟨5228857715561136635618489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13943620574829697694982637 5228857715561136635618489)
                    ·
                      refine ⟨3921643286670852476713867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5228857715561136635618489 3921643286670852476713867)
                      ·
                        rfl

theorem cell23_7637373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_7637373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637373 prefixEnd_7637373 := by exact prefixLift 7637373
  have htrace : WordTrace (prefixWord ++ tailWord_7637373) baseStart_7637373 baseEnd_7637373 := by
    simpa [prefixWord, tailWord_7637373, baseEnd_7637373] using wordTrace_append hprefix tailTrace_7637373
  have hstable : (prefixWord ++ tailWord_7637373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637373).length < 2 ^ (prefixWord ++ tailWord_7637373).sum := by decide
  have hdescent : baseEnd_7637373 < baseStart_7637373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637380 : List Nat := [2, 3, 2, 1, 1, 2, 2, 5, 1, 1, 3]
def baseStart_7637380 : Nat := 118140960795 + 7637380 * 2 ^ 59
def prefixEnd_7637380 : Nat := 4983230072969 + 3 ^ 40 * 7637380 * 2
def baseEnd_7637380 : Nat := 3921646881035433949326335

theorem tailTrace_7637380 : CollatzResearch.WordTrace tailWord_7637380 prefixEnd_7637380 3921646881035433949326335 := by
  unfold tailWord_7637380
  simp only [CollatzResearch.WordTrace]
  refine ⟨139279066535542047751826797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185705422047389397002435729 139279066535542047751826797)
  ·
    refine ⟨52229649950828267906935049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139279066535542047751826797 52229649950828267906935049)
    ·
      refine ⟨39172237463121200930201287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52229649950828267906935049 39172237463121200930201287)
      ·
        refine ⟨58758356194681801395301931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39172237463121200930201287 58758356194681801395301931)
        ·
          refine ⟨88137534292022702092952897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58758356194681801395301931 88137534292022702092952897)
          ·
            refine ⟨66103150719017026569714673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88137534292022702092952897 66103150719017026569714673)
            ·
              refine ⟨49577363039262769927286005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66103150719017026569714673 49577363039262769927286005)
              ·
                refine ⟨4647877784930884680683063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49577363039262769927286005 4647877784930884680683063)
                ·
                  refine ⟨6971816677396327021024595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4647877784930884680683063 6971816677396327021024595)
                  ·
                    refine ⟨10457725016094490531536893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6971816677396327021024595 10457725016094490531536893)
                    ·
                      refine ⟨3921646881035433949326335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10457725016094490531536893 3921646881035433949326335)
                      ·
                        rfl

theorem cell23_7637380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_7637380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637380 prefixEnd_7637380 := by exact prefixLift 7637380
  have htrace : WordTrace (prefixWord ++ tailWord_7637380) baseStart_7637380 baseEnd_7637380 := by
    simpa [prefixWord, tailWord_7637380, baseEnd_7637380] using wordTrace_append hprefix tailTrace_7637380
  have hstable : (prefixWord ++ tailWord_7637380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637380).length < 2 ^ (prefixWord ++ tailWord_7637380).sum := by decide
  have hdescent : baseEnd_7637380 < baseStart_7637380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637383 : List Nat := [1, 1, 4, 2, 2, 1, 5, 1, 1, 5]
def baseStart_7637383 : Nat := 118140960795 + 7637383 * 2 ^ 59
def prefixEnd_7637383 : Nat := 4983230072969 + 3 ^ 40 * 7637383 * 2
def baseEnd_7637383 : Nat := 1307216140492465812529607

theorem tailTrace_7637383 : CollatzResearch.WordTrace tailWord_7637383 prefixEnd_7637383 1307216140492465812529607 := by
  unfold tailWord_7637383
  simp only [CollatzResearch.WordTrace]
  refine ⟨278558242490073227016012803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185705494993382151344008535 278558242490073227016012803)
  ·
    refine ⟨417837363735109840524019205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278558242490073227016012803 417837363735109840524019205)
    ·
      refine ⟨78344505700333095098253601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417837363735109840524019205 78344505700333095098253601)
      ·
        refine ⟨58758379275249821323690201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78344505700333095098253601 58758379275249821323690201)
        ·
          refine ⟨44068784456437365992767651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58758379275249821323690201 44068784456437365992767651)
          ·
            refine ⟨66103176684656048989151477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44068784456437365992767651 66103176684656048989151477)
            ·
              refine ⟨6197172814186504592732951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66103176684656048989151477 6197172814186504592732951)
              ·
                refine ⟨9295759221279756889099427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6197172814186504592732951 9295759221279756889099427)
                ·
                  refine ⟨13943638831919635333649141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9295759221279756889099427 13943638831919635333649141)
                  ·
                    refine ⟨1307216140492465812529607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13943638831919635333649141 1307216140492465812529607)
                    ·
                      rfl

theorem cell23_7637383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_7637383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637383 prefixEnd_7637383 := by exact prefixLift 7637383
  have htrace : WordTrace (prefixWord ++ tailWord_7637383) baseStart_7637383 baseEnd_7637383 := by
    simpa [prefixWord, tailWord_7637383, baseEnd_7637383] using wordTrace_append hprefix tailTrace_7637383
  have hstable : (prefixWord ++ tailWord_7637383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637383).length < 2 ^ (prefixWord ++ tailWord_7637383).sum := by decide
  have hdescent : baseEnd_7637383 < baseStart_7637383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637390 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2]
def baseStart_7637390 : Nat := 118140960795 + 7637390 * 2 ^ 59
def prefixEnd_7637390 : Nat := 4983230072969 + 3 ^ 40 * 7637390 * 2
def baseEnd_7637390 : Nat := 3921652015841978910201289

theorem tailTrace_7637390 : CollatzResearch.WordTrace tailWord_7637390 prefixEnd_7637390 3921652015841978910201289 := by
  unfold tailWord_7637390
  simp only [CollatzResearch.WordTrace]
  refine ⟨34819812225130983401439703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185705665200698578141011749 34819812225130983401439703)
  ·
    refine ⟨52229718337696475102159555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34819812225130983401439703 52229718337696475102159555)
    ·
      refine ⟨78344577506544712653239333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52229718337696475102159555 78344577506544712653239333)
      ·
        refine ⟨14689608282477133622482375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78344577506544712653239333 14689608282477133622482375)
        ·
          refine ⟨22034412423715700433723563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14689608282477133622482375 22034412423715700433723563)
          ·
            refine ⟨33051618635573550650585345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22034412423715700433723563 33051618635573550650585345)
            ·
              refine ⟨24788713976680162987939009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33051618635573550650585345 24788713976680162987939009)
              ·
                refine ⟨18591535482510122240954257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24788713976680162987939009 18591535482510122240954257)
                ·
                  refine ⟨13943651611882591680715693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18591535482510122240954257 13943651611882591680715693)
                  ·
                    refine ⟨5228869354455971880268385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13943651611882591680715693 5228869354455971880268385)
                    ·
                      refine ⟨3921652015841978910201289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5228869354455971880268385 3921652015841978910201289)
                      ·
                        rfl

theorem cell23_7637390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_7637390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637390 prefixEnd_7637390 := by exact prefixLift 7637390
  have htrace : WordTrace (prefixWord ++ tailWord_7637390) baseStart_7637390 baseEnd_7637390 := by
    simpa [prefixWord, tailWord_7637390, baseEnd_7637390] using wordTrace_append hprefix tailTrace_7637390
  have hstable : (prefixWord ++ tailWord_7637390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637390).length < 2 ^ (prefixWord ++ tailWord_7637390).sum := by decide
  have hdescent : baseEnd_7637390 < baseStart_7637390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637399 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_7637399 : Nat := 118140960795 + 7637399 * 2 ^ 59
def prefixEnd_7637399 : Nat := 4983230072969 + 3 ^ 40 * 7637399 * 2
def baseEnd_7637399 : Nat := 3921656637167869374988747

theorem tailTrace_7637399 : CollatzResearch.WordTrace tailWord_7637399 prefixEnd_7637399 3921656637167869374988747 := by
  unfold tailWord_7637399
  simp only [CollatzResearch.WordTrace]
  refine ⟨278558826058015261748595251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185705884038676841165730167 278558826058015261748595251)
  ·
    refine ⟨417838239087022892622892877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278558826058015261748595251 417838239087022892622892877)
    ·
      refine ⟨156689339657633584733584829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417838239087022892622892877 156689339657633584733584829)
      ·
        refine ⟨58758502371612594275094311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156689339657633584733584829 58758502371612594275094311)
        ·
          refine ⟨88137753557418891412641467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58758502371612594275094311 88137753557418891412641467)
          ·
            refine ⟨132206630336128337118962201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88137753557418891412641467 132206630336128337118962201)
            ·
              refine ⟨99154972752096252839221651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132206630336128337118962201 99154972752096252839221651)
              ·
                refine ⟨148732459128144379258832477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99154972752096252839221651 148732459128144379258832477)
                ·
                  refine ⟨55774672173054142222062179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148732459128144379258832477 55774672173054142222062179)
                  ·
                    refine ⟨83662008259581213333093269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55774672173054142222062179 83662008259581213333093269)
                    ·
                      refine ⟨3921656637167869374988747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83662008259581213333093269 3921656637167869374988747)
                      ·
                        rfl

theorem cell23_7637399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_7637399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637399 prefixEnd_7637399 := by exact prefixLift 7637399
  have htrace : WordTrace (prefixWord ++ tailWord_7637399) baseStart_7637399 baseEnd_7637399 := by
    simpa [prefixWord, tailWord_7637399, baseEnd_7637399] using wordTrace_append hprefix tailTrace_7637399
  have hstable : (prefixWord ++ tailWord_7637399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637399).length < 2 ^ (prefixWord ++ tailWord_7637399).sum := by decide
  have hdescent : baseEnd_7637399 < baseStart_7637399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637426 : List Nat := [3, 2, 1, 1, 1, 1, 7, 7]
def baseStart_7637426 : Nat := 118140960795 + 7637426 * 2 ^ 59
def prefixEnd_7637426 : Nat := 4983230072969 + 3 ^ 40 * 7637426 * 2
def baseEnd_7637426 : Nat := 145247055597982991457449

theorem tailTrace_7637426 : CollatzResearch.WordTrace tailWord_7637426 prefixEnd_7637426 145247055597982991457449 := by
  unfold tailWord_7637426
  simp only [CollatzResearch.WordTrace]
  refine ⟨69639952707229361339957033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185706540552611630239885421 69639952707229361339957033)
  ·
    refine ⟨52229964530422021004967775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69639952707229361339957033 52229964530422021004967775)
    ·
      refine ⟨78344946795633031507451663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52229964530422021004967775 78344946795633031507451663)
      ·
        refine ⟨117517420193449547261177495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78344946795633031507451663 117517420193449547261177495)
        ·
          refine ⟨176276130290174320891766243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117517420193449547261177495 176276130290174320891766243)
          ·
            refine ⟨264414195435261481337649365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176276130290174320891766243 264414195435261481337649365)
            ·
              refine ⟨6197207705513940968851157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 264414195435261481337649365 6197207705513940968851157)
              ·
                refine ⟨145247055597982991457449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6197207705513940968851157 145247055597982991457449)
                ·
                  rfl

theorem cell23_7637426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 7].length) (baseStart_7637426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637426 prefixEnd_7637426 := by exact prefixLift 7637426
  have htrace : WordTrace (prefixWord ++ tailWord_7637426) baseStart_7637426 baseEnd_7637426 := by
    simpa [prefixWord, tailWord_7637426, baseEnd_7637426] using wordTrace_append hprefix tailTrace_7637426
  have hstable : (prefixWord ++ tailWord_7637426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637426).length < 2 ^ (prefixWord ++ tailWord_7637426).sum := by decide
  have hdescent : baseEnd_7637426 < baseStart_7637426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637437 : List Nat := [1, 4, 1, 2, 2, 2, 1, 5, 1, 2, 2]
def baseStart_7637437 : Nat := 118140960795 + 7637437 * 2 ^ 59
def prefixEnd_7637437 : Nat := 4983230072969 + 3 ^ 40 * 7637437 * 2
def baseEnd_7637437 : Nat := 3921676149432740226313573

theorem tailTrace_7637437 : CollatzResearch.WordTrace tailWord_7637437 prefixEnd_7637437 3921676149432740226313573 := by
  unfold tailWord_7637437
  simp only [CollatzResearch.WordTrace]
  refine ⟨278560212031877594238478565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185706808021251729492319043 278560212031877594238478565)
  ·
    refine ⟨52230039755977048919714731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278560212031877594238478565 52230039755977048919714731)
    ·
      refine ⟨78345059633965573379572097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52230039755977048919714731 78345059633965573379572097)
      ·
        refine ⟨58758794725474180034679073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78345059633965573379572097 58758794725474180034679073)
        ·
          refine ⟨44069096044105635026009305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58758794725474180034679073 44069096044105635026009305)
          ·
            refine ⟨33051822033079226269506979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44069096044105635026009305 33051822033079226269506979)
            ·
              refine ⟨49577733049618839404260469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33051822033079226269506979 49577733049618839404260469)
              ·
                refine ⟨4647912473401766194149419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49577733049618839404260469 4647912473401766194149419)
                ·
                  refine ⟨6971868710102649291224129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4647912473401766194149419 6971868710102649291224129)
                  ·
                    refine ⟨5228901532576986968418097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6971868710102649291224129 5228901532576986968418097)
                    ·
                      refine ⟨3921676149432740226313573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5228901532576986968418097 3921676149432740226313573)
                      ·
                        rfl

theorem cell23_7637437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_7637437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637437 prefixEnd_7637437 := by exact prefixLift 7637437
  have htrace : WordTrace (prefixWord ++ tailWord_7637437) baseStart_7637437 baseEnd_7637437 := by
    simpa [prefixWord, tailWord_7637437, baseEnd_7637437] using wordTrace_append hprefix tailTrace_7637437
  have hstable : (prefixWord ++ tailWord_7637437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637437).length < 2 ^ (prefixWord ++ tailWord_7637437).sum := by decide
  have hdescent : baseEnd_7637437 < baseStart_7637437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637474 : List Nat := [3, 3, 3, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_7637474 : Nat := 118140960795 + 7637474 * 2 ^ 59
def prefixEnd_7637474 : Nat := 4983230072969 + 3 ^ 40 * 7637474 * 2
def baseEnd_7637474 : Nat := 3921695148216956581550903

theorem tailTrace_7637474 : CollatzResearch.WordTrace tailWord_7637474 prefixEnd_7637474 3921695148216956581550903 := by
  unfold tailWord_7637474
  simp only [CollatzResearch.WordTrace]
  refine ⟨69640390383185887389393869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185707707688495699705050317 69640390383185887389393869)
  ·
    refine ⟨26115146393694707771022701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69640390383185887389393869 26115146393694707771022701)
    ·
      refine ⟨9793179897635515414133513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26115146393694707771022701 9793179897635515414133513)
      ·
        refine ⟨7344884923226636560600135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9793179897635515414133513 7344884923226636560600135)
        ·
          refine ⟨11017327384839954840900203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7344884923226636560600135 11017327384839954840900203)
          ·
            refine ⟨16525991077259932261350305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11017327384839954840900203 16525991077259932261350305)
            ·
              refine ⟨12394493307944949196012729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16525991077259932261350305 12394493307944949196012729)
              ·
                refine ⟨9295869980958711897009547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12394493307944949196012729 9295869980958711897009547)
                ·
                  refine ⟨13943804971438067845514321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9295869980958711897009547 13943804971438067845514321)
                  ·
                    refine ⟨10457853728578550884135741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13943804971438067845514321 10457853728578550884135741)
                    ·
                      refine ⟨3921695148216956581550903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10457853728578550884135741 3921695148216956581550903)
                      ·
                        rfl

theorem cell23_7637474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_7637474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637474 prefixEnd_7637474 := by exact prefixLift 7637474
  have htrace : WordTrace (prefixWord ++ tailWord_7637474) baseStart_7637474 baseEnd_7637474 := by
    simpa [prefixWord, tailWord_7637474, baseEnd_7637474] using wordTrace_append hprefix tailTrace_7637474
  have hstable : (prefixWord ++ tailWord_7637474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637474).length < 2 ^ (prefixWord ++ tailWord_7637474).sum := by decide
  have hdescent : baseEnd_7637474 < baseStart_7637474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637480 : List Nat := [2, 1, 4, 1, 1, 3, 1, 4, 1, 3, 2]
def baseStart_7637480 : Nat := 118140960795 + 7637480 * 2 ^ 59
def prefixEnd_7637480 : Nat := 4983230072969 + 3 ^ 40 * 7637480 * 2
def baseEnd_7637480 : Nat := 3921698229100883558075875

theorem tailTrace_7637480 : CollatzResearch.WordTrace tailWord_7637480 prefixEnd_7637480 3921698229100883558075875 := by
  unfold tailWord_7637480
  simp only [CollatzResearch.WordTrace]
  refine ⟨139280890185360906291146947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185707853580481208388195929 139280890185360906291146947)
  ·
    refine ⟨208921335278041359436720421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139280890185360906291146947 208921335278041359436720421)
    ·
      refine ⟨39172750364632754894385079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208921335278041359436720421 39172750364632754894385079)
      ·
        refine ⟨58759125546949132341577619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39172750364632754894385079 58759125546949132341577619)
        ·
          refine ⟨88138688320423698512366429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58759125546949132341577619 88138688320423698512366429)
          ·
            refine ⟨33052008120158886942137411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88138688320423698512366429 33052008120158886942137411)
            ·
              refine ⟨49578012180238330413206117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33052008120158886942137411 49578012180238330413206117)
              ·
                refine ⟨9295877283794686952476147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49578012180238330413206117 9295877283794686952476147)
                ·
                  refine ⟨13943815925692030428714221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9295877283794686952476147 13943815925692030428714221)
                  ·
                    refine ⟨5228930972134511410767833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13943815925692030428714221 5228930972134511410767833)
                    ·
                      refine ⟨3921698229100883558075875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5228930972134511410767833 3921698229100883558075875)
                      ·
                        rfl

theorem cell23_7637480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_7637480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637480 prefixEnd_7637480 := by exact prefixLift 7637480
  have htrace : WordTrace (prefixWord ++ tailWord_7637480) baseStart_7637480 baseEnd_7637480 := by
    simpa [prefixWord, tailWord_7637480, baseEnd_7637480] using wordTrace_append hprefix tailTrace_7637480
  have hstable : (prefixWord ++ tailWord_7637480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637480).length < 2 ^ (prefixWord ++ tailWord_7637480).sum := by decide
  have hdescent : baseEnd_7637480 < baseStart_7637480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637496 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 2, 1, 5]
def baseStart_7637496 : Nat := 118140960795 + 7637496 * 2 ^ 59
def prefixEnd_7637496 : Nat := 4983230072969 + 3 ^ 40 * 7637496 * 2
def baseEnd_7637496 : Nat := 3921706444791355495475801

theorem tailTrace_7637496 : CollatzResearch.WordTrace tailWord_7637496 prefixEnd_7637496 3921706444791355495475801 := by
  unfold tailWord_7637496
  simp only [CollatzResearch.WordTrace]
  refine ⟨139281181969331923657438171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185708242625775898209917561 139281181969331923657438171)
  ·
    refine ⟨208921772953997885486157257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139281181969331923657438171 208921772953997885486157257)
    ·
      refine ⟨156691329715498414114617943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208921772953997885486157257 156691329715498414114617943)
      ·
        refine ⟨235036994573247621171926915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156691329715498414114617943 235036994573247621171926915)
        ·
          refine ⟨352555491859871431757890373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235036994573247621171926915 352555491859871431757890373)
          ·
            refine ⟨66104154723725893454604445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352555491859871431757890373 66104154723725893454604445)
            ·
              refine ⟨24789058021397210045476667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66104154723725893454604445 24789058021397210045476667)
              ·
                refine ⟨37183587032095815068215001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24789058021397210045476667 37183587032095815068215001)
                ·
                  refine ⟨27887690274071861301161251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37183587032095815068215001 27887690274071861301161251)
                  ·
                    refine ⟨41831535411107791951741877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27887690274071861301161251 41831535411107791951741877)
                    ·
                      refine ⟨3921706444791355495475801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41831535411107791951741877 3921706444791355495475801)
                      ·
                        rfl

theorem cell23_7637496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_7637496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637496 prefixEnd_7637496 := by exact prefixLift 7637496
  have htrace : WordTrace (prefixWord ++ tailWord_7637496) baseStart_7637496 baseEnd_7637496 := by
    simpa [prefixWord, tailWord_7637496, baseEnd_7637496] using wordTrace_append hprefix tailTrace_7637496
  have hstable : (prefixWord ++ tailWord_7637496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637496).length < 2 ^ (prefixWord ++ tailWord_7637496).sum := by decide
  have hdescent : baseEnd_7637496 < baseStart_7637496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637583 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 1, 6, 2]
def baseStart_7637583 : Nat := 118140960795 + 7637583 * 2 ^ 59
def prefixEnd_7637583 : Nat := 4983230072969 + 3 ^ 40 * 7637583 * 2
def baseEnd_7637583 : Nat := 3921751117608296655087901

theorem tailTrace_7637583 : CollatzResearch.WordTrace tailWord_7637583 prefixEnd_7637583 3921751117608296655087901 := by
  unfold tailWord_7637583
  simp only [CollatzResearch.WordTrace]
  refine ⟨278565537089348661173293403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185710358059565774115528935 278565537089348661173293403)
  ·
    refine ⟨417848305634022991759940105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278565537089348661173293403 417848305634022991759940105)
    ·
      refine ⟨313386229225517243819955079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417848305634022991759940105 313386229225517243819955079)
      ·
        refine ⟨470079343838275865729932619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313386229225517243819955079 470079343838275865729932619)
        ·
          refine ⟨705119015757413798594898929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470079343838275865729932619 705119015757413798594898929)
          ·
            refine ⟨528839261818060348946174197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705119015757413798594898929 528839261818060348946174197)
            ·
              refine ⟨49578680795443157713703831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 528839261818060348946174197 49578680795443157713703831)
              ·
                refine ⟨74368021193164736570555747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49578680795443157713703831 74368021193164736570555747)
                ·
                  refine ⟨111552031789747104855833621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74368021193164736570555747 111552031789747104855833621)
                  ·
                    refine ⟨5229001490144395540117201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111552031789747104855833621 5229001490144395540117201)
                    ·
                      refine ⟨3921751117608296655087901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5229001490144395540117201 3921751117608296655087901)
                      ·
                        rfl

theorem cell23_7637583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 6, 2].length) (baseStart_7637583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637583 prefixEnd_7637583 := by exact prefixLift 7637583
  have htrace : WordTrace (prefixWord ++ tailWord_7637583) baseStart_7637583 baseEnd_7637583 := by
    simpa [prefixWord, tailWord_7637583, baseEnd_7637583] using wordTrace_append hprefix tailTrace_7637583
  have hstable : (prefixWord ++ tailWord_7637583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637583).length < 2 ^ (prefixWord ++ tailWord_7637583).sum := by decide
  have hdescent : baseEnd_7637583 < baseStart_7637583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637603 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 3]
def baseStart_7637603 : Nat := 118140960795 + 7637603 * 2 ^ 59
def prefixEnd_7637603 : Nat := 4983230072969 + 3 ^ 40 * 7637603 * 2
def baseEnd_7637603 : Nat := 3921761387221386576837809

theorem tailTrace_7637603 : CollatzResearch.WordTrace tailWord_7637603 prefixEnd_7637603 3921761387221386576837809 := by
  unfold tailWord_7637603
  simp only [CollatzResearch.WordTrace]
  refine ⟨278566266549276204589021463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185710844366184136392680975 278566266549276204589021463)
  ·
    refine ⟨417849399823914306883532195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278566266549276204589021463 417849399823914306883532195)
    ·
      refine ⟨626774099735871460325298293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417849399823914306883532195 626774099735871460325298293)
      ·
        refine ⟨58760071850237949405496715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 626774099735871460325298293 58760071850237949405496715)
        ·
          refine ⟨88140107775356924108245073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58760071850237949405496715 88140107775356924108245073)
          ·
            refine ⟨66105080831517693081183805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88140107775356924108245073 66105080831517693081183805)
            ·
              refine ⟨24789405311819134905443927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66105080831517693081183805 24789405311819134905443927)
              ·
                refine ⟨37184107967728702358165891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24789405311819134905443927 37184107967728702358165891)
                ·
                  refine ⟨55776161951593053537248837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37184107967728702358165891 55776161951593053537248837)
                  ·
                    refine ⟨10458030365923697538234157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55776161951593053537248837 10458030365923697538234157)
                    ·
                      refine ⟨3921761387221386576837809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10458030365923697538234157 3921761387221386576837809)
                      ·
                        rfl

theorem cell23_7637603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_7637603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637603 prefixEnd_7637603 := by exact prefixLift 7637603
  have htrace : WordTrace (prefixWord ++ tailWord_7637603) baseStart_7637603 baseEnd_7637603 := by
    simpa [prefixWord, tailWord_7637603, baseEnd_7637603] using wordTrace_append hprefix tailTrace_7637603
  have hstable : (prefixWord ++ tailWord_7637603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637603).length < 2 ^ (prefixWord ++ tailWord_7637603).sum := by decide
  have hdescent : baseEnd_7637603 < baseStart_7637603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637613 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_7637613 : Nat := 118140960795 + 7637613 * 2 ^ 59
def prefixEnd_7637613 : Nat := 4983230072969 + 3 ^ 40 * 7637613 * 2
def baseEnd_7637613 : Nat := 3921766522027931537712763

theorem tailTrace_7637613 : CollatzResearch.WordTrace tailWord_7637613 prefixEnd_7637613 3921766522027931537712763 := by
  unfold tailWord_7637613
  simp only [CollatzResearch.WordTrace]
  refine ⟨278566631279239976296885493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185711087519493317531256995 278566631279239976296885493)
  ·
    refine ⟨26115621682428747777833015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278566631279239976296885493 26115621682428747777833015)
    ·
      refine ⟨39173432523643121666749523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26115621682428747777833015 39173432523643121666749523)
      ·
        refine ⟨58760148785464682500124285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39173432523643121666749523 58760148785464682500124285)
        ·
          refine ⟨22035055794549255937546607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58760148785464682500124285 22035055794549255937546607)
          ·
            refine ⟨33052583691823883906319911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22035055794549255937546607 33052583691823883906319911)
            ·
              refine ⟨49578875537735825859479867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33052583691823883906319911 49578875537735825859479867)
              ·
                refine ⟨74368313306603738789219801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49578875537735825859479867 74368313306603738789219801)
                ·
                  refine ⟨55776234979952804091914851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74368313306603738789219801 55776234979952804091914851)
                  ·
                    refine ⟨83664352469929206137872277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55776234979952804091914851 83664352469929206137872277)
                    ·
                      refine ⟨3921766522027931537712763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83664352469929206137872277 3921766522027931537712763)
                      ·
                        rfl

theorem cell23_7637613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_7637613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637613 prefixEnd_7637613 := by exact prefixLift 7637613
  have htrace : WordTrace (prefixWord ++ tailWord_7637613) baseStart_7637613 baseEnd_7637613 := by
    simpa [prefixWord, tailWord_7637613, baseEnd_7637613] using wordTrace_append hprefix tailTrace_7637613
  have hstable : (prefixWord ++ tailWord_7637613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637613).length < 2 ^ (prefixWord ++ tailWord_7637613).sum := by decide
  have hdescent : baseEnd_7637613 < baseStart_7637613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637623 : List Nat := [1, 1, 3, 1, 1, 3, 5, 2, 6]
def baseStart_7637623 : Nat := 118140960795 + 7637623 * 2 ^ 59
def prefixEnd_7637623 : Nat := 4983230072969 + 3 ^ 40 * 7637623 * 2
def baseEnd_7637623 : Nat := 435752406314941833176413

theorem tailTrace_7637623 : CollatzResearch.WordTrace tailWord_7637623 prefixEnd_7637623 435752406314941833176413 := by
  unfold tailWord_7637623
  simp only [CollatzResearch.WordTrace]
  refine ⟨278566996009203748004749523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185711330672802498669833015 278566996009203748004749523)
  ·
    refine ⟨417850494013805622007124285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278566996009203748004749523 417850494013805622007124285)
    ·
      refine ⟨156693935255177108252671607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417850494013805622007124285 156693935255177108252671607)
      ·
        refine ⟨235040902882765662379007411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156693935255177108252671607 235040902882765662379007411)
        ·
          refine ⟨352561354324148493568511117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235040902882765662379007411 352561354324148493568511117)
          ·
            refine ⟨132210507871555685088191669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352561354324148493568511117 132210507871555685088191669)
            ·
              refine ⟨12394735112958345477017969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132210507871555685088191669 12394735112958345477017969)
              ·
                refine ⟨9296051334718759107763477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12394735112958345477017969 9296051334718759107763477)
                ·
                  refine ⟨435752406314941833176413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9296051334718759107763477 435752406314941833176413)
                  ·
                    rfl

theorem cell23_7637623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 6].length) (baseStart_7637623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637623 prefixEnd_7637623 := by exact prefixLift 7637623
  have htrace : WordTrace (prefixWord ++ tailWord_7637623) baseStart_7637623 baseEnd_7637623 := by
    simpa [prefixWord, tailWord_7637623, baseEnd_7637623] using wordTrace_append hprefix tailTrace_7637623
  have hstable : (prefixWord ++ tailWord_7637623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637623).length < 2 ^ (prefixWord ++ tailWord_7637623).sum := by decide
  have hdescent : baseEnd_7637623 < baseStart_7637623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637667 : List Nat := [1, 1, 1, 4, 1, 1, 2, 7, 1, 1, 3]
def baseStart_7637667 : Nat := 118140960795 + 7637667 * 2 ^ 59
def prefixEnd_7637667 : Nat := 4983230072969 + 3 ^ 40 * 7637667 * 2
def baseEnd_7637667 : Nat := 3921794249983274326437515

theorem tailTrace_7637667 : CollatzResearch.WordTrace tailWord_7637667 prefixEnd_7637667 3921794249983274326437515 := by
  unfold tailWord_7637667
  simp only [CollatzResearch.WordTrace]
  refine ⟨278568600821044343519351255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185712400547362895679567503 278568600821044343519351255)
  ·
    refine ⟨417852901231566515279026883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278568600821044343519351255 417852901231566515279026883)
    ·
      refine ⟨626779351847349772918540325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417852901231566515279026883 626779351847349772918540325)
      ·
        refine ⟨117521128471378082422226311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 626779351847349772918540325 117521128471378082422226311)
        ·
          refine ⟨176281692707067123633339467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117521128471378082422226311 176281692707067123633339467)
          ·
            refine ⟨264422539060600685450009201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176281692707067123633339467 264422539060600685450009201)
            ·
              refine ⟨198316904295450514087506901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264422539060600685450009201 198316904295450514087506901)
              ·
                refine ⟨4648052444424621423925943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 198316904295450514087506901 4648052444424621423925943)
                ·
                  refine ⟨6972078666636932135888915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4648052444424621423925943 6972078666636932135888915)
                  ·
                    refine ⟨10458117999955398203833373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6972078666636932135888915 10458117999955398203833373)
                    ·
                      refine ⟨3921794249983274326437515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10458117999955398203833373 3921794249983274326437515)
                      ·
                        rfl

theorem cell23_7637667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_7637667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637667 prefixEnd_7637667 := by exact prefixLift 7637667
  have htrace : WordTrace (prefixWord ++ tailWord_7637667) baseStart_7637667 baseEnd_7637667 := by
    simpa [prefixWord, tailWord_7637667, baseEnd_7637667] using wordTrace_append hprefix tailTrace_7637667
  have hstable : (prefixWord ++ tailWord_7637667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637667).length < 2 ^ (prefixWord ++ tailWord_7637667).sum := by decide
  have hdescent : baseEnd_7637667 < baseStart_7637667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637677 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_7637677 : Nat := 118140960795 + 7637677 * 2 ^ 59
def prefixEnd_7637677 : Nat := 4983230072969 + 3 ^ 40 * 7637677 * 2
def baseEnd_7637677 : Nat := 3921799384789819287312469

theorem tailTrace_7637677 : CollatzResearch.WordTrace tailWord_7637677 prefixEnd_7637677 3921799384789819287312469 := by
  unfold tailWord_7637677
  simp only [CollatzResearch.WordTrace]
  refine ⟨278568965551008115227215285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185712643700672076818143523 278568965551008115227215285)
  ·
    refine ⟨26115840520407010802551433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278568965551008115227215285 26115840520407010802551433)
    ·
      refine ⟨19586880390305258101913575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26115840520407010802551433 19586880390305258101913575)
      ·
        refine ⟨29380320585457887152870363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19586880390305258101913575 29380320585457887152870363)
        ·
          refine ⟨44070480878186830729305545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29380320585457887152870363 44070480878186830729305545)
          ·
            refine ⟨33052860658640123046979159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44070480878186830729305545 33052860658640123046979159)
            ·
              refine ⟨49579290987960184570468739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33052860658640123046979159 49579290987960184570468739)
              ·
                refine ⟨74368936481940276855703109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49579290987960184570468739 74368936481940276855703109)
                ·
                  refine ⟨13944175590363801910444333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74368936481940276855703109 13944175590363801910444333)
                  ·
                    refine ⟨5229065846386425716416625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13944175590363801910444333 5229065846386425716416625)
                    ·
                      refine ⟨3921799384789819287312469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5229065846386425716416625 3921799384789819287312469)
                      ·
                        rfl

theorem cell23_7637677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_7637677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637677 prefixEnd_7637677 := by exact prefixLift 7637677
  have htrace : WordTrace (prefixWord ++ tailWord_7637677) baseStart_7637677 baseEnd_7637677 := by
    simpa [prefixWord, tailWord_7637677, baseEnd_7637677] using wordTrace_append hprefix tailTrace_7637677
  have hstable : (prefixWord ++ tailWord_7637677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637677).length < 2 ^ (prefixWord ++ tailWord_7637677).sum := by decide
  have hdescent : baseEnd_7637677 < baseStart_7637677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637717 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 1, 6]
def baseStart_7637717 : Nat := 118140960795 + 7637717 * 2 ^ 59
def prefixEnd_7637717 : Nat := 4983230072969 + 3 ^ 40 * 7637717 * 2
def baseEnd_7637717 : Nat := 1307273308005333043604095

theorem tailTrace_7637717 : CollatzResearch.WordTrace tailWord_7637717 prefixEnd_7637717 1307273308005333043604095 := by
  unfold tailWord_7637717
  simp only [CollatzResearch.WordTrace]
  refine ⟨278570424470863202058671405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185713616313908801372447603 278570424470863202058671405)
  ·
    refine ⟨104463909176573700772001777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278570424470863202058671405 104463909176573700772001777)
    ·
      refine ⟨78347931882430275579001333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104463909176573700772001777 78347931882430275579001333)
      ·
        refine ⟨7345118613977838335531375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78347931882430275579001333 7345118613977838335531375)
        ·
          refine ⟨11017677920966757503297063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7345118613977838335531375 11017677920966757503297063)
          ·
            refine ⟨16526516881450136254945595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11017677920966757503297063 16526516881450136254945595)
            ·
              refine ⟨24789775322175204382418393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16526516881450136254945595 24789775322175204382418393)
              ·
                refine ⟨18592331491631403286813795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24789775322175204382418393 18592331491631403286813795)
                ·
                  refine ⟨27888497237447104930220693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18592331491631403286813795 27888497237447104930220693)
                  ·
                    refine ⟨1307273308005333043604095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27888497237447104930220693 1307273308005333043604095)
                    ·
                      rfl

theorem cell23_7637717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_7637717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637717 prefixEnd_7637717 := by exact prefixLift 7637717
  have htrace : WordTrace (prefixWord ++ tailWord_7637717) baseStart_7637717 baseEnd_7637717 := by
    simpa [prefixWord, tailWord_7637717, baseEnd_7637717] using wordTrace_append hprefix tailTrace_7637717
  have hstable : (prefixWord ++ tailWord_7637717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637717).length < 2 ^ (prefixWord ++ tailWord_7637717).sum := by decide
  have hdescent : baseEnd_7637717 < baseStart_7637717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637720 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 1, 2, 4]
def baseStart_7637720 : Nat := 118140960795 + 7637720 * 2 ^ 59
def prefixEnd_7637720 : Nat := 4983230072969 + 3 ^ 40 * 7637720 * 2
def baseEnd_7637720 : Nat := 3921821464457962619074771

theorem tailTrace_7637720 : CollatzResearch.WordTrace tailWord_7637720 prefixEnd_7637720 3921821464457962619074771 := by
  unfold tailWord_7637720
  simp only [CollatzResearch.WordTrace]
  refine ⟨139285266944926166785515307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185713689259901555714020409 139285266944926166785515307)
  ·
    refine ⟨208927900417389250178272961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139285266944926166785515307 208927900417389250178272961)
    ·
      refine ⟨156695925313041937633704721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208927900417389250178272961 156695925313041937633704721)
      ·
        refine ⟨117521943984781453225278541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156695925313041937633704721 117521943984781453225278541)
        ·
          refine ⟨44070728994293044959479453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117521943984781453225278541 44070728994293044959479453)
          ·
            refine ⟨16526523372859891859804795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44070728994293044959479453 16526523372859891859804795)
            ·
              refine ⟨24789785059289837789707193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16526523372859891859804795 24789785059289837789707193)
              ·
                refine ⟨18592338794467378342280395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24789785059289837789707193 18592338794467378342280395)
                ·
                  refine ⟨27888508191701067513420593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18592338794467378342280395 27888508191701067513420593)
                  ·
                    refine ⟨20916381143775800635065445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27888508191701067513420593 20916381143775800635065445)
                    ·
                      refine ⟨3921821464457962619074771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20916381143775800635065445 3921821464457962619074771)
                      ·
                        rfl

theorem cell23_7637720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_7637720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637720 prefixEnd_7637720 := by exact prefixLift 7637720
  have htrace : WordTrace (prefixWord ++ tailWord_7637720) baseStart_7637720 baseEnd_7637720 := by
    simpa [prefixWord, tailWord_7637720, baseEnd_7637720] using wordTrace_append hprefix tailTrace_7637720
  have hstable : (prefixWord ++ tailWord_7637720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637720).length < 2 ^ (prefixWord ++ tailWord_7637720).sum := by decide
  have hdescent : baseEnd_7637720 < baseStart_7637720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637741 : List Nat := [1, 5, 1, 2, 1, 1, 3, 4, 1, 2, 2]
def baseStart_7637741 : Nat := 118140960795 + 7637741 * 2 ^ 59
def prefixEnd_7637741 : Nat := 4983230072969 + 3 ^ 40 * 7637741 * 2
def baseEnd_7637741 : Nat := 3921832247551707036912175

theorem tailTrace_7637741 : CollatzResearch.WordTrace tailWord_7637741 prefixEnd_7637741 3921832247551707036912175 := by
  unfold tailWord_7637741
  simp only [CollatzResearch.WordTrace]
  refine ⟨278571299822776254157545077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185714199881850836105030051 278571299822776254157545077)
  ·
    refine ⟨26116059358385273827269851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278571299822776254157545077 26116059358385273827269851)
    ·
      refine ⟨39174089037577910740904777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26116059358385273827269851 39174089037577910740904777)
      ·
        refine ⟨29380566778183433055678583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39174089037577910740904777 29380566778183433055678583)
        ·
          refine ⟨44070850167275149583517875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29380566778183433055678583 44070850167275149583517875)
          ·
            refine ⟨66106275250912724375276813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44070850167275149583517875 66106275250912724375276813)
            ·
              refine ⟨24789853219092271640728805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66106275250912724375276813 24789853219092271640728805)
              ·
                refine ⟨4648097478579800932636651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24789853219092271640728805 4648097478579800932636651)
                ·
                  refine ⟨6972146217869701398954977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4648097478579800932636651 6972146217869701398954977)
                  ·
                    refine ⟨5229109663402276049216233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6972146217869701398954977 5229109663402276049216233)
                    ·
                      refine ⟨3921832247551707036912175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5229109663402276049216233 3921832247551707036912175)
                      ·
                        rfl

theorem cell23_7637741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_7637741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637741 prefixEnd_7637741 := by exact prefixLift 7637741
  have htrace : WordTrace (prefixWord ++ tailWord_7637741) baseStart_7637741 baseEnd_7637741 := by
    simpa [prefixWord, tailWord_7637741, baseEnd_7637741] using wordTrace_append hprefix tailTrace_7637741
  have hstable : (prefixWord ++ tailWord_7637741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637741).length < 2 ^ (prefixWord ++ tailWord_7637741).sum := by decide
  have hdescent : baseEnd_7637741 < baseStart_7637741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637743 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 2, 7]
def baseStart_7637743 : Nat := 118140960795 + 7637743 * 2 ^ 59
def prefixEnd_7637743 : Nat := 4983230072969 + 3 ^ 40 * 7637743 * 2
def baseEnd_7637743 : Nat := 1307277758171005343029055

theorem tailTrace_7637743 : CollatzResearch.WordTrace tailWord_7637743 prefixEnd_7637743 1307277758171005343029055 := by
  unfold tailWord_7637743
  simp only [CollatzResearch.WordTrace]
  refine ⟨278571372768769008499117883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185714248512512672332745255 278571372768769008499117883)
  ·
    refine ⟨417857059153153512748676825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278571372768769008499117883 417857059153153512748676825)
    ·
      refine ⟨313392794364865134561507619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417857059153153512748676825 313392794364865134561507619)
      ·
        refine ⟨470089191547297701842261429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313392794364865134561507619 470089191547297701842261429)
        ·
          refine ⟨44070861707559159547712009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 470089191547297701842261429 44070861707559159547712009)
          ·
            refine ⟨33053146280669369660784007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44070861707559159547712009 33053146280669369660784007)
            ·
              refine ⟨49579719421004054491176011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33053146280669369660784007 49579719421004054491176011)
              ·
                refine ⟨74369579131506081736764017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49579719421004054491176011 74369579131506081736764017)
                ·
                  refine ⟨55777184348629561302573013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74369579131506081736764017 55777184348629561302573013)
                  ·
                    refine ⟨1307277758171005343029055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55777184348629561302573013 1307277758171005343029055)
                    ·
                      rfl

theorem cell23_7637743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 7].length) (baseStart_7637743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637743 prefixEnd_7637743 := by exact prefixLift 7637743
  have htrace : WordTrace (prefixWord ++ tailWord_7637743) baseStart_7637743 baseEnd_7637743 := by
    simpa [prefixWord, tailWord_7637743, baseEnd_7637743] using wordTrace_append hprefix tailTrace_7637743
  have hstable : (prefixWord ++ tailWord_7637743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637743).length < 2 ^ (prefixWord ++ tailWord_7637743).sum := by decide
  have hdescent : baseEnd_7637743 < baseStart_7637743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637757 : List Nat := [1, 4, 1, 1, 1, 1, 3, 5, 2, 1, 3]
def baseStart_7637757 : Nat := 118140960795 + 7637757 * 2 ^ 59
def prefixEnd_7637757 : Nat := 4983230072969 + 3 ^ 40 * 7637757 * 2
def baseEnd_7637757 : Nat := 3921840463242178974312101

theorem tailTrace_7637757 : CollatzResearch.WordTrace tailWord_7637757 prefixEnd_7637757 3921840463242178974312101 := by
  unfold tailWord_7637757
  simp only [CollatzResearch.WordTrace]
  refine ⟨278571883390718288890127525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185714588927145525926751683 278571883390718288890127525)
  ·
    refine ⟨52232228135759679166898911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278571883390718288890127525 52232228135759679166898911)
    ·
      refine ⟨78348342203639518750348367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52232228135759679166898911 78348342203639518750348367)
      ·
        refine ⟨117522513305459278125522551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78348342203639518750348367 117522513305459278125522551)
        ·
          refine ⟨176283769958188917188283827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117522513305459278125522551 176283769958188917188283827)
          ·
            refine ⟨264425654937283375782425741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176283769958188917188283827 264425654937283375782425741)
            ·
              refine ⟨99159620601481265918409653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264425654937283375782425741 99159620601481265918409653)
              ·
                refine ⟨9296214431388868679850905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99159620601481265918409653 9296214431388868679850905)
                ·
                  refine ⟨6972160823541651509888179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9296214431388868679850905 6972160823541651509888179)
                  ·
                    refine ⟨10458241235312477264832269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6972160823541651509888179 10458241235312477264832269)
                    ·
                      refine ⟨3921840463242178974312101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10458241235312477264832269 3921840463242178974312101)
                      ·
                        rfl

theorem cell23_7637757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_7637757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637757 prefixEnd_7637757 := by exact prefixLift 7637757
  have htrace : WordTrace (prefixWord ++ tailWord_7637757) baseStart_7637757 baseEnd_7637757 := by
    simpa [prefixWord, tailWord_7637757, baseEnd_7637757] using wordTrace_append hprefix tailTrace_7637757
  have hstable : (prefixWord ++ tailWord_7637757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637757).length < 2 ^ (prefixWord ++ tailWord_7637757).sum := by decide
  have hdescent : baseEnd_7637757 < baseStart_7637757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637763 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 4]
def baseStart_7637763 : Nat := 118140960795 + 7637763 * 2 ^ 59
def prefixEnd_7637763 : Nat := 4983230072969 + 3 ^ 40 * 7637763 * 2
def baseEnd_7637763 : Nat := 3921843544126105950837073

theorem tailTrace_7637763 : CollatzResearch.WordTrace tailWord_7637763 prefixEnd_7637763 3921843544126105950837073 := by
  unfold tailWord_7637763
  simp only [CollatzResearch.WordTrace]
  refine ⟨278572102228696551914845943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185714734819131034609897295 278572102228696551914845943)
  ·
    refine ⟨417858153343044827872268915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278572102228696551914845943 417858153343044827872268915)
    ·
      refine ⟨626787230014567241808403373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417858153343044827872268915 626787230014567241808403373)
      ·
        refine ⟨235045211255462715678151265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 626787230014567241808403373 235045211255462715678151265)
        ·
          refine ⟨176283908441597036758613449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235045211255462715678151265 176283908441597036758613449)
          ·
            refine ⟨132212931331197777568960087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176283908441597036758613449 132212931331197777568960087)
            ·
              refine ⟨198319396996796666353440131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132212931331197777568960087 198319396996796666353440131)
              ·
                refine ⟨297479095495194999530160197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198319396996796666353440131 297479095495194999530160197)
                ·
                  refine ⟨55777330405349062411905037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297479095495194999530160197 55777330405349062411905037)
                  ·
                    refine ⟨20916498902005898404464389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55777330405349062411905037 20916498902005898404464389)
                    ·
                      refine ⟨3921843544126105950837073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20916498902005898404464389 3921843544126105950837073)
                      ·
                        rfl

theorem cell23_7637763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_7637763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637763 prefixEnd_7637763 := by exact prefixLift 7637763
  have htrace : WordTrace (prefixWord ++ tailWord_7637763) baseStart_7637763 baseEnd_7637763 := by
    simpa [prefixWord, tailWord_7637763, baseEnd_7637763] using wordTrace_append hprefix tailTrace_7637763
  have hstable : (prefixWord ++ tailWord_7637763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637763).length < 2 ^ (prefixWord ++ tailWord_7637763).sum := by decide
  have hdescent : baseEnd_7637763 < baseStart_7637763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637778 : List Nat := [3, 2, 4, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_7637778 : Nat := 118140960795 + 7637778 * 2 ^ 59
def prefixEnd_7637778 : Nat := 4983230072969 + 3 ^ 40 * 7637778 * 2
def baseEnd_7637778 : Nat := 3921851246335923392149505

theorem tailTrace_7637778 : CollatzResearch.WordTrace tailWord_7637778 prefixEnd_7637778 3921851246335923392149505 := by
  unfold tailWord_7637778
  simp only [CollatzResearch.WordTrace]
  refine ⟨69643162330910552369160497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185715099549094806317761325 69643162330910552369160497)
  ·
    refine ⟨52232371748182914276870373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69643162330910552369160497 52232371748182914276870373)
    ·
      refine ⟨9793569702784296426913195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52232371748182914276870373 9793569702784296426913195)
      ·
        refine ⟨14690354554176444640369793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9793569702784296426913195 14690354554176444640369793)
        ·
          refine ⟨11017765915632333480277345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14690354554176444640369793 11017765915632333480277345)
          ·
            refine ⟨8263324436724250110208009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11017765915632333480277345 8263324436724250110208009)
            ·
              refine ⟨6197493327543187582656007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8263324436724250110208009 6197493327543187582656007)
              ·
                refine ⟨9296239991314781373984011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6197493327543187582656007 9296239991314781373984011)
                ·
                  refine ⟨13944359986972172060976017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9296239991314781373984011 13944359986972172060976017)
                  ·
                    refine ⟨10458269990229129045732013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13944359986972172060976017 10458269990229129045732013)
                    ·
                      refine ⟨3921851246335923392149505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10458269990229129045732013 3921851246335923392149505)
                      ·
                        rfl

theorem cell23_7637778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_7637778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637778 prefixEnd_7637778 := by exact prefixLift 7637778
  have htrace : WordTrace (prefixWord ++ tailWord_7637778) baseStart_7637778 baseEnd_7637778 := by
    simpa [prefixWord, tailWord_7637778, baseEnd_7637778] using wordTrace_append hprefix tailTrace_7637778
  have hstable : (prefixWord ++ tailWord_7637778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637778).length < 2 ^ (prefixWord ++ tailWord_7637778).sum := by decide
  have hdescent : baseEnd_7637778 < baseStart_7637778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637803 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 7]
def baseStart_7637803 : Nat := 118140960795 + 7637803 * 2 ^ 59
def prefixEnd_7637803 : Nat := 4983230072969 + 3 ^ 40 * 7637803 * 2
def baseEnd_7637803 : Nat := 435762675928031754926321

theorem tailTrace_7637803 : CollatzResearch.WordTrace tailWord_7637803 prefixEnd_7637803 435762675928031754926321 := by
  unfold tailWord_7637803
  simp only [CollatzResearch.WordTrace]
  refine ⟨278573561148551638746302063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185715707432367759164201375 278573561148551638746302063)
  ·
    refine ⟨417860341722827458119453095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278573561148551638746302063 417860341722827458119453095)
    ·
      refine ⟨626790512584241187179179643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417860341722827458119453095 626790512584241187179179643)
      ·
        refine ⟨940185768876361780768769465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626790512584241187179179643 940185768876361780768769465)
        ·
          refine ⟨705139326657271335576577099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 940185768876361780768769465 705139326657271335576577099)
          ·
            refine ⟨1057708989985907003364865649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705139326657271335576577099 1057708989985907003364865649)
            ·
              refine ⟨793281742489430252523649237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1057708989985907003364865649 793281742489430252523649237)
              ·
                refine ⟨18592540839596021543523029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 793281742489430252523649237 18592540839596021543523029)
                ·
                  refine ⟨435762675928031754926321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18592540839596021543523029 435762675928031754926321)
                  ·
                    rfl

theorem cell23_7637803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 7].length) (baseStart_7637803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637803 prefixEnd_7637803 := by exact prefixLift 7637803
  have htrace : WordTrace (prefixWord ++ tailWord_7637803) baseStart_7637803 baseEnd_7637803 := by
    simpa [prefixWord, tailWord_7637803, baseEnd_7637803] using wordTrace_append hprefix tailTrace_7637803
  have hstable : (prefixWord ++ tailWord_7637803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637803).length < 2 ^ (prefixWord ++ tailWord_7637803).sum := by decide
  have hdescent : baseEnd_7637803 < baseStart_7637803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637810 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_7637810 : Nat := 118140960795 + 7637810 * 2 ^ 59
def prefixEnd_7637810 : Nat := 4983230072969 + 3 ^ 40 * 7637810 * 2
def baseEnd_7637810 : Nat := 3921867677716867266949357

theorem tailTrace_7637810 : CollatzResearch.WordTrace tailWord_7637810 prefixEnd_7637810 3921867677716867266949357 := by
  unfold tailWord_7637810
  simp only [CollatzResearch.WordTrace]
  refine ⟨69643454114881569735451721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185715877639684185961204589 69643454114881569735451721)
  ·
    refine ⟨52232590586161177301588791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69643454114881569735451721 52232590586161177301588791)
    ·
      refine ⟨78348885879241765952383187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52232590586161177301588791 78348885879241765952383187)
      ·
        refine ⟨117523328818862648928574781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78348885879241765952383187 117523328818862648928574781)
        ·
          refine ⟨44071248307073493348215543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117523328818862648928574781 44071248307073493348215543)
          ·
            refine ⟨66106872460610240022323315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44071248307073493348215543 66106872460610240022323315)
            ·
              refine ⟨99160308690915360033484973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66106872460610240022323315 99160308690915360033484973)
              ·
                refine ⟨37185115759093260012556865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99160308690915360033484973 37185115759093260012556865)
                ·
                  refine ⟨27888836819319945009417649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37185115759093260012556865 27888836819319945009417649)
                  ·
                    refine ⟨20916627614489958757063237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27888836819319945009417649 20916627614489958757063237)
                    ·
                      refine ⟨3921867677716867266949357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20916627614489958757063237 3921867677716867266949357)
                      ·
                        rfl

theorem cell23_7637810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_7637810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637810 prefixEnd_7637810 := by exact prefixLift 7637810
  have htrace : WordTrace (prefixWord ++ tailWord_7637810) baseStart_7637810 baseEnd_7637810 := by
    simpa [prefixWord, tailWord_7637810, baseEnd_7637810] using wordTrace_append hprefix tailTrace_7637810
  have hstable : (prefixWord ++ tailWord_7637810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637810).length < 2 ^ (prefixWord ++ tailWord_7637810).sum := by decide
  have hdescent : baseEnd_7637810 < baseStart_7637810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637843 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 7]
def baseStart_7637843 : Nat := 118140960795 + 7637843 * 2 ^ 59
def prefixEnd_7637843 : Nat := 4983230072969 + 3 ^ 40 * 7637843 * 2
def baseEnd_7637843 : Nat := 3921884622578465637836705

theorem tailTrace_7637843 : CollatzResearch.WordTrace tailWord_7637843 prefixEnd_7637843 3921884622578465637836705 := by
  unfold tailWord_7637843
  simp only [CollatzResearch.WordTrace]
  refine ⟨278575020068406725577758183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185716680045604483718505455 278575020068406725577758183)
  ·
    refine ⟨417862530102610088366637275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278575020068406725577758183 417862530102610088366637275)
    ·
      refine ⟨626793795153915132549955913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417862530102610088366637275 626793795153915132549955913)
      ·
        refine ⟨470095346365436349412466935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626793795153915132549955913 470095346365436349412466935)
        ·
          refine ⟨705143019548154524118700403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470095346365436349412466935 705143019548154524118700403)
          ·
            refine ⟨1057714529322231786178050605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705143019548154524118700403 1057714529322231786178050605)
            ·
              refine ⟨396642948495836919816768977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1057714529322231786178050605 396642948495836919816768977)
              ·
                refine ⟨297482211371877689862576733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396642948495836919816768977 297482211371877689862576733)
                ·
                  refine ⟨111555829264454133698466275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297482211371877689862576733 111555829264454133698466275)
                  ·
                    refine ⟨167333743896681200547699413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111555829264454133698466275 167333743896681200547699413)
                    ·
                      refine ⟨3921884622578465637836705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167333743896681200547699413 3921884622578465637836705)
                      ·
                        rfl

theorem cell23_7637843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_7637843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637843 prefixEnd_7637843 := by exact prefixLift 7637843
  have htrace : WordTrace (prefixWord ++ tailWord_7637843) baseStart_7637843 baseEnd_7637843 := by
    simpa [prefixWord, tailWord_7637843, baseEnd_7637843] using wordTrace_append hprefix tailTrace_7637843
  have hstable : (prefixWord ++ tailWord_7637843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637843).length < 2 ^ (prefixWord ++ tailWord_7637843).sum := by decide
  have hdescent : baseEnd_7637843 < baseStart_7637843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637850 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 4, 5]
def baseStart_7637850 : Nat := 118140960795 + 7637850 * 2 ^ 59
def prefixEnd_7637850 : Nat := 4983230072969 + 3 ^ 40 * 7637850 * 2
def baseEnd_7637850 : Nat := 1307296072314349036816391

theorem tailTrace_7637850 : CollatzResearch.WordTrace tailWord_7637850 prefixEnd_7637850 1307296072314349036816391 := by
  unfold tailWord_7637850
  simp only [CollatzResearch.WordTrace]
  refine ⟨69643818844845341443315751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185716850252920910515508669 69643818844845341443315751)
  ·
    refine ⟨104465728267268012164973627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69643818844845341443315751 104465728267268012164973627)
    ·
      refine ⟨156698592400902018247460441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104465728267268012164973627 156698592400902018247460441)
      ·
        refine ⟨117523944300676513685595331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156698592400902018247460441 117523944300676513685595331)
        ·
          refine ⟨176285916451014770528392997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117523944300676513685595331 176285916451014770528392997)
          ·
            refine ⟨33053609334565269474073687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176285916451014770528392997 33053609334565269474073687)
            ·
              refine ⟨49580414001847904211110531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33053609334565269474073687 49580414001847904211110531)
              ·
                refine ⟨74370621002771856316665797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49580414001847904211110531 74370621002771856316665797)
                ·
                  refine ⟨13944491438019723059374837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74370621002771856316665797 13944491438019723059374837)
                  ·
                    refine ⟨1307296072314349036816391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13944491438019723059374837 1307296072314349036816391)
                    ·
                      rfl

theorem cell23_7637850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_7637850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637850 prefixEnd_7637850 := by exact prefixLift 7637850
  have htrace : WordTrace (prefixWord ++ tailWord_7637850) baseStart_7637850 baseEnd_7637850 := by
    simpa [prefixWord, tailWord_7637850, baseEnd_7637850] using wordTrace_append hprefix tailTrace_7637850
  have hstable : (prefixWord ++ tailWord_7637850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637850).length < 2 ^ (prefixWord ++ tailWord_7637850).sum := by decide
  have hdescent : baseEnd_7637850 < baseStart_7637850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637860 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_7637860 : Nat := 118140960795 + 7637860 * 2 ^ 59
def prefixEnd_7637860 : Nat := 4983230072969 + 3 ^ 40 * 7637860 * 2
def baseEnd_7637860 : Nat := 3921893351749592071324127

theorem tailTrace_7637860 : CollatzResearch.WordTrace tailWord_7637860 prefixEnd_7637860 3921893351749592071324127 := by
  unfold tailWord_7637860
  simp only [CollatzResearch.WordTrace]
  refine ⟨139287820054672568740563517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185717093406230091654084689 139287820054672568740563517)
  ·
    refine ⟨52232932520502213277711319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139287820054672568740563517 52232932520502213277711319)
    ·
      refine ⟨78349398780753319916566979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52232932520502213277711319 78349398780753319916566979)
      ·
        refine ⟨117524098171129979874850469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78349398780753319916566979 117524098171129979874850469)
        ·
          refine ⟨22035768407086871226534463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117524098171129979874850469 22035768407086871226534463)
          ·
            refine ⟨33053652610630306839801695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22035768407086871226534463 33053652610630306839801695)
            ·
              refine ⟨49580478915945460259702543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33053652610630306839801695 49580478915945460259702543)
              ·
                refine ⟨74370718373918190389553815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49580478915945460259702543 74370718373918190389553815)
                ·
                  refine ⟨111556077560877285584330723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74370718373918190389553815 111556077560877285584330723)
                  ·
                    refine ⟨167334116341315928376496085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111556077560877285584330723 167334116341315928376496085)
                    ·
                      refine ⟨3921893351749592071324127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167334116341315928376496085 3921893351749592071324127)
                      ·
                        rfl

theorem cell23_7637860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_7637860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637860 prefixEnd_7637860 := by exact prefixLift 7637860
  have htrace : WordTrace (prefixWord ++ tailWord_7637860) baseStart_7637860 baseEnd_7637860 := by
    simpa [prefixWord, tailWord_7637860, baseEnd_7637860] using wordTrace_append hprefix tailTrace_7637860
  have hstable : (prefixWord ++ tailWord_7637860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637860).length < 2 ^ (prefixWord ++ tailWord_7637860).sum := by decide
  have hdescent : baseEnd_7637860 < baseStart_7637860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637964 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 4, 3, 2]
def baseStart_7637964 : Nat := 118140960795 + 7637964 * 2 ^ 59
def prefixEnd_7637964 : Nat := 4983230072969 + 3 ^ 40 * 7637964 * 2
def baseEnd_7637964 : Nat := 3921946753737659664423649

theorem tailTrace_7637964 : CollatzResearch.WordTrace tailWord_7637964 prefixEnd_7637964 3921946753737659664423649 := by
  unfold tailWord_7637964
  simp only [CollatzResearch.WordTrace]
  refine ⟨139289716650484181621456473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185719622200645575495275297 139289716650484181621456473)
  ·
    refine ⟨104467287487863136216092355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139289716650484181621456473 104467287487863136216092355)
    ·
      refine ⟨156700931231794704324138533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104467287487863136216092355 156700931231794704324138533)
      ·
        refine ⟨29381424605961507060775975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156700931231794704324138533 29381424605961507060775975)
        ·
          refine ⟨44072136908942260591163963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29381424605961507060775975 44072136908942260591163963)
          ·
            refine ⟨66108205363413390886745945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44072136908942260591163963 66108205363413390886745945)
            ·
              refine ⟨49581154022560043165059459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66108205363413390886745945 49581154022560043165059459)
              ·
                refine ⟨74371731033840064747589189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49581154022560043165059459 74371731033840064747589189)
                ·
                  refine ⟨13944699568845012140172973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74371731033840064747589189 13944699568845012140172973)
                  ·
                    refine ⟨5229262338316879552564865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13944699568845012140172973 5229262338316879552564865)
                    ·
                      refine ⟨3921946753737659664423649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5229262338316879552564865 3921946753737659664423649)
                      ·
                        rfl

theorem cell23_7637964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_7637964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637964 prefixEnd_7637964 := by exact prefixLift 7637964
  have htrace : WordTrace (prefixWord ++ tailWord_7637964) baseStart_7637964 baseEnd_7637964 := by
    simpa [prefixWord, tailWord_7637964, baseEnd_7637964] using wordTrace_append hprefix tailTrace_7637964
  have hstable : (prefixWord ++ tailWord_7637964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637964).length < 2 ^ (prefixWord ++ tailWord_7637964).sum := by decide
  have hdescent : baseEnd_7637964 < baseStart_7637964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637965 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_7637965 : Nat := 118140960795 + 7637965 * 2 ^ 59
def prefixEnd_7637965 : Nat := 4983230072969 + 3 ^ 40 * 7637965 * 2
def baseEnd_7637965 : Nat := 1307315755739438053503715

theorem tailTrace_7637965 : CollatzResearch.WordTrace tailWord_7637965 prefixEnd_7637965 1307315755739438053503715 := by
  unfold tailWord_7637965
  simp only [CollatzResearch.WordTrace]
  refine ⟨278579469773964740413699349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185719646515976493609132899 278579469773964740413699349)
  ·
    refine ⟨13058412645654597206892157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 278579469773964740413699349 13058412645654597206892157)
    ·
      refine ⟨4896904742120473952584559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13058412645654597206892157 4896904742120473952584559)
      ·
        refine ⟨7345357113180710928876839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4896904742120473952584559 7345357113180710928876839)
        ·
          refine ⟨11018035669771066393315259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7345357113180710928876839 11018035669771066393315259)
          ·
            refine ⟨16527053504656599589972889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11018035669771066393315259 16527053504656599589972889)
            ·
              refine ⟨12395290128492449692479667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16527053504656599589972889 12395290128492449692479667)
              ·
                refine ⟨18592935192738674538719501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12395290128492449692479667 18592935192738674538719501)
                ·
                  refine ⟨6972350697277002952019813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18592935192738674538719501 6972350697277002952019813)
                  ·
                    refine ⟨1307315755739438053503715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6972350697277002952019813 1307315755739438053503715)
                    ·
                      rfl

theorem cell23_7637965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_7637965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637965 prefixEnd_7637965 := by exact prefixLift 7637965
  have htrace : WordTrace (prefixWord ++ tailWord_7637965) baseStart_7637965 baseEnd_7637965 := by
    simpa [prefixWord, tailWord_7637965, baseEnd_7637965] using wordTrace_append hprefix tailTrace_7637965
  have hstable : (prefixWord ++ tailWord_7637965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637965).length < 2 ^ (prefixWord ++ tailWord_7637965).sum := by decide
  have hdescent : baseEnd_7637965 < baseStart_7637965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7637994 : List Nat := [3, 1, 3, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_7637994 : Nat := 118140960795 + 7637994 * 2 ^ 59
def prefixEnd_7637994 : Nat := 4983230072969 + 3 ^ 40 * 7637994 * 2
def baseEnd_7637994 : Nat := 3921962158157294547048511

theorem tailTrace_7637994 : CollatzResearch.WordTrace tailWord_7637994 prefixEnd_7637994 3921962158157294547048511 := by
  unfold tailWord_7637994
  simp only [CollatzResearch.WordTrace]
  refine ⟨69645131872714919591626259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185720351660573118911003357 69645131872714919591626259)
  ·
    refine ⟨104467697809072379387439389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69645131872714919591626259 104467697809072379387439389)
    ·
      refine ⟨39175386678402142270289771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104467697809072379387439389 39175386678402142270289771)
      ·
        refine ⟨58763080017603213405434657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39175386678402142270289771 58763080017603213405434657)
        ·
          refine ⟨44072310013202410054075993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58763080017603213405434657 44072310013202410054075993)
          ·
            refine ⟨33054232509901807540556995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44072310013202410054075993 33054232509901807540556995)
            ·
              refine ⟨49581348764852711310835493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33054232509901807540556995 49581348764852711310835493)
              ·
                refine ⟨9296502893409883370781655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49581348764852711310835493 9296502893409883370781655)
                ·
                  refine ⟨13944754340114825056172483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9296502893409883370781655 13944754340114825056172483)
                  ·
                    refine ⟨20917131510172237584258725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13944754340114825056172483 20917131510172237584258725)
                    ·
                      refine ⟨3921962158157294547048511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20917131510172237584258725 3921962158157294547048511)
                      ·
                        rfl

theorem cell23_7637994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_7637994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7637994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7637994 prefixEnd_7637994 := by exact prefixLift 7637994
  have htrace : WordTrace (prefixWord ++ tailWord_7637994) baseStart_7637994 baseEnd_7637994 := by
    simpa [prefixWord, tailWord_7637994, baseEnd_7637994] using wordTrace_append hprefix tailTrace_7637994
  have hstable : (prefixWord ++ tailWord_7637994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7637994).length < 2 ^ (prefixWord ++ tailWord_7637994).sum := by decide
  have hdescent : baseEnd_7637994 < baseStart_7637994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7637994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638017 : List Nat := [1, 2, 4, 1, 2, 4, 9]
def baseStart_7638017 : Nat := 118140960795 + 7638017 * 2 ^ 59
def prefixEnd_7638017 : Nat := 4983230072969 + 3 ^ 40 * 7638017 * 2
def baseEnd_7638017 : Nat := 48419431706325283420505

theorem tailTrace_7638017 : CollatzResearch.WordTrace tailWord_7638017 prefixEnd_7638017 48419431706325283420505 := by
  unfold tailWord_7638017
  simp only [CollatzResearch.WordTrace]
  refine ⟨278581366369776353294592305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185720910913184235529728203 278581366369776353294592305)
  ·
    refine ⟨208936024777332264970944229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278581366369776353294592305 208936024777332264970944229)
    ·
      refine ⟨39175504645749799682052043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208936024777332264970944229 39175504645749799682052043)
      ·
        refine ⟨58763256968624699523078065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39175504645749799682052043 58763256968624699523078065)
        ·
          refine ⟨44072442726468524642308549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58763256968624699523078065 44072442726468524642308549)
          ·
            refine ⟨8263583011212848370432853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44072442726468524642308549 8263583011212848370432853)
            ·
              refine ⟨48419431706325283420505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8263583011212848370432853 48419431706325283420505)
              ·
                rfl

theorem cell23_7638017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 9].length) (baseStart_7638017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638017 prefixEnd_7638017 := by exact prefixLift 7638017
  have htrace : WordTrace (prefixWord ++ tailWord_7638017) baseStart_7638017 baseEnd_7638017 := by
    simpa [prefixWord, tailWord_7638017, baseEnd_7638017] using wordTrace_append hprefix tailTrace_7638017
  have hstable : (prefixWord ++ tailWord_7638017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638017).length < 2 ^ (prefixWord ++ tailWord_7638017).sum := by decide
  have hdescent : baseEnd_7638017 < baseStart_7638017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638028 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 3, 2, 2]
def baseStart_7638028 : Nat := 118140960795 + 7638028 * 2 ^ 59
def prefixEnd_7638028 : Nat := 4983230072969 + 3 ^ 40 * 7638028 * 2
def baseEnd_7638028 : Nat := 3921979616499547414023355

theorem tailTrace_7638028 : CollatzResearch.WordTrace tailWord_7638028 prefixEnd_7638028 3921979616499547414023355 := by
  unfold tailWord_7638028
  simp only [CollatzResearch.WordTrace]
  refine ⟨139290883786368251086621369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185721178381824334782161825 139290883786368251086621369)
  ·
    refine ⟨104468162839776188314966027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139290883786368251086621369 104468162839776188314966027)
    ·
      refine ⟨156702244259664282472449041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104468162839776188314966027 156702244259664282472449041)
      ·
        refine ⟨117526683194748211854336781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156702244259664282472449041 117526683194748211854336781)
        ·
          refine ⟨44072506198030579445376293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117526683194748211854336781 44072506198030579445376293)
          ·
            refine ⟨8263594912130733646008055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44072506198030579445376293 8263594912130733646008055)
            ·
              refine ⟨12395392368196100469012083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8263594912130733646008055 12395392368196100469012083)
              ·
                refine ⟨18593088552294150703518125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12395392368196100469012083 18593088552294150703518125)
                ·
                  refine ⟨6972408207110306513819297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18593088552294150703518125 6972408207110306513819297)
                  ·
                    refine ⟨5229306155332729885364473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6972408207110306513819297 5229306155332729885364473)
                    ·
                      refine ⟨3921979616499547414023355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5229306155332729885364473 3921979616499547414023355)
                      ·
                        rfl

theorem cell23_7638028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_7638028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638028 prefixEnd_7638028 := by exact prefixLift 7638028
  have htrace : WordTrace (prefixWord ++ tailWord_7638028) baseStart_7638028 baseEnd_7638028 := by
    simpa [prefixWord, tailWord_7638028, baseEnd_7638028] using wordTrace_append hprefix tailTrace_7638028
  have hstable : (prefixWord ++ tailWord_7638028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638028).length < 2 ^ (prefixWord ++ tailWord_7638028).sum := by decide
  have hdescent : baseEnd_7638028 < baseStart_7638028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638078 : List Nat := [4, 2, 1, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_7638078 : Nat := 118140960795 + 7638078 * 2 ^ 59
def prefixEnd_7638078 : Nat := 4983230072969 + 3 ^ 40 * 7638078 * 2
def baseEnd_7638078 : Nat := 3922005290532272218398125

theorem tailTrace_7638078 : CollatzResearch.WordTrace tailWord_7638078 prefixEnd_7638078 3922005290532272218398125 := by
  unfold tailWord_7638078
  simp only [CollatzResearch.WordTrace]
  refine ⟨34822948902819420089070361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185722394148370240475041925 34822948902819420089070361)
  ·
    refine ⟨26117211677114565066802771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34822948902819420089070361 26117211677114565066802771)
    ·
      refine ⟨39175817515671847600204157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26117211677114565066802771 39175817515671847600204157)
      ·
        refine ⟨14690931568376942850076559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39175817515671847600204157 14690931568376942850076559)
        ·
          refine ⟨22036397352565414275114839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14690931568376942850076559 22036397352565414275114839)
          ·
            refine ⟨33054596028848121412672259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22036397352565414275114839 33054596028848121412672259)
            ·
              refine ⟨49581894043272182119008389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33054596028848121412672259 49581894043272182119008389)
              ·
                refine ⟨9296605133113534147314073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49581894043272182119008389 9296605133113534147314073)
                ·
                  refine ⟨6972453849835150610485555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9296605133113534147314073 6972453849835150610485555)
                  ·
                    refine ⟨10458680774752725915728333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6972453849835150610485555 10458680774752725915728333)
                    ·
                      refine ⟨3922005290532272218398125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10458680774752725915728333 3922005290532272218398125)
                      ·
                        rfl

theorem cell23_7638078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_7638078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638078 prefixEnd_7638078 := by exact prefixLift 7638078
  have htrace : WordTrace (prefixWord ++ tailWord_7638078) baseStart_7638078 baseEnd_7638078 := by
    simpa [prefixWord, tailWord_7638078, baseEnd_7638078] using wordTrace_append hprefix tailTrace_7638078
  have hstable : (prefixWord ++ tailWord_7638078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638078).length < 2 ^ (prefixWord ++ tailWord_7638078).sum := by decide
  have hdescent : baseEnd_7638078 < baseStart_7638078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638097 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 1, 4, 4]
def baseStart_7638097 : Nat := 118140960795 + 7638097 * 2 ^ 59
def prefixEnd_7638097 : Nat := 4983230072969 + 3 ^ 40 * 7638097 * 2
def baseEnd_7638097 : Nat := 3922015046664707644060537

theorem tailTrace_7638097 : CollatzResearch.WordTrace tailWord_7638097 prefixEnd_7638097 3922015046664707644060537 := by
  unfold tailWord_7638097
  simp only [CollatzResearch.WordTrace]
  refine ⟨278584284209486526957504545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185722856139657684638336363 278584284209486526957504545)
  ·
    refine ⟨208938213157114895218128409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278584284209486526957504545 208938213157114895218128409)
    ·
      refine ⟨156703659867836171413596307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208938213157114895218128409 156703659867836171413596307)
      ·
        refine ⟨235055489801754257120394461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156703659867836171413596307 235055489801754257120394461)
        ·
          refine ⟨88145808675657846420147923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235055489801754257120394461 88145808675657846420147923)
          ·
            refine ⟨132218713013486769630221885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88145808675657846420147923 132218713013486769630221885)
            ·
              refine ⟨49582017380057538611333207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132218713013486769630221885 49582017380057538611333207)
              ·
                refine ⟨74373026070086307916999811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49582017380057538611333207 74373026070086307916999811)
                ·
                  refine ⟨111559539105129461875499717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74373026070086307916999811 111559539105129461875499717)
                  ·
                    refine ⟨20917413582211774101656197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111559539105129461875499717 20917413582211774101656197)
                    ·
                      refine ⟨3922015046664707644060537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20917413582211774101656197 3922015046664707644060537)
                      ·
                        rfl

theorem cell23_7638097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_7638097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638097 prefixEnd_7638097 := by exact prefixLift 7638097
  have htrace : WordTrace (prefixWord ++ tailWord_7638097) baseStart_7638097 baseEnd_7638097 := by
    simpa [prefixWord, tailWord_7638097, baseEnd_7638097] using wordTrace_append hprefix tailTrace_7638097
  have hstable : (prefixWord ++ tailWord_7638097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638097).length < 2 ^ (prefixWord ++ tailWord_7638097).sum := by decide
  have hdescent : baseEnd_7638097 < baseStart_7638097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638101 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 1, 4, 2]
def baseStart_7638101 : Nat := 118140960795 + 7638101 * 2 ^ 59
def prefixEnd_7638101 : Nat := 4983230072969 + 3 ^ 40 * 7638101 * 2
def baseEnd_7638101 : Nat := 3922017100587325628410519

theorem tailTrace_7638101 : CollatzResearch.WordTrace tailWord_7638101 prefixEnd_7638101 3922017100587325628410519 := by
  unfold tailWord_7638101
  simp only [CollatzResearch.WordTrace]
  refine ⟨278584430101472035640650157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185722953400981357093766771 278584430101472035640650157)
  ·
    refine ⟨104469161288052013365243809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278584430101472035640650157 104469161288052013365243809)
    ·
      refine ⟨78351870966039010023932857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104469161288052013365243809 78351870966039010023932857)
      ·
        refine ⟨58763903224529257517949643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78351870966039010023932857 58763903224529257517949643)
        ·
          refine ⟨88145854836793886276924465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58763903224529257517949643 88145854836793886276924465)
          ·
            refine ⟨66109391127595414707693349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88145854836793886276924465 66109391127595414707693349)
            ·
              refine ⟨12395510836424140257692503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66109391127595414707693349 12395510836424140257692503)
              ·
                refine ⟨18593266254636210386538755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12395510836424140257692503 18593266254636210386538755)
                ·
                  refine ⟨27889899381954315579808133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18593266254636210386538755 27889899381954315579808133)
                  ·
                    refine ⟨5229356134116434171214025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27889899381954315579808133 5229356134116434171214025)
                    ·
                      refine ⟨3922017100587325628410519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5229356134116434171214025 3922017100587325628410519)
                      ·
                        rfl

theorem cell23_7638101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_7638101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638101 prefixEnd_7638101 := by exact prefixLift 7638101
  have htrace : WordTrace (prefixWord ++ tailWord_7638101) baseStart_7638101 baseEnd_7638101 := by
    simpa [prefixWord, tailWord_7638101, baseEnd_7638101] using wordTrace_append hprefix tailTrace_7638101
  have hstable : (prefixWord ++ tailWord_7638101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638101).length < 2 ^ (prefixWord ++ tailWord_7638101).sum := by decide
  have hdescent : baseEnd_7638101 < baseStart_7638101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638144 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 1, 7, 2]
def baseStart_7638144 : Nat := 118140960795 + 7638144 * 2 ^ 59
def prefixEnd_7638144 : Nat := 4983230072969 + 3 ^ 40 * 7638144 * 2
def baseEnd_7638144 : Nat := 3922039180255468960172821

theorem tailTrace_7638144 : CollatzResearch.WordTrace tailWord_7638144 prefixEnd_7638144 3922039180255468960172821 := by
  unfold tailWord_7638144
  simp only [CollatzResearch.WordTrace]
  refine ⟨139292999220158126992232743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185723998960210835989643657 139292999220158126992232743)
  ·
    refine ⟨208939498830237190488349115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139292999220158126992232743 208939498830237190488349115)
    ·
      refine ⟨313409248245355785732523673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208939498830237190488349115 313409248245355785732523673)
      ·
        refine ⟨235056936184016839299392755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313409248245355785732523673 235056936184016839299392755)
        ·
          refine ⟨352585404276025258949089133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235056936184016839299392755 352585404276025258949089133)
          ·
            refine ⟨132219526603509472105908425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352585404276025258949089133 132219526603509472105908425)
            ·
              refine ⟨99164644952632104079431319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132219526603509472105908425 99164644952632104079431319)
              ·
                refine ⟨148746967428948156119146979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99164644952632104079431319 148746967428948156119146979)
                ·
                  refine ⟨223120451143422234178720469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148746967428948156119146979 223120451143422234178720469)
                  ·
                    refine ⟨5229385573673958613563761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 223120451143422234178720469 5229385573673958613563761)
                    ·
                      refine ⟨3922039180255468960172821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5229385573673958613563761 3922039180255468960172821)
                      ·
                        rfl

theorem cell23_7638144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 7, 2].length) (baseStart_7638144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638144 prefixEnd_7638144 := by exact prefixLift 7638144
  have htrace : WordTrace (prefixWord ++ tailWord_7638144) baseStart_7638144 baseEnd_7638144 := by
    simpa [prefixWord, tailWord_7638144, baseEnd_7638144] using wordTrace_append hprefix tailTrace_7638144
  have hstable : (prefixWord ++ tailWord_7638144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638144).length < 2 ^ (prefixWord ++ tailWord_7638144).sum := by decide
  have hdescent : baseEnd_7638144 < baseStart_7638144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638147 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 7]
def baseStart_7638147 : Nat := 118140960795 + 7638147 * 2 ^ 59
def prefixEnd_7638147 : Nat := 4983230072969 + 3 ^ 40 * 7638147 * 2
def baseEnd_7638147 : Nat := 3922040720697432448435307

theorem tailTrace_7638147 : CollatzResearch.WordTrace tailWord_7638147 prefixEnd_7638147 3922040720697432448435307 := by
  unfold tailWord_7638147
  simp only [CollatzResearch.WordTrace]
  refine ⟨278586107859305385496824695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185724071906203590331216463 278586107859305385496824695)
  ·
    refine ⟨417879161788958078245237043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278586107859305385496824695 417879161788958078245237043)
    ·
      refine ⟨626818742683437117367855565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417879161788958078245237043 626818742683437117367855565)
      ·
        refine ⟨235057028506288919012945837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 626818742683437117367855565 235057028506288919012945837)
        ·
          refine ⟨88146385689858344629854689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235057028506288919012945837 88146385689858344629854689)
          ·
            refine ⟨66109789267393758472391017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88146385689858344629854689 66109789267393758472391017)
            ·
              refine ⟨49582341950545318854293263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66109789267393758472391017 49582341950545318854293263)
              ·
                refine ⟨74373512925817978281439895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49582341950545318854293263 74373512925817978281439895)
                ·
                  refine ⟨111560269388726967422159843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74373512925817978281439895 111560269388726967422159843)
                  ·
                    refine ⟨167340404083090451133239765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111560269388726967422159843 167340404083090451133239765)
                    ·
                      refine ⟨3922040720697432448435307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167340404083090451133239765 3922040720697432448435307)
                      ·
                        rfl

theorem cell23_7638147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_7638147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638147 prefixEnd_7638147 := by exact prefixLift 7638147
  have htrace : WordTrace (prefixWord ++ tailWord_7638147) baseStart_7638147 baseEnd_7638147 := by
    simpa [prefixWord, tailWord_7638147, baseEnd_7638147] using wordTrace_append hprefix tailTrace_7638147
  have hstable : (prefixWord ++ tailWord_7638147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638147).length < 2 ^ (prefixWord ++ tailWord_7638147).sum := by decide
  have hdescent : baseEnd_7638147 < baseStart_7638147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638152 : List Nat := [2, 1, 3, 4, 2, 1, 3, 1, 2, 2, 2]
def baseStart_7638152 : Nat := 118140960795 + 7638152 * 2 ^ 59
def prefixEnd_7638152 : Nat := 4983230072969 + 3 ^ 40 * 7638152 * 2
def baseEnd_7638152 : Nat := 3922043288100704928872785

theorem tailTrace_7638152 : CollatzResearch.WordTrace tailWord_7638152 prefixEnd_7638152 3922043288100704928872785 := by
  unfold tailWord_7638152
  simp only [CollatzResearch.WordTrace]
  refine ⟨139293145112143635675378355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185724193482858180900504473 139293145112143635675378355)
  ·
    refine ⟨208939717668215453513067533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139293145112143635675378355 208939717668215453513067533)
    ·
      refine ⟨78352394125580795067400325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208939717668215453513067533 78352394125580795067400325)
      ·
        refine ⟨14691073898546399075137561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78352394125580795067400325 14691073898546399075137561)
        ·
          refine ⟨11018305423909799306353171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14691073898546399075137561 11018305423909799306353171)
          ·
            refine ⟨16527458135864698959529757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11018305423909799306353171 16527458135864698959529757)
            ·
              refine ⟨6197796800949262109823659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16527458135864698959529757 6197796800949262109823659)
              ·
                refine ⟨9296695201423893164735489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6197796800949262109823659 9296695201423893164735489)
                ·
                  refine ⟨6972521401067919873551617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9296695201423893164735489 6972521401067919873551617)
                  ·
                    refine ⟨5229391050800939905163713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6972521401067919873551617 5229391050800939905163713)
                    ·
                      refine ⟨3922043288100704928872785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5229391050800939905163713 3922043288100704928872785)
                      ·
                        rfl

theorem cell23_7638152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_7638152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638152 prefixEnd_7638152 := by exact prefixLift 7638152
  have htrace : WordTrace (prefixWord ++ tailWord_7638152) baseStart_7638152 baseEnd_7638152 := by
    simpa [prefixWord, tailWord_7638152, baseEnd_7638152] using wordTrace_append hprefix tailTrace_7638152
  have hstable : (prefixWord ++ tailWord_7638152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638152).length < 2 ^ (prefixWord ++ tailWord_7638152).sum := by decide
  have hdescent : baseEnd_7638152 < baseStart_7638152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638175 : List Nat := [1, 1, 2, 6, 3, 1, 1, 3, 5]
def baseStart_7638175 : Nat := 118140960795 + 7638175 * 2 ^ 59
def prefixEnd_7638175 : Nat := 4983230072969 + 3 ^ 40 * 7638175 * 2
def baseEnd_7638175 : Nat := 435783899795084259876131

theorem tailTrace_7638175 : CollatzResearch.WordTrace tailWord_7638175 prefixEnd_7638175 435783899795084259876131 := by
  unfold tailWord_7638175
  simp only [CollatzResearch.WordTrace]
  refine ⟨278587129103203946278843979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185724752735469297519229319 278587129103203946278843979)
  ·
    refine ⟨417880693654805919418265969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278587129103203946278843979 417880693654805919418265969)
    ·
      refine ⟨313410520241104439563699477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417880693654805919418265969 313410520241104439563699477)
      ·
        refine ⟨14691118136301770604548413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 313410520241104439563699477 14691118136301770604548413)
        ·
          refine ⟨5509169301113163976705655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14691118136301770604548413 5509169301113163976705655)
          ·
            refine ⟨8263753951669745965058483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5509169301113163976705655 8263753951669745965058483)
            ·
              refine ⟨12395630927504618947587725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8263753951669745965058483 12395630927504618947587725)
              ·
                refine ⟨4648361597814232105345397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12395630927504618947587725 4648361597814232105345397)
                ·
                  refine ⟨435783899795084259876131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4648361597814232105345397 435783899795084259876131)
                  ·
                    rfl

theorem cell23_7638175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 5].length) (baseStart_7638175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638175 prefixEnd_7638175 := by exact prefixLift 7638175
  have htrace : WordTrace (prefixWord ++ tailWord_7638175) baseStart_7638175 baseEnd_7638175 := by
    simpa [prefixWord, tailWord_7638175, baseEnd_7638175] using wordTrace_append hprefix tailTrace_7638175
  have hstable : (prefixWord ++ tailWord_7638175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638175).length < 2 ^ (prefixWord ++ tailWord_7638175).sum := by decide
  have hdescent : baseEnd_7638175 < baseStart_7638175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638201 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 3, 4]
def baseStart_7638201 : Nat := 118140960795 + 7638201 * 2 ^ 59
def prefixEnd_7638201 : Nat := 4983230072969 + 3 ^ 40 * 7638201 * 2
def baseEnd_7638201 : Nat := 1307356149550925079053353

theorem tailTrace_7638201 : CollatzResearch.WordTrace tailWord_7638201 prefixEnd_7638201 1307356149550925079053353 := by
  unfold tailWord_7638201
  simp only [CollatzResearch.WordTrace]
  refine ⟨278588077401109752719290457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185725384934073168479526971 278588077401109752719290457)
  ·
    refine ⟨208941058050832314539467843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278588077401109752719290457 208941058050832314539467843)
    ·
      refine ⟨313411587076248471809201765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208941058050832314539467843 313411587076248471809201765)
      ·
        refine ⟨58764672576796588464225331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313411587076248471809201765 58764672576796588464225331)
        ·
          refine ⟨88147008865194882696337997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58764672576796588464225331 88147008865194882696337997)
          ·
            refine ⟨33055128324448081011126749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88147008865194882696337997 33055128324448081011126749)
            ·
              refine ⟨12395673121668030379172531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33055128324448081011126749 12395673121668030379172531)
              ·
                refine ⟨18593509682502045568758797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12395673121668030379172531 18593509682502045568758797)
                ·
                  refine ⟨6972566130938267088284549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18593509682502045568758797 6972566130938267088284549)
                  ·
                    refine ⟨1307356149550925079053353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6972566130938267088284549 1307356149550925079053353)
                    ·
                      rfl

theorem cell23_7638201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 4].length) (baseStart_7638201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638201 prefixEnd_7638201 := by exact prefixLift 7638201
  have htrace : WordTrace (prefixWord ++ tailWord_7638201) baseStart_7638201 baseEnd_7638201 := by
    simpa [prefixWord, tailWord_7638201, baseEnd_7638201] using wordTrace_append hprefix tailTrace_7638201
  have hstable : (prefixWord ++ tailWord_7638201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638201).length < 2 ^ (prefixWord ++ tailWord_7638201).sum := by decide
  have hdescent : baseEnd_7638201 < baseStart_7638201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638217 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 8]
def baseStart_7638217 : Nat := 118140960795 + 7638217 * 2 ^ 59
def prefixEnd_7638217 : Nat := 4983230072969 + 3 ^ 40 * 7638217 * 2
def baseEnd_7638217 : Nat := 3922076664343247174559985

theorem tailTrace_7638217 : CollatzResearch.WordTrace tailWord_7638217 prefixEnd_7638217 3922076664343247174559985 := by
  unfold tailWord_7638217
  simp only [CollatzResearch.WordTrace]
  refine ⟨278588660969051787451872905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185725773979367858301248603 278588660969051787451872905)
  ·
    refine ⟨208941495726788840588904679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278588660969051787451872905 208941495726788840588904679)
    ·
      refine ⟨313412243590183260883357019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208941495726788840588904679 313412243590183260883357019)
      ·
        refine ⟨470118365385274891325035529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313412243590183260883357019 470118365385274891325035529)
        ·
          refine ⟨352588774038956168493776647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470118365385274891325035529 352588774038956168493776647)
          ·
            refine ⟨528883161058434252740664971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352588774038956168493776647 528883161058434252740664971)
            ·
              refine ⟨793324741587651379110997457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528883161058434252740664971 793324741587651379110997457)
              ·
                refine ⟨594993556190738534333248093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793324741587651379110997457 594993556190738534333248093)
                ·
                  refine ⟨223122583571526950374968035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 594993556190738534333248093 223122583571526950374968035)
                  ·
                    refine ⟨334683875357290425562452053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223122583571526950374968035 334683875357290425562452053)
                    ·
                      refine ⟨3922076664343247174559985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 334683875357290425562452053 3922076664343247174559985)
                      ·
                        rfl

theorem cell23_7638217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_7638217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638217 prefixEnd_7638217 := by exact prefixLift 7638217
  have htrace : WordTrace (prefixWord ++ tailWord_7638217) baseStart_7638217 baseEnd_7638217 := by
    simpa [prefixWord, tailWord_7638217, baseEnd_7638217] using wordTrace_append hprefix tailTrace_7638217
  have hstable : (prefixWord ++ tailWord_7638217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638217).length < 2 ^ (prefixWord ++ tailWord_7638217).sum := by decide
  have hdescent : baseEnd_7638217 < baseStart_7638217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638227 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 2, 9]
def baseStart_7638227 : Nat := 118140960795 + 7638227 * 2 ^ 59
def prefixEnd_7638227 : Nat := 4983230072969 + 3 ^ 40 * 7638227 * 2
def baseEnd_7638227 : Nat := 1307360599716597378478313

theorem tailTrace_7638227 : CollatzResearch.WordTrace tailWord_7638227 prefixEnd_7638227 1307360599716597378478313 := by
  unfold tailWord_7638227
  simp only [CollatzResearch.WordTrace]
  refine ⟨278589025699015559159736935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185726017132677039439824623 278589025699015559159736935)
  ·
    refine ⟨417883538548523338739605403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278589025699015559159736935 417883538548523338739605403)
    ·
      refine ⟨626825307822785008109408105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417883538548523338739605403 626825307822785008109408105)
      ·
        refine ⟨470118980867088756082056079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626825307822785008109408105 470118980867088756082056079)
        ·
          refine ⟨705178471300633134123084119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470118980867088756082056079 705178471300633134123084119)
          ·
            refine ⟨1057767706950949701184626179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705178471300633134123084119 1057767706950949701184626179)
            ·
              refine ⟨1586651560426424551776939269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1057767706950949701184626179 1586651560426424551776939269)
              ·
                refine ⟨297497167579954603458176113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1586651560426424551776939269 297497167579954603458176113)
                ·
                  refine ⟨223122875684965952593632085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297497167579954603458176113 223122875684965952593632085)
                  ·
                    refine ⟨1307360599716597378478313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 223122875684965952593632085 1307360599716597378478313)
                    ·
                      rfl

theorem cell23_7638227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 9].length) (baseStart_7638227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638227 prefixEnd_7638227 := by exact prefixLift 7638227
  have htrace : WordTrace (prefixWord ++ tailWord_7638227) baseStart_7638227 baseEnd_7638227 := by
    simpa [prefixWord, tailWord_7638227, baseEnd_7638227] using wordTrace_append hprefix tailTrace_7638227
  have hstable : (prefixWord ++ tailWord_7638227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638227).length < 2 ^ (prefixWord ++ tailWord_7638227).sum := by decide
  have hdescent : baseEnd_7638227 < baseStart_7638227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638281 : List Nat := [1, 2, 1, 1, 3, 3, 2, 4, 1, 1, 4]
def baseStart_7638281 : Nat := 118140960795 + 7638281 * 2 ^ 59
def prefixEnd_7638281 : Nat := 4983230072969 + 3 ^ 40 * 7638281 * 2
def baseEnd_7638281 : Nat := 3922109527105134924159691

theorem tailTrace_7638281 : CollatzResearch.WordTrace tailWord_7638281 prefixEnd_7638281 3922109527105134924159691 := by
  unfold tailWord_7638281
  simp only [CollatzResearch.WordTrace]
  refine ⟨278590995240819926382202697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185727330160546617588135131 278590995240819926382202697)
  ·
    refine ⟨208943246430614944786652023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278590995240819926382202697 208943246430614944786652023)
    ·
      refine ⟨313414869645922417179978035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208943246430614944786652023 313414869645922417179978035)
      ·
        refine ⟨470122304468883625769967053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313414869645922417179978035 470122304468883625769967053)
        ·
          refine ⟨176295864175831359663737645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 470122304468883625769967053 176295864175831359663737645)
          ·
            refine ⟨66110949065936759873901617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176295864175831359663737645 66110949065936759873901617)
            ·
              refine ⟨49583211799452569905426213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66110949065936759873901617 49583211799452569905426213)
              ·
                refine ⟨9296852212397356857267415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49583211799452569905426213 9296852212397356857267415)
                ·
                  refine ⟨13945278318596035285901123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9296852212397356857267415 13945278318596035285901123)
                  ·
                    refine ⟨20917917477894052928851685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13945278318596035285901123 20917917477894052928851685)
                    ·
                      refine ⟨3922109527105134924159691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20917917477894052928851685 3922109527105134924159691)
                      ·
                        rfl

theorem cell23_7638281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 1, 4].length) (baseStart_7638281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638281 prefixEnd_7638281 := by exact prefixLift 7638281
  have htrace : WordTrace (prefixWord ++ tailWord_7638281) baseStart_7638281 baseEnd_7638281 := by
    simpa [prefixWord, tailWord_7638281, baseEnd_7638281] using wordTrace_append hprefix tailTrace_7638281
  have hstable : (prefixWord ++ tailWord_7638281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638281).length < 2 ^ (prefixWord ++ tailWord_7638281).sum := by decide
  have hdescent : baseEnd_7638281 < baseStart_7638281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638298 : List Nat := [3, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4]
def baseStart_7638298 : Nat := 118140960795 + 7638298 * 2 ^ 59
def prefixEnd_7638298 : Nat := 4983230072969 + 3 ^ 40 * 7638298 * 2
def baseEnd_7638298 : Nat := 3922118256276261357647113

theorem tailTrace_7638298 : CollatzResearch.WordTrace tailWord_7638298 prefixEnd_7638298 3922118256276261357647113 := by
  unfold tailWord_7638298
  simp only [CollatzResearch.WordTrace]
  refine ⟨69647903820439584571392887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185727743521172225523714365 69647903820439584571392887)
  ·
    refine ⟨104471855730659376857089331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69647903820439584571392887 104471855730659376857089331)
    ·
      refine ⟨156707783595989065285633997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104471855730659376857089331 156707783595989065285633997)
      ·
        refine ⟨58765418848495899482112749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156707783595989065285633997 58765418848495899482112749)
        ·
          refine ⟨22037032068185962305792281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58765418848495899482112749 22037032068185962305792281)
          ·
            refine ⟨16527774051139471729344211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22037032068185962305792281 16527774051139471729344211)
            ·
              refine ⟨24791661076709207594016317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16527774051139471729344211 24791661076709207594016317)
              ·
                refine ⟨9296872903765952847756119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24791661076709207594016317 9296872903765952847756119)
                ·
                  refine ⟨13945309355648929271634179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9296872903765952847756119 13945309355648929271634179)
                  ·
                    refine ⟨20917964033473393907451269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13945309355648929271634179 20917964033473393907451269)
                    ·
                      refine ⟨3922118256276261357647113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20917964033473393907451269 3922118256276261357647113)
                      ·
                        rfl

theorem cell23_7638298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_7638298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638298 prefixEnd_7638298 := by exact prefixLift 7638298
  have htrace : WordTrace (prefixWord ++ tailWord_7638298) baseStart_7638298 baseEnd_7638298 := by
    simpa [prefixWord, tailWord_7638298, baseEnd_7638298] using wordTrace_append hprefix tailTrace_7638298
  have hstable : (prefixWord ++ tailWord_7638298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638298).length < 2 ^ (prefixWord ++ tailWord_7638298).sum := by decide
  have hdescent : baseEnd_7638298 < baseStart_7638298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638325 : List Nat := [1, 3, 3, 1, 2, 3, 3, 1, 2, 4]
def baseStart_7638325 : Nat := 118140960795 + 7638325 * 2 ^ 59
def prefixEnd_7638325 : Nat := 4983230072969 + 3 ^ 40 * 7638325 * 2
def baseEnd_7638325 : Nat := 1307377373417977584003163

theorem tailTrace_7638325 : CollatzResearch.WordTrace tailWord_7638325 prefixEnd_7638325 1307377373417977584003163 := by
  unfold tailWord_7638325
  simp only [CollatzResearch.WordTrace]
  refine ⟨278592600052660521896804429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185728400035107014597869619 278592600052660521896804429)
  ·
    refine ⟨104472225019747695711301661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278592600052660521896804429 104472225019747695711301661)
    ·
      refine ⟨39177084382405385891738123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104472225019747695711301661 39177084382405385891738123)
      ·
        refine ⟨58765626573608078837607185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39177084382405385891738123 58765626573608078837607185)
        ·
          refine ⟨44074219930206059128205389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58765626573608078837607185 44074219930206059128205389)
          ·
            refine ⟨16527832473827272173077021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44074219930206059128205389 16527832473827272173077021)
            ·
              refine ⟨6197937177685227064903883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16527832473827272173077021 6197937177685227064903883)
              ·
                refine ⟨9296905766527840597355825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6197937177685227064903883 9296905766527840597355825)
                ·
                  refine ⟨6972679324895880448016869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9296905766527840597355825 6972679324895880448016869)
                  ·
                    refine ⟨1307377373417977584003163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6972679324895880448016869 1307377373417977584003163)
                    ·
                      rfl

theorem cell23_7638325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_7638325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638325 prefixEnd_7638325 := by exact prefixLift 7638325
  have htrace : WordTrace (prefixWord ++ tailWord_7638325) baseStart_7638325 baseEnd_7638325 := by
    simpa [prefixWord, tailWord_7638325, baseEnd_7638325] using wordTrace_append hprefix tailTrace_7638325
  have hstable : (prefixWord ++ tailWord_7638325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638325).length < 2 ^ (prefixWord ++ tailWord_7638325).sum := by decide
  have hdescent : baseEnd_7638325 < baseStart_7638325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638341 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 2, 7, 2]
def baseStart_7638341 : Nat := 118140960795 + 7638341 * 2 ^ 59
def prefixEnd_7638341 : Nat := 4983230072969 + 3 ^ 40 * 7638341 * 2
def baseEnd_7638341 : Nat := 3922140335944404689409415

theorem tailTrace_7638341 : CollatzResearch.WordTrace tailWord_7638341 prefixEnd_7638341 3922140335944404689409415 := by
  unfold tailWord_7638341
  simp only [CollatzResearch.WordTrace]
  refine ⟨278593183620602556629386877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185728789080401704419591251 278593183620602556629386877)
  ·
    refine ⟨104472443857725958736020079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278593183620602556629386877 104472443857725958736020079)
    ·
      refine ⟨156708665786588938104030119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104472443857725958736020079 156708665786588938104030119)
      ·
        refine ⟨235062998679883407156045179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156708665786588938104030119 235062998679883407156045179)
        ·
          refine ⟨352594498019825110734067769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235062998679883407156045179 352594498019825110734067769)
          ·
            refine ⟨264445873514868833050550827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352594498019825110734067769 264445873514868833050550827)
            ·
              refine ⟨396668810272303249575826241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264445873514868833050550827 396668810272303249575826241)
              ·
                refine ⟨297501607704227437181869681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396668810272303249575826241 297501607704227437181869681)
                ·
                  refine ⟨223126205778170577886402261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297501607704227437181869681 223126205778170577886402261)
                  ·
                    refine ⟨5229520447925872919212553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 223126205778170577886402261 5229520447925872919212553)
                    ·
                      refine ⟨3922140335944404689409415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5229520447925872919212553 3922140335944404689409415)
                      ·
                        rfl

theorem cell23_7638341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 7, 2].length) (baseStart_7638341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638341 prefixEnd_7638341 := by exact prefixLift 7638341
  have htrace : WordTrace (prefixWord ++ tailWord_7638341) baseStart_7638341 baseEnd_7638341 := by
    simpa [prefixWord, tailWord_7638341, baseEnd_7638341] using wordTrace_append hprefix tailTrace_7638341
  have hstable : (prefixWord ++ tailWord_7638341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638341).length < 2 ^ (prefixWord ++ tailWord_7638341).sum := by decide
  have hdescent : baseEnd_7638341 < baseStart_7638341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638348 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 4, 1, 3]
def baseStart_7638348 : Nat := 118140960795 + 7638348 * 2 ^ 59
def prefixEnd_7638348 : Nat := 4983230072969 + 3 ^ 40 * 7638348 * 2
def baseEnd_7638348 : Nat := 3922143930308986162021883

theorem tailTrace_7638348 : CollatzResearch.WordTrace tailWord_7638348 prefixEnd_7638348 3922143930308986162021883 := by
  unfold tailWord_7638348
  simp only [CollatzResearch.WordTrace]
  refine ⟨139296719465788598412445849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185728959287718131216594465 139296719465788598412445849)
  ·
    refine ⟨104472539599341448809334387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139296719465788598412445849 104472539599341448809334387)
    ·
      refine ⟨156708809399012173214001581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104472539599341448809334387 156708809399012173214001581)
      ·
        refine ⟨58765803524629564955250593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156708809399012173214001581 58765803524629564955250593)
        ·
          refine ⟨44074352643472173716437945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58765803524629564955250593 44074352643472173716437945)
          ·
            refine ⟨33055764482604130287328459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44074352643472173716437945 33055764482604130287328459)
            ·
              refine ⟨49583646723906195430992689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33055764482604130287328459 49583646723906195430992689)
              ·
                refine ⟨37187735042929646573244517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49583646723906195430992689 37187735042929646573244517)
                ·
                  refine ⟨6972700320549308732483347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37187735042929646573244517 6972700320549308732483347)
                  ·
                    refine ⟨10459050480823963098725021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6972700320549308732483347 10459050480823963098725021)
                    ·
                      refine ⟨3922143930308986162021883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10459050480823963098725021 3922143930308986162021883)
                      ·
                        rfl

theorem cell23_7638348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_7638348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638348 prefixEnd_7638348 := by exact prefixLift 7638348
  have htrace : WordTrace (prefixWord ++ tailWord_7638348) baseStart_7638348 baseEnd_7638348 := by
    simpa [prefixWord, tailWord_7638348, baseEnd_7638348] using wordTrace_append hprefix tailTrace_7638348
  have hstable : (prefixWord ++ tailWord_7638348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638348).length < 2 ^ (prefixWord ++ tailWord_7638348).sum := by decide
  have hdescent : baseEnd_7638348 < baseStart_7638348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638478 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_7638478 : Nat := 118140960795 + 7638478 * 2 ^ 59
def prefixEnd_7638478 : Nat := 4983230072969 + 3 ^ 40 * 7638478 * 2
def baseEnd_7638478 : Nat := 3922210682794070653396285

theorem tailTrace_7638478 : CollatzResearch.WordTrace tailWord_7638478 prefixEnd_7638478 3922210682794070653396285 := by
  unfold tailWord_7638478
  simp only [CollatzResearch.WordTrace]
  refine ⟨34824772552638278628390511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185732120280737486018082725 34824772552638278628390511)
  ·
    refine ⟨52237158828957417942585767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34824772552638278628390511 52237158828957417942585767)
    ·
      refine ⟨78355738243436126913878651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52237158828957417942585767 78355738243436126913878651)
      ·
        refine ⟨117533607365154190370817977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78355738243436126913878651 117533607365154190370817977)
        ·
          refine ⟨88150205523865642778113483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117533607365154190370817977 88150205523865642778113483)
          ·
            refine ⟨132225308285798464167170225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88150205523865642778113483 132225308285798464167170225)
            ·
              refine ⟨99168981214348848125377669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132225308285798464167170225 99168981214348848125377669)
              ·
                refine ⟨18594183977690409023508313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99168981214348848125377669 18594183977690409023508313)
                ·
                  refine ⟨13945637983267806767631235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18594183977690409023508313 13945637983267806767631235)
                  ·
                    refine ⟨20918456974901710151446853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13945637983267806767631235 20918456974901710151446853)
                    ·
                      refine ⟨3922210682794070653396285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20918456974901710151446853 3922210682794070653396285)
                      ·
                        rfl

theorem cell23_7638478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_7638478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638478 prefixEnd_7638478 := by exact prefixLift 7638478
  have htrace : WordTrace (prefixWord ++ tailWord_7638478) baseStart_7638478 baseEnd_7638478 := by
    simpa [prefixWord, tailWord_7638478, baseEnd_7638478] using wordTrace_append hprefix tailTrace_7638478
  have hstable : (prefixWord ++ tailWord_7638478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638478).length < 2 ^ (prefixWord ++ tailWord_7638478).sum := by decide
  have hdescent : baseEnd_7638478 < baseStart_7638478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638488 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 3, 4]
def baseStart_7638488 : Nat := 118140960795 + 7638488 * 2 ^ 59
def prefixEnd_7638488 : Nat := 4983230072969 + 3 ^ 40 * 7638488 * 2
def baseEnd_7638488 : Nat := 1307405272533538538090413

theorem tailTrace_7638488 : CollatzResearch.WordTrace tailWord_7638488 prefixEnd_7638488 1307405272533538538090413 := by
  unfold tailWord_7638488
  simp only [CollatzResearch.WordTrace]
  refine ⟨139299272575535000367494059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185732363434046667156658745 139299272575535000367494059)
  ·
    refine ⟨208948908863302500551241089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139299272575535000367494059 208948908863302500551241089)
    ·
      refine ⟨156711681647476875413430817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208948908863302500551241089 156711681647476875413430817)
      ·
        refine ⟨117533761235607656560073113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156711681647476875413430817 117533761235607656560073113)
        ·
          refine ⟨88150320926705742420054835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117533761235607656560073113 88150320926705742420054835)
          ·
            refine ⟨132225481390058613630082253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88150320926705742420054835 132225481390058613630082253)
            ·
              refine ⟨49584555521271980111280845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132225481390058613630082253 49584555521271980111280845)
              ·
                refine ⟨18594208320476992541730317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49584555521271980111280845 18594208320476992541730317)
                ·
                  refine ⟨6972828120178872203148869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18594208320476992541730317 6972828120178872203148869)
                  ·
                    refine ⟨1307405272533538538090413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6972828120178872203148869 1307405272533538538090413)
                    ·
                      rfl

theorem cell23_7638488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_7638488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638488 prefixEnd_7638488 := by exact prefixLift 7638488
  have htrace : WordTrace (prefixWord ++ tailWord_7638488) baseStart_7638488 baseEnd_7638488 := by
    simpa [prefixWord, tailWord_7638488, baseEnd_7638488] using wordTrace_append hprefix tailTrace_7638488
  have hstable : (prefixWord ++ tailWord_7638488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638488).length < 2 ^ (prefixWord ++ tailWord_7638488).sum := by decide
  have hdescent : baseEnd_7638488 < baseStart_7638488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638518 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_7638518 : Nat := 118140960795 + 7638518 * 2 ^ 59
def prefixEnd_7638518 : Nat := 4983230072969 + 3 ^ 40 * 7638518 * 2
def baseEnd_7638518 : Nat := 435803469113361166321789

theorem tailTrace_7638518 : CollatzResearch.WordTrace tailWord_7638518 prefixEnd_7638518 435803469113361166321789 := by
  unfold tailWord_7638518
  simp only [CollatzResearch.WordTrace]
  refine ⟨17412477458810082241161263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185733092893974210572386805 17412477458810082241161263)
  ·
    refine ⟨26118716188215123361741895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17412477458810082241161263 26118716188215123361741895)
    ·
      refine ⟨39178074282322685042612843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26118716188215123361741895 39178074282322685042612843)
      ·
        refine ⟨58767111423484027563919265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39178074282322685042612843 58767111423484027563919265)
        ·
          refine ⟨44075333567613020672939449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58767111423484027563919265 44075333567613020672939449)
          ·
            refine ⟨33056500175709765504704587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44075333567613020672939449 33056500175709765504704587)
            ·
              refine ⟨49584750263564648257056881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33056500175709765504704587 49584750263564648257056881)
              ·
                refine ⟨37188562697673486192792661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49584750263564648257056881 37188562697673486192792661)
                ·
                  refine ⟨435803469113361166321789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37188562697673486192792661 435803469113361166321789)
                  ·
                    rfl

theorem cell23_7638518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_7638518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638518 prefixEnd_7638518 := by exact prefixLift 7638518
  have htrace : WordTrace (prefixWord ++ tailWord_7638518) baseStart_7638518 baseEnd_7638518 := by
    simpa [prefixWord, tailWord_7638518, baseEnd_7638518] using wordTrace_append hprefix tailTrace_7638518
  have hstable : (prefixWord ++ tailWord_7638518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638518).length < 2 ^ (prefixWord ++ tailWord_7638518).sum := by decide
  have hdescent : baseEnd_7638518 < baseStart_7638518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638532 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_7638532 : Nat := 118140960795 + 7638532 * 2 ^ 59
def prefixEnd_7638532 : Nat := 4983230072969 + 3 ^ 40 * 7638532 * 2
def baseEnd_7638532 : Nat := 3922238410749413442121037

theorem tailTrace_7638532 : CollatzResearch.WordTrace tailWord_7638532 prefixEnd_7638532 3922238410749413442121037 := by
  unfold tailWord_7638532
  simp only [CollatzResearch.WordTrace]
  refine ⟨139300074981455298124794925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185733433308607064166393233 139300074981455298124794925)
  ·
    refine ⟨52237528118045736796798097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139300074981455298124794925 52237528118045736796798097)
    ·
      refine ⟨39178146088534302597598573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52237528118045736796798097 39178146088534302597598573)
      ·
        refine ⟨14691804783200363474099465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39178146088534302597598573 14691804783200363474099465)
        ·
          refine ⟨11018853587400272605574599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14691804783200363474099465 11018853587400272605574599)
          ·
            refine ⟨16528280381100408908361899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11018853587400272605574599 16528280381100408908361899)
            ·
              refine ⟨24792420571650613362542849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16528280381100408908361899 24792420571650613362542849)
              ·
                refine ⟨18594315428737960021907137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24792420571650613362542849 18594315428737960021907137)
                ·
                  refine ⟨13945736571553470016430353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18594315428737960021907137 13945736571553470016430353)
                  ·
                    refine ⟨10459302428665102512322765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13945736571553470016430353 10459302428665102512322765)
                    ·
                      refine ⟨3922238410749413442121037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10459302428665102512322765 3922238410749413442121037)
                      ·
                        rfl

theorem cell23_7638532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_7638532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638532 prefixEnd_7638532 := by exact prefixLift 7638532
  have htrace : WordTrace (prefixWord ++ tailWord_7638532) baseStart_7638532 baseEnd_7638532 := by
    simpa [prefixWord, tailWord_7638532, baseEnd_7638532] using wordTrace_append hprefix tailTrace_7638532
  have hstable : (prefixWord ++ tailWord_7638532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638532).length < 2 ^ (prefixWord ++ tailWord_7638532).sum := by decide
  have hdescent : baseEnd_7638532 < baseStart_7638532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638539 : List Nat := [1, 1, 1, 1, 8, 1, 3, 2, 1, 4]
def baseStart_7638539 : Nat := 118140960795 + 7638539 * 2 ^ 59
def prefixEnd_7638539 : Nat := 4983230072969 + 3 ^ 40 * 7638539 * 2
def baseEnd_7638539 : Nat := 1307414001704664971577835

theorem tailTrace_7638539 : CollatzResearch.WordTrace tailWord_7638539 prefixEnd_7638539 1307414001704664971577835 := by
  unfold tailWord_7638539
  simp only [CollatzResearch.WordTrace]
  refine ⟨278600405273885236445094671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185733603515923490963396447 278600405273885236445094671)
  ·
    refine ⟨417900607910827854667642007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278600405273885236445094671 417900607910827854667642007)
    ·
      refine ⟨626850911866241782001463011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417900607910827854667642007 626850911866241782001463011)
      ·
        refine ⟨940276367799362673002194517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626850911866241782001463011 940276367799362673002194517)
        ·
          refine ⟨11018863685148781324244467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 940276367799362673002194517 11018863685148781324244467)
          ·
            refine ⟨16528295527723171986366701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11018863685148781324244467 16528295527723171986366701)
            ·
              refine ⟨6198110822896189494887513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16528295527723171986366701 6198110822896189494887513)
              ·
                refine ⟨4648583117172142121165635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6198110822896189494887513 4648583117172142121165635)
                ·
                  refine ⟨6972874675758213181748453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4648583117172142121165635 6972874675758213181748453)
                  ·
                    refine ⟨1307414001704664971577835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6972874675758213181748453 1307414001704664971577835)
                    ·
                      rfl

theorem cell23_7638539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 1, 4].length) (baseStart_7638539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638539 prefixEnd_7638539 := by exact prefixLift 7638539
  have htrace : WordTrace (prefixWord ++ tailWord_7638539) baseStart_7638539 baseEnd_7638539 := by
    simpa [prefixWord, tailWord_7638539, baseEnd_7638539] using wordTrace_append hprefix tailTrace_7638539
  have hstable : (prefixWord ++ tailWord_7638539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638539).length < 2 ^ (prefixWord ++ tailWord_7638539).sum := by decide
  have hdescent : baseEnd_7638539 < baseStart_7638539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638552 : List Nat := [2, 1, 2, 3, 4, 2, 2, 1, 6]
def baseStart_7638552 : Nat := 118140960795 + 7638552 * 2 ^ 59
def prefixEnd_7638552 : Nat := 4983230072969 + 3 ^ 40 * 7638552 * 2
def baseEnd_7638552 : Nat := 435805408929167040430105

theorem tailTrace_7638552 : CollatzResearch.WordTrace tailWord_7638552 prefixEnd_7638552 435805408929167040430105 := by
  unfold tailWord_7638552
  simp only [CollatzResearch.WordTrace]
  refine ⟨139300439711419069832658955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185733919615225426443545273 139300439711419069832658955)
  ·
    refine ⟨208950659567128604748988433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139300439711419069832658955 208950659567128604748988433)
    ·
      refine ⟨156712994675346453561741325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208950659567128604748988433 156712994675346453561741325)
      ·
        refine ⟨58767373003254920085652997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156712994675346453561741325 58767373003254920085652997)
        ·
          refine ⟨11018882438110297516059937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58767373003254920085652997 11018882438110297516059937)
          ·
            refine ⟨8264161828582723137044953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11018882438110297516059937 8264161828582723137044953)
            ·
              refine ⟨6198121371437042352783715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8264161828582723137044953 6198121371437042352783715)
              ·
                refine ⟨9297182057155563529175573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6198121371437042352783715 9297182057155563529175573)
                ·
                  refine ⟨435805408929167040430105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9297182057155563529175573 435805408929167040430105)
                  ·
                    rfl

theorem cell23_7638552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 6].length) (baseStart_7638552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638552 prefixEnd_7638552 := by exact prefixLift 7638552
  have htrace : WordTrace (prefixWord ++ tailWord_7638552) baseStart_7638552 baseEnd_7638552 := by
    simpa [prefixWord, tailWord_7638552, baseEnd_7638552] using wordTrace_append hprefix tailTrace_7638552
  have hstable : (prefixWord ++ tailWord_7638552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638552).length < 2 ^ (prefixWord ++ tailWord_7638552).sum := by decide
  have hdescent : baseEnd_7638552 < baseStart_7638552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638571 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 5]
def baseStart_7638571 : Nat := 118140960795 + 7638571 * 2 ^ 59
def prefixEnd_7638571 : Nat := 4983230072969 + 3 ^ 40 * 7638571 * 2
def baseEnd_7638571 : Nat := 3922258436494938789533357

theorem tailTrace_7638571 : CollatzResearch.WordTrace tailWord_7638571 prefixEnd_7638571 3922258436494938789533357 := by
  unfold tailWord_7638571
  simp only [CollatzResearch.WordTrace]
  refine ⟨278601572409769305910259567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185734381606512870606839711 278601572409769305910259567)
  ·
    refine ⟨417902358614653958865389351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278601572409769305910259567 417902358614653958865389351)
    ·
      refine ⟨626853537921980938298084027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417902358614653958865389351 626853537921980938298084027)
      ·
        refine ⟨940280306882971407447126041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626853537921980938298084027 940280306882971407447126041)
        ·
          refine ⟨705210230162228555585344531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 940280306882971407447126041 705210230162228555585344531)
          ·
            refine ⟨1057815345243342833378016797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705210230162228555585344531 1057815345243342833378016797)
            ·
              refine ⟨396680754466253562516756299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1057815345243342833378016797 396680754466253562516756299)
              ·
                refine ⟨595021131699380343775134449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396680754466253562516756299 595021131699380343775134449)
                ·
                  refine ⟨446265848774535257831350837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595021131699380343775134449 446265848774535257831350837)
                  ·
                    refine ⟨41837423322612680421689141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 446265848774535257831350837 41837423322612680421689141)
                    ·
                      refine ⟨3922258436494938789533357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41837423322612680421689141 3922258436494938789533357)
                      ·
                        rfl

theorem cell23_7638571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 5].length) (baseStart_7638571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638571 prefixEnd_7638571 := by exact prefixLift 7638571
  have htrace : WordTrace (prefixWord ++ tailWord_7638571) baseStart_7638571 baseEnd_7638571 := by
    simpa [prefixWord, tailWord_7638571, baseEnd_7638571] using wordTrace_append hprefix tailTrace_7638571
  have hstable : (prefixWord ++ tailWord_7638571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638571).length < 2 ^ (prefixWord ++ tailWord_7638571).sum := by decide
  have hdescent : baseEnd_7638571 < baseStart_7638571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638591 : List Nat := [1, 1, 2, 2, 3, 14]
def baseStart_7638591 : Nat := 118140960795 + 7638591 * 2 ^ 59
def prefixEnd_7638591 : Nat := 4983230072969 + 3 ^ 40 * 7638591 * 2
def baseEnd_7638591 : Nat := 16141023481926044079355

theorem tailTrace_7638591 : CollatzResearch.WordTrace tailWord_7638591 prefixEnd_7638591 16141023481926044079355 := by
  unfold tailWord_7638591
  simp only [CollatzResearch.WordTrace]
  refine ⟨278602301869696849325987627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185734867913131232883991751 278602301869696849325987627)
  ·
    refine ⟨417903452804545273988981441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278602301869696849325987627 417903452804545273988981441)
    ·
      refine ⟨313427589603408955491736081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417903452804545273988981441 313427589603408955491736081)
      ·
        refine ⟨235070692202556716618802061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313427589603408955491736081 235070692202556716618802061)
        ·
          refine ⟨88151509575958768732050773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235070692202556716618802061 88151509575958768732050773)
          ·
            refine ⟨16141023481926044079355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 88151509575958768732050773 16141023481926044079355)
            ·
              rfl

theorem cell23_7638591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 14].length) (baseStart_7638591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638591 prefixEnd_7638591 := by exact prefixLift 7638591
  have htrace : WordTrace (prefixWord ++ tailWord_7638591) baseStart_7638591 baseEnd_7638591 := by
    simpa [prefixWord, tailWord_7638591, baseEnd_7638591] using wordTrace_append hprefix tailTrace_7638591
  have hstable : (prefixWord ++ tailWord_7638591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638591).length < 2 ^ (prefixWord ++ tailWord_7638591).sum := by decide
  have hdescent : baseEnd_7638591 < baseStart_7638591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638602 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 3, 2, 2]
def baseStart_7638602 : Nat := 118140960795 + 7638602 * 2 ^ 59
def prefixEnd_7638602 : Nat := 4983230072969 + 3 ^ 40 * 7638602 * 2
def baseEnd_7638602 : Nat := 3922274354395228168245715

theorem tailTrace_7638602 : CollatzResearch.WordTrace tailWord_7638602 prefixEnd_7638602 3922274354395228168245715 := by
  unfold tailWord_7638602
  simp only [CollatzResearch.WordTrace]
  refine ⟨69650675768164249551159515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185735135381771332136425373 69650675768164249551159515)
  ·
    refine ⟨104476013652246374326739273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69650675768164249551159515 104476013652246374326739273)
    ·
      refine ⟨78357010239184780745054455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104476013652246374326739273 78357010239184780745054455)
      ·
        refine ⟨117535515358777171117581683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78357010239184780745054455 117535515358777171117581683)
        ·
          refine ⟨176303273038165756676372525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117535515358777171117581683 176303273038165756676372525)
          ·
            refine ⟨66113727389312158753639697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176303273038165756676372525 66113727389312158753639697)
            ·
              refine ⟨49585295541984119065229773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66113727389312158753639697 49585295541984119065229773)
              ·
                refine ⟨18594485828244044649461165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49585295541984119065229773 18594485828244044649461165)
                ·
                  refine ⟨6972932185591516743547937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18594485828244044649461165 6972932185591516743547937)
                  ·
                    refine ⟨5229699139193637557660953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6972932185591516743547937 5229699139193637557660953)
                    ·
                      refine ⟨3922274354395228168245715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5229699139193637557660953 3922274354395228168245715)
                      ·
                        rfl

theorem cell23_7638602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_7638602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638602 prefixEnd_7638602 := by exact prefixLift 7638602
  have htrace : WordTrace (prefixWord ++ tailWord_7638602) baseStart_7638602 baseEnd_7638602 := by
    simpa [prefixWord, tailWord_7638602, baseEnd_7638602] using wordTrace_append hprefix tailTrace_7638602
  have hstable : (prefixWord ++ tailWord_7638602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638602).length < 2 ^ (prefixWord ++ tailWord_7638602).sum := by decide
  have hdescent : baseEnd_7638602 < baseStart_7638602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638615 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 4]
def baseStart_7638615 : Nat := 118140960795 + 7638615 * 2 ^ 59
def prefixEnd_7638615 : Nat := 4983230072969 + 3 ^ 40 * 7638615 * 2
def baseEnd_7638615 : Nat := 3922281029643736617383155

theorem tailTrace_7638615 : CollatzResearch.WordTrace tailWord_7638615 prefixEnd_7638615 3922281029643736617383155 := by
  unfold tailWord_7638615
  simp only [CollatzResearch.WordTrace]
  refine ⟨278603177221609901424861299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185735451481073267616574199 278603177221609901424861299)
  ·
    refine ⟨417904765832414852137291949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278603177221609901424861299 417904765832414852137291949)
    ·
      refine ⟨156714287187155569551484481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417904765832414852137291949 156714287187155569551484481)
      ·
        refine ⟨117535715390366677163613361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156714287187155569551484481 117535715390366677163613361)
        ·
          refine ⟨88151786542775007872710021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117535715390366677163613361 88151786542775007872710021)
          ·
            refine ⟨16528459976770313976133129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88151786542775007872710021 16528459976770313976133129)
            ·
              refine ⟨12396344982577735482099847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16528459976770313976133129 12396344982577735482099847)
              ·
                refine ⟨18594517473866603223149771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12396344982577735482099847 18594517473866603223149771)
                ·
                  refine ⟨27891776210799904834724657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18594517473866603223149771 27891776210799904834724657)
                  ·
                    refine ⟨20918832158099928626043493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27891776210799904834724657 20918832158099928626043493)
                    ·
                      refine ⟨3922281029643736617383155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20918832158099928626043493 3922281029643736617383155)
                      ·
                        rfl

theorem cell23_7638615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_7638615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638615 prefixEnd_7638615 := by exact prefixLift 7638615
  have htrace : WordTrace (prefixWord ++ tailWord_7638615) baseStart_7638615 baseEnd_7638615 := by
    simpa [prefixWord, tailWord_7638615, baseEnd_7638615] using wordTrace_append hprefix tailTrace_7638615
  have hstable : (prefixWord ++ tailWord_7638615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638615).length < 2 ^ (prefixWord ++ tailWord_7638615).sum := by decide
  have hdescent : baseEnd_7638615 < baseStart_7638615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638668 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 2, 6]
def baseStart_7638668 : Nat := 118140960795 + 7638668 * 2 ^ 59
def prefixEnd_7638668 : Nat := 4983230072969 + 3 ^ 40 * 7638668 * 2
def baseEnd_7638668 : Nat := 1307436081372808303340137

theorem tailTrace_7638668 : CollatzResearch.WordTrace tailWord_7638668 prefixEnd_7638668 1307436081372808303340137 := by
  unfold tailWord_7638668
  simp only [CollatzResearch.WordTrace]
  refine ⟨139302555145208945738270329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185736740193611927651027105 139302555145208945738270329)
  ·
    refine ⟨104476916358906709303702747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139302555145208945738270329 104476916358906709303702747)
    ·
      refine ⟨156715374538360063955554121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104476916358906709303702747 156715374538360063955554121)
      ·
        refine ⟨117536530903770047966665591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156715374538360063955554121 117536530903770047966665591)
        ·
          refine ⟨176304796355655071949998387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117536530903770047966665591 176304796355655071949998387)
          ·
            refine ⟨264457194533482607924997581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176304796355655071949998387 264457194533482607924997581)
            ·
              refine ⟨99171447950055977971874093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264457194533482607924997581 99171447950055977971874093)
              ·
                refine ⟨37189292981270991739452785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99171447950055977971874093 37189292981270991739452785)
                ·
                  refine ⟨27891969735953243804589589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37189292981270991739452785 27891969735953243804589589)
                  ·
                    refine ⟨1307436081372808303340137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27891969735953243804589589 1307436081372808303340137)
                    ·
                      rfl

theorem cell23_7638668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_7638668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638668 prefixEnd_7638668 := by exact prefixLift 7638668
  have htrace : WordTrace (prefixWord ++ tailWord_7638668) baseStart_7638668 baseEnd_7638668 := by
    simpa [prefixWord, tailWord_7638668, baseEnd_7638668] using wordTrace_append hprefix tailTrace_7638668
  have hstable : (prefixWord ++ tailWord_7638668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638668).length < 2 ^ (prefixWord ++ tailWord_7638668).sum := by decide
  have hdescent : baseEnd_7638668 < baseStart_7638668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638679 : List Nat := [1, 1, 3, 3, 2, 3, 2, 2, 1, 3, 2]
def baseStart_7638679 : Nat := 118140960795 + 7638679 * 2 ^ 59
def prefixEnd_7638679 : Nat := 4983230072969 + 3 ^ 40 * 7638679 * 2
def baseEnd_7638679 : Nat := 3922313892405624366982861

theorem tailTrace_7638679 : CollatzResearch.WordTrace tailWord_7638679 prefixEnd_7638679 3922313892405624366982861 := by
  unfold tailWord_7638679
  simp only [CollatzResearch.WordTrace]
  refine ⟨278605511493378040355191091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185737007662252026903460727 278605511493378040355191091)
  ·
    refine ⟨417908267240067060532786637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278605511493378040355191091 417908267240067060532786637)
    ·
      refine ⟨156715600215025147699794989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417908267240067060532786637 156715600215025147699794989)
      ·
        refine ⟨58768350080634430387423121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156715600215025147699794989 58768350080634430387423121)
        ·
          refine ⟨44076262560475822790567341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58768350080634430387423121 44076262560475822790567341)
          ·
            refine ⟨16528598460178433546462753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44076262560475822790567341 16528598460178433546462753)
            ·
              refine ⟨12396448845133825159847065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16528598460178433546462753 12396448845133825159847065)
              ·
                refine ⟨9297336633850368869885299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12396448845133825159847065 9297336633850368869885299)
                ·
                  refine ⟨13946004950775553304827949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9297336633850368869885299 13946004950775553304827949)
                  ·
                    refine ⟨5229751856540832489310481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13946004950775553304827949 5229751856540832489310481)
                    ·
                      refine ⟨3922313892405624366982861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5229751856540832489310481 3922313892405624366982861)
                      ·
                        rfl

theorem cell23_7638679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_7638679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638679 prefixEnd_7638679 := by exact prefixLift 7638679
  have htrace : WordTrace (prefixWord ++ tailWord_7638679) baseStart_7638679 baseEnd_7638679 := by
    simpa [prefixWord, tailWord_7638679, baseEnd_7638679] using wordTrace_append hprefix tailTrace_7638679
  have hstable : (prefixWord ++ tailWord_7638679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638679).length < 2 ^ (prefixWord ++ tailWord_7638679).sum := by decide
  have hdescent : baseEnd_7638679 < baseStart_7638679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638715 : List Nat := [1, 1, 1, 1, 1, 2, 3, 8, 5]
def baseStart_7638715 : Nat := 118140960795 + 7638715 * 2 ^ 59
def prefixEnd_7638715 : Nat := 4983230072969 + 3 ^ 40 * 7638715 * 2
def baseEnd_7638715 : Nat := 435814708634354025125855

theorem tailTrace_7638715 : CollatzResearch.WordTrace tailWord_7638715 prefixEnd_7638715 435814708634354025125855 := by
  unfold tailWord_7638715
  simp only [CollatzResearch.WordTrace]
  refine ⟨278606824521247618503501599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185737883014165079002334399 278606824521247618503501599)
  ·
    refine ⟨417910236781871427755252399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278606824521247618503501599 417910236781871427755252399)
    ·
      refine ⟨626865355172807141632878599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417910236781871427755252399 626865355172807141632878599)
      ·
        refine ⟨940298032759210712449317899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626865355172807141632878599 940298032759210712449317899)
        ·
          refine ⟨1410447049138816068673976849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940298032759210712449317899 1410447049138816068673976849)
          ·
            refine ⟨1057835286854112051505482637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1410447049138816068673976849 1057835286854112051505482637)
            ·
              refine ⟨396688232570292019314555989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1057835286854112051505482637 396688232570292019314555989)
              ·
                refine ⟨4648690225433109601342453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 396688232570292019314555989 4648690225433109601342453)
                ·
                  refine ⟨435814708634354025125855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4648690225433109601342453 435814708634354025125855)
                  ·
                    rfl

theorem cell23_7638715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 5].length) (baseStart_7638715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638715 prefixEnd_7638715 := by exact prefixLift 7638715
  have htrace : WordTrace (prefixWord ++ tailWord_7638715) baseStart_7638715 baseEnd_7638715 := by
    simpa [prefixWord, tailWord_7638715, baseEnd_7638715] using wordTrace_append hprefix tailTrace_7638715
  have hstable : (prefixWord ++ tailWord_7638715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638715).length < 2 ^ (prefixWord ++ tailWord_7638715).sum := by decide
  have hdescent : baseEnd_7638715 < baseStart_7638715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638745 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 2, 5]
def baseStart_7638745 : Nat := 118140960795 + 7638745 * 2 ^ 59
def prefixEnd_7638745 : Nat := 4983230072969 + 3 ^ 40 * 7638745 * 2
def baseEnd_7638745 : Nat := 1307449260709607036252519

theorem tailTrace_7638745 : CollatzResearch.WordTrace tailWord_7638745 prefixEnd_7638745 1307449260709607036252519 := by
  unfold tailWord_7638745
  simp only [CollatzResearch.WordTrace]
  refine ⟨278607918711138933627093689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185738612474092622418062459 278607918711138933627093689)
  ·
    refine ⟨208955939033354200220320267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278607918711138933627093689 208955939033354200220320267)
    ·
      refine ⟨313433908550031300330480401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208955939033354200220320267 313433908550031300330480401)
      ·
        refine ⟨235075431412523475247860301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313433908550031300330480401 235075431412523475247860301)
        ·
          refine ⟨88153286779696303217947613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235075431412523475247860301 88153286779696303217947613)
          ·
            refine ⟨33057482542386113706730355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88153286779696303217947613 33057482542386113706730355)
            ·
              refine ⟨49586223813579170560095533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33057482542386113706730355 49586223813579170560095533)
              ·
                refine ⟨18594833930092188960035825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49586223813579170560095533 18594833930092188960035825)
                ·
                  refine ⟨13946125447569141720026869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18594833930092188960035825 13946125447569141720026869)
                  ·
                    refine ⟨1307449260709607036252519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13946125447569141720026869 1307449260709607036252519)
                    ·
                      rfl

theorem cell23_7638745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 5].length) (baseStart_7638745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638745 prefixEnd_7638745 := by exact prefixLift 7638745
  have htrace : WordTrace (prefixWord ++ tailWord_7638745) baseStart_7638745 baseEnd_7638745 := by
    simpa [prefixWord, tailWord_7638745, baseEnd_7638745] using wordTrace_append hprefix tailTrace_7638745
  have hstable : (prefixWord ++ tailWord_7638745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638745).length < 2 ^ (prefixWord ++ tailWord_7638745).sum := by decide
  have hdescent : baseEnd_7638745 < baseStart_7638745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638792 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 3, 4]
def baseStart_7638792 : Nat := 118140960795 + 7638792 * 2 ^ 59
def prefixEnd_7638792 : Nat := 4983230072969 + 3 ^ 40 * 7638792 * 2
def baseEnd_7638792 : Nat := 1307457305239860808289947

theorem tailTrace_7638792 : CollatzResearch.WordTrace tailWord_7638792 prefixEnd_7638792 1307457305239860808289947 := by
  unfold tailWord_7638792
  simp only [CollatzResearch.WordTrace]
  refine ⟨139304816470984330327027315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185739755294645773769369753 139304816470984330327027315)
  ·
    refine ⟨208957224706476495490540973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139304816470984330327027315 208957224706476495490540973)
    ·
      refine ⟨78358959264928685808952865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208957224706476495490540973 78358959264928685808952865)
      ·
        refine ⟨58769219448696514356714649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78358959264928685808952865 58769219448696514356714649)
        ·
          refine ⟨44076914586522385767535987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58769219448696514356714649 44076914586522385767535987)
          ·
            refine ⟨66115371879783578651303981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44076914586522385767535987 66115371879783578651303981)
            ·
              refine ⟨24793264454918841994238993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66115371879783578651303981 24793264454918841994238993)
              ·
                refine ⟨18594948341189131495679245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24793264454918841994238993 18594948341189131495679245)
                ·
                  refine ⟨6973105627945924310879717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18594948341189131495679245 6973105627945924310879717)
                  ·
                    refine ⟨1307457305239860808289947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6973105627945924310879717 1307457305239860808289947)
                    ·
                      rfl

theorem cell23_7638792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_7638792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638792 prefixEnd_7638792 := by exact prefixLift 7638792
  have htrace : WordTrace (prefixWord ++ tailWord_7638792) baseStart_7638792 baseEnd_7638792 := by
    simpa [prefixWord, tailWord_7638792, baseEnd_7638792] using wordTrace_append hprefix tailTrace_7638792
  have hstable : (prefixWord ++ tailWord_7638792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638792).length < 2 ^ (prefixWord ++ tailWord_7638792).sum := by decide
  have hdescent : baseEnd_7638792 < baseStart_7638792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638883 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 3, 1, 3]
def baseStart_7638883 : Nat := 118140960795 + 7638883 * 2 ^ 59
def prefixEnd_7638883 : Nat := 4983230072969 + 3 ^ 40 * 7638883 * 2
def baseEnd_7638883 : Nat := 3922418642459141568831923

theorem tailTrace_7638883 : CollatzResearch.WordTrace tailWord_7638883 prefixEnd_7638883 3922418642459141568831923 := by
  unfold tailWord_7638883
  simp only [CollatzResearch.WordTrace]
  refine ⟨278612951984638983195617303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185741967989759322130411535 278612951984638983195617303)
  ·
    refine ⟨417919427976958474793425955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278612951984638983195617303 417919427976958474793425955)
    ·
      refine ⟨626879141965437712190138933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417919427976958474793425955 626879141965437712190138933)
      ·
        refine ⟨58769919559259785517825525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 626879141965437712190138933 58769919559259785517825525)
        ·
          refine ⟨5509679958680604892296143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58769919559259785517825525 5509679958680604892296143)
          ·
            refine ⟨8264519938020907338444215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5509679958680604892296143 8264519938020907338444215)
            ·
              refine ⟨12396779907031361007666323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8264519938020907338444215 12396779907031361007666323)
              ·
                refine ⟨18595169860547041511499485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12396779907031361007666323 18595169860547041511499485)
                ·
                  refine ⟨6973188697705140566812307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18595169860547041511499485 6973188697705140566812307)
                  ·
                    refine ⟨10459783046557710850218461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6973188697705140566812307 10459783046557710850218461)
                    ·
                      refine ⟨3922418642459141568831923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10459783046557710850218461 3922418642459141568831923)
                      ·
                        rfl

theorem cell23_7638883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_7638883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638883 prefixEnd_7638883 := by exact prefixLift 7638883
  have htrace : WordTrace (prefixWord ++ tailWord_7638883) baseStart_7638883 baseEnd_7638883 := by
    simpa [prefixWord, tailWord_7638883, baseEnd_7638883] using wordTrace_append hprefix tailTrace_7638883
  have hstable : (prefixWord ++ tailWord_7638883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638883).length < 2 ^ (prefixWord ++ tailWord_7638883).sum := by decide
  have hdescent : baseEnd_7638883 < baseStart_7638883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638892 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 5]
def baseStart_7638892 : Nat := 118140960795 + 7638892 * 2 ^ 59
def prefixEnd_7638892 : Nat := 4983230072969 + 3 ^ 40 * 7638892 * 2
def baseEnd_7638892 : Nat := 3922423263785032033619381

theorem tailTrace_7638892 : CollatzResearch.WordTrace tailWord_7638892 prefixEnd_7638892 3922423263785032033619381 := by
  unfold tailWord_7638892
  simp only [CollatzResearch.WordTrace]
  refine ⟨139306640120803188866347465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185742186827737585155129953 139306640120803188866347465)
  ·
    refine ⟨104479980090602391649760599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139306640120803188866347465 104479980090602391649760599)
    ·
      refine ⟨156719970135903587474640899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104479980090602391649760599 156719970135903587474640899)
      ·
        refine ⟨235079955203855381211961349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156719970135903587474640899 235079955203855381211961349)
        ·
          refine ⟨44077491600722883977242753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235079955203855381211961349 44077491600722883977242753)
          ·
            refine ⟨33058118700542162982932065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44077491600722883977242753 33058118700542162982932065)
            ·
              refine ⟨24793589025406622237199049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33058118700542162982932065 24793589025406622237199049)
              ·
                refine ⟨18595191769054966677899287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24793589025406622237199049 18595191769054966677899287)
                ·
                  refine ⟨27892787653582450016848931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18595191769054966677899287 27892787653582450016848931)
                  ·
                    refine ⟨41839181480373675025273397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27892787653582450016848931 41839181480373675025273397)
                    ·
                      refine ⟨3922423263785032033619381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41839181480373675025273397 3922423263785032033619381)
                      ·
                        rfl

theorem cell23_7638892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_7638892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638892 prefixEnd_7638892 := by exact prefixLift 7638892
  have htrace : WordTrace (prefixWord ++ tailWord_7638892) baseStart_7638892 baseEnd_7638892 := by
    simpa [prefixWord, tailWord_7638892, baseEnd_7638892] using wordTrace_append hprefix tailTrace_7638892
  have hstable : (prefixWord ++ tailWord_7638892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638892).length < 2 ^ (prefixWord ++ tailWord_7638892).sum := by decide
  have hdescent : baseEnd_7638892 < baseStart_7638892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638919 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 4]
def baseStart_7638919 : Nat := 118140960795 + 7638919 * 2 ^ 59
def prefixEnd_7638919 : Nat := 4983230072969 + 3 ^ 40 * 7638919 * 2
def baseEnd_7638919 : Nat := 3922437127762703427981757

theorem tailTrace_7638919 : CollatzResearch.WordTrace tailWord_7638919 prefixEnd_7638919 3922437127762703427981757 := by
  unfold tailWord_7638919
  simp only [CollatzResearch.WordTrace]
  refine ⟨278614265012508561343927811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185742843341672374229285207 278614265012508561343927811)
  ·
    refine ⟨417921397518762842015891717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278614265012508561343927811 417921397518762842015891717)
    ·
      refine ⟨78360262034768032877979697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417921397518762842015891717 78360262034768032877979697)
      ·
        refine ⟨58770196526076024658484773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78360262034768032877979697 58770196526076024658484773)
        ·
          refine ⟨11019411848639254623465895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58770196526076024658484773 11019411848639254623465895)
          ·
            refine ⟨16529117772958881935198843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11019411848639254623465895 16529117772958881935198843)
            ·
              refine ⟨24793676659438322902798265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16529117772958881935198843 24793676659438322902798265)
              ·
                refine ⟨18595257494578742177098699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24793676659438322902798265 18595257494578742177098699)
                ·
                  refine ⟨27892886241868113265648049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18595257494578742177098699 27892886241868113265648049)
                  ·
                    refine ⟨20919664681401084949236037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27892886241868113265648049 20919664681401084949236037)
                    ·
                      refine ⟨3922437127762703427981757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20919664681401084949236037 3922437127762703427981757)
                      ·
                        rfl

theorem cell23_7638919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_7638919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638919 prefixEnd_7638919 := by exact prefixLift 7638919
  have htrace : WordTrace (prefixWord ++ tailWord_7638919) baseStart_7638919 baseEnd_7638919 := by
    simpa [prefixWord, tailWord_7638919, baseEnd_7638919] using wordTrace_append hprefix tailTrace_7638919
  have hstable : (prefixWord ++ tailWord_7638919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638919).length < 2 ^ (prefixWord ++ tailWord_7638919).sum := by decide
  have hdescent : baseEnd_7638919 < baseStart_7638919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638940 : List Nat := [2, 2, 3, 3, 1, 2, 1, 4, 1, 2, 2]
def baseStart_7638940 : Nat := 118140960795 + 7638940 * 2 ^ 59
def prefixEnd_7638940 : Nat := 4983230072969 + 3 ^ 40 * 7638940 * 2
def baseEnd_7638940 : Nat := 3922447910856447845819161

theorem tailTrace_7638940 : CollatzResearch.WordTrace tailWord_7638940 prefixEnd_7638940 3922447910856447845819161 := by
  unfold tailWord_7638940
  simp only [CollatzResearch.WordTrace]
  refine ⟨139307515472716240965221137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185743353963621654620294849 139307515472716240965221137)
  ·
    refine ⟨104480636604537180723915853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139307515472716240965221137 104480636604537180723915853)
    ·
      refine ⟨39180238726701442771468445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104480636604537180723915853 39180238726701442771468445)
      ·
        refine ⟨14692589522513041039300667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39180238726701442771468445 14692589522513041039300667)
        ·
          refine ⟨22038884283769561558951001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14692589522513041039300667 22038884283769561558951001)
          ·
            refine ⟨16529163212827171169213251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22038884283769561558951001 16529163212827171169213251)
            ·
              refine ⟨24793744819240756753819877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16529163212827171169213251 24793744819240756753819877)
              ·
                refine ⟨4648827153607641891341227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24793744819240756753819877 4648827153607641891341227)
                ·
                  refine ⟨6973240730411462837011841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4648827153607641891341227 6973240730411462837011841)
                  ·
                    refine ⟨5229930547808597127758881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6973240730411462837011841 5229930547808597127758881)
                    ·
                      refine ⟨3922447910856447845819161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5229930547808597127758881 3922447910856447845819161)
                      ·
                        rfl

theorem cell23_7638940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_7638940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638940 prefixEnd_7638940 := by exact prefixLift 7638940
  have htrace : WordTrace (prefixWord ++ tailWord_7638940) baseStart_7638940 baseEnd_7638940 := by
    simpa [prefixWord, tailWord_7638940, baseEnd_7638940] using wordTrace_append hprefix tailTrace_7638940
  have hstable : (prefixWord ++ tailWord_7638940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638940).length < 2 ^ (prefixWord ++ tailWord_7638940).sum := by decide
  have hdescent : baseEnd_7638940 < baseStart_7638940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638946 : List Nat := [3, 3, 1, 2, 4, 1, 1, 8]
def baseStart_7638946 : Nat := 118140960795 + 7638946 * 2 ^ 59
def prefixEnd_7638946 : Nat := 4983230072969 + 3 ^ 40 * 7638946 * 2
def baseEnd_7638946 : Nat := 145275962657050919346079

theorem tailTrace_7638946 : CollatzResearch.WordTrace tailWord_7638946 prefixEnd_7638946 145275962657050919346079 := by
  unfold tailWord_7638946
  simp only [CollatzResearch.WordTrace]
  refine ⟨69653812445852686238790173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185743499855607163303440461 69653812445852686238790173)
  ·
    refine ⟨26120179667194757339546315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69653812445852686238790173 26120179667194757339546315)
    ·
      refine ⟨39180269500792136009319473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26120179667194757339546315 39180269500792136009319473)
      ·
        refine ⟨29385202125594102006989605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39180269500792136009319473 29385202125594102006989605)
        ·
          refine ⟨5509725398548894126310551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29385202125594102006989605 5509725398548894126310551)
          ·
            refine ⟨8264588097823341189465827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5509725398548894126310551 8264588097823341189465827)
            ·
              refine ⟨12396882146735011784198741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8264588097823341189465827 12396882146735011784198741)
              ·
                refine ⟨145275962657050919346079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12396882146735011784198741 145275962657050919346079)
                ·
                  rfl

theorem cell23_7638946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 8].length) (baseStart_7638946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638946 prefixEnd_7638946 := by exact prefixLift 7638946
  have htrace : WordTrace (prefixWord ++ tailWord_7638946) baseStart_7638946 baseEnd_7638946 := by
    simpa [prefixWord, tailWord_7638946, baseEnd_7638946] using wordTrace_append hprefix tailTrace_7638946
  have hstable : (prefixWord ++ tailWord_7638946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638946).length < 2 ^ (prefixWord ++ tailWord_7638946).sum := by decide
  have hdescent : baseEnd_7638946 < baseStart_7638946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7638992 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 4]
def baseStart_7638992 : Nat := 118140960795 + 7638992 * 2 ^ 59
def prefixEnd_7638992 : Nat := 4983230072969 + 3 ^ 40 * 7638992 * 2
def baseEnd_7638992 : Nat := 3922474611850481642368921

theorem tailTrace_7638992 : CollatzResearch.WordTrace tailWord_7638992 prefixEnd_7638992 3922474611850481642368921 := by
  unfold tailWord_7638992
  simp only [CollatzResearch.WordTrace]
  refine ⟨139308463770622047405667615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185744618360829396540890153 139308463770622047405667615)
  ·
    refine ⟨208962695655933071108501423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139308463770622047405667615 208962695655933071108501423)
    ·
      refine ⟨313444043483899606662752135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208962695655933071108501423 313444043483899606662752135)
      ·
        refine ⟨470166065225849409994128203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313444043483899606662752135 470166065225849409994128203)
        ·
          refine ⟨705249097838774114991192305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470166065225849409994128203 705249097838774114991192305)
          ·
            refine ⟨528936823379080586243394229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705249097838774114991192305 528936823379080586243394229)
            ·
              refine ⟨49587827191788804960318209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 528936823379080586243394229 49587827191788804960318209)
              ·
                refine ⟨37190870393841603720238657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49587827191788804960318209 37190870393841603720238657)
                ·
                  refine ⟨27893152795381202790178993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37190870393841603720238657 27893152795381202790178993)
                  ·
                    refine ⟨20919864596535902092634245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27893152795381202790178993 20919864596535902092634245)
                    ·
                      refine ⟨3922474611850481642368921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20919864596535902092634245 3922474611850481642368921)
                      ·
                        rfl

theorem cell23_7638992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_7638992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7638992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7638992 prefixEnd_7638992 := by exact prefixLift 7638992
  have htrace : WordTrace (prefixWord ++ tailWord_7638992) baseStart_7638992 baseEnd_7638992 := by
    simpa [prefixWord, tailWord_7638992, baseEnd_7638992] using wordTrace_append hprefix tailTrace_7638992
  have hstable : (prefixWord ++ tailWord_7638992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7638992).length < 2 ^ (prefixWord ++ tailWord_7638992).sum := by decide
  have hdescent : baseEnd_7638992 < baseStart_7638992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7638992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639032 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 1, 7]
def baseStart_7639032 : Nat := 118140960795 + 7639032 * 2 ^ 59
def prefixEnd_7639032 : Nat := 4983230072969 + 3 ^ 40 * 7639032 * 2
def baseEnd_7639032 : Nat := 1307498383692220495289579

theorem tailTrace_7639032 : CollatzResearch.WordTrace tailWord_7639032 prefixEnd_7639032 1307498383692220495289579 := by
  unfold tailWord_7639032
  simp only [CollatzResearch.WordTrace]
  refine ⟨139309193230549590821395675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185745590974066121095194233 139309193230549590821395675)
  ·
    refine ⟨208963789845824386232093513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139309193230549590821395675 208963789845824386232093513)
    ·
      refine ⟨156722842384368289674070135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208963789845824386232093513 156722842384368289674070135)
      ·
        refine ⟨235084263576552434511105203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156722842384368289674070135 235084263576552434511105203)
        ·
          refine ⟨352626395364828651766657805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235084263576552434511105203 352626395364828651766657805)
          ·
            refine ⟨132234898261810744412496677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352626395364828651766657805 132234898261810744412496677)
            ·
              refine ⟨24794043424089514577343127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132234898261810744412496677 24794043424089514577343127)
              ·
                refine ⟨37191065136134271866014691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24794043424089514577343127 37191065136134271866014691)
                ·
                  refine ⟨55786597704201407799022037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37191065136134271866014691 55786597704201407799022037)
                  ·
                    refine ⟨1307498383692220495289579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55786597704201407799022037 1307498383692220495289579)
                    ·
                      rfl

theorem cell23_7639032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_7639032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639032 prefixEnd_7639032 := by exact prefixLift 7639032
  have htrace : WordTrace (prefixWord ++ tailWord_7639032) baseStart_7639032 baseEnd_7639032 := by
    simpa [prefixWord, tailWord_7639032, baseEnd_7639032] using wordTrace_append hprefix tailTrace_7639032
  have hstable : (prefixWord ++ tailWord_7639032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639032).length < 2 ^ (prefixWord ++ tailWord_7639032).sum := by decide
  have hdescent : baseEnd_7639032 < baseStart_7639032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639086 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_7639086 : Nat := 118140960795 + 7639086 * 2 ^ 59
def prefixEnd_7639086 : Nat := 4983230072969 + 3 ^ 40 * 7639086 * 2
def baseEnd_7639086 : Nat := 3922522879032004274593489

theorem tailTrace_7639086 : CollatzResearch.WordTrace tailWord_7639086 prefixEnd_7639086 3922522879032004274593489 := by
  unfold tailWord_7639086
  simp only [CollatzResearch.WordTrace]
  refine ⟨34827544500362943608157139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185746904001935699243504741 34827544500362943608157139)
  ·
    refine ⟨52241316750544415412235709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34827544500362943608157139 52241316750544415412235709)
    ·
      refine ⟨19590493781454155779588391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52241316750544415412235709 19590493781454155779588391)
      ·
        refine ⟨29385740672181233669382587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19590493781454155779588391 29385740672181233669382587)
        ·
          refine ⟨44078611008271850504073881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29385740672181233669382587 44078611008271850504073881)
          ·
            refine ⟨33058958256203887878055411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44078611008271850504073881 33058958256203887878055411)
            ·
              refine ⟨49588437384305831817083117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33058958256203887878055411 49588437384305831817083117)
              ·
                refine ⟨18595664019114686931406169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49588437384305831817083117 18595664019114686931406169)
                ·
                  refine ⟨13946748014336015198554627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18595664019114686931406169 13946748014336015198554627)
                  ·
                    refine ⟨20920122021504022797831941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13946748014336015198554627 20920122021504022797831941)
                    ·
                      refine ⟨3922522879032004274593489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20920122021504022797831941 3922522879032004274593489)
                      ·
                        rfl

theorem cell23_7639086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_7639086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639086 prefixEnd_7639086 := by exact prefixLift 7639086
  have htrace : WordTrace (prefixWord ++ tailWord_7639086) baseStart_7639086 baseEnd_7639086 := by
    simpa [prefixWord, tailWord_7639086, baseEnd_7639086] using wordTrace_append hprefix tailTrace_7639086
  have hstable : (prefixWord ++ tailWord_7639086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639086).length < 2 ^ (prefixWord ++ tailWord_7639086).sum := by decide
  have hdescent : baseEnd_7639086 < baseStart_7639086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639136 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 5, 1, 3]
def baseStart_7639136 : Nat := 118140960795 + 7639136 * 2 ^ 59
def prefixEnd_7639136 : Nat := 4983230072969 + 3 ^ 40 * 7639136 * 2
def baseEnd_7639136 : Nat := 3922548553064729078968259

theorem tailTrace_7639136 : CollatzResearch.WordTrace tailWord_7639136 prefixEnd_7639136 3922548553064729078968259 := by
  unfold tailWord_7639136
  simp only [CollatzResearch.WordTrace]
  refine ⟨139311089826361203702288631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185748119768481604936384841 139311089826361203702288631)
  ·
    refine ⟨208966634739541805553432947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139311089826361203702288631 208966634739541805553432947)
    ·
      refine ⟨313449952109312708330149421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208966634739541805553432947 313449952109312708330149421)
      ·
        refine ⟨117543732040992265623806033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313449952109312708330149421 117543732040992265623806033)
        ·
          refine ⟨88157799030744199217854525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117543732040992265623806033 88157799030744199217854525)
          ·
            refine ⟨33059174636529074706695447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88157799030744199217854525 33059174636529074706695447)
            ·
              refine ⟨49588761954793612060043171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33059174636529074706695447 49588761954793612060043171)
              ·
                refine ⟨74383142932190418090064757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49588761954793612060043171 74383142932190418090064757)
                ·
                  refine ⟨6973419649892851695943571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74383142932190418090064757 6973419649892851695943571)
                  ·
                    refine ⟨10460129474839277543915357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6973419649892851695943571 10460129474839277543915357)
                    ·
                      refine ⟨3922548553064729078968259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10460129474839277543915357 3922548553064729078968259)
                      ·
                        rfl

theorem cell23_7639136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_7639136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639136 prefixEnd_7639136 := by exact prefixLift 7639136
  have htrace : WordTrace (prefixWord ++ tailWord_7639136) baseStart_7639136 baseEnd_7639136 := by
    simpa [prefixWord, tailWord_7639136, baseEnd_7639136] using wordTrace_append hprefix tailTrace_7639136
  have hstable : (prefixWord ++ tailWord_7639136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639136).length < 2 ^ (prefixWord ++ tailWord_7639136).sum := by decide
  have hdescent : baseEnd_7639136 < baseStart_7639136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639139 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 3, 5]
def baseStart_7639139 : Nat := 118140960795 + 7639139 * 2 ^ 59
def prefixEnd_7639139 : Nat := 4983230072969 + 3 ^ 40 * 7639139 * 2
def baseEnd_7639139 : Nat := 1307516697835564189076915

theorem tailTrace_7639139 : CollatzResearch.WordTrace tailWord_7639139 prefixEnd_7639139 1307516697835564189076915 := by
  unfold tailWord_7639139
  simp only [CollatzResearch.WordTrace]
  refine ⟨278622289071711538916936471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185748192714474359277957647 278622289071711538916936471)
  ·
    refine ⟨417933433607567308375404707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278622289071711538916936471 417933433607567308375404707)
    ·
      refine ⟨626900150411350962563107061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417933433607567308375404707 626900150411350962563107061)
      ·
        refine ⟨58771889101064152740291287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 626900150411350962563107061 58771889101064152740291287)
        ·
          refine ⟨88157833651596229110436931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58771889101064152740291287 88157833651596229110436931)
          ·
            refine ⟨132236750477394343665655397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88157833651596229110436931 132236750477394343665655397)
            ·
              refine ⟨24794390714511439437310387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132236750477394343665655397 24794390714511439437310387)
              ·
                refine ⟨37191586071767159155965581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24794390714511439437310387 37191586071767159155965581)
                ·
                  refine ⟨13946844776912684683487093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37191586071767159155965581 13946844776912684683487093)
                  ·
                    refine ⟨1307516697835564189076915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13946844776912684683487093 1307516697835564189076915)
                    ·
                      rfl

theorem cell23_7639139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 5].length) (baseStart_7639139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639139 prefixEnd_7639139 := by exact prefixLift 7639139
  have htrace : WordTrace (prefixWord ++ tailWord_7639139) baseStart_7639139 baseEnd_7639139 := by
    simpa [prefixWord, tailWord_7639139, baseEnd_7639139] using wordTrace_append hprefix tailTrace_7639139
  have hstable : (prefixWord ++ tailWord_7639139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639139).length < 2 ^ (prefixWord ++ tailWord_7639139).sum := by decide
  have hdescent : baseEnd_7639139 < baseStart_7639139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639189 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_7639189 : Nat := 118140960795 + 7639189 * 2 ^ 59
def prefixEnd_7639189 : Nat := 4983230072969 + 3 ^ 40 * 7639189 * 2
def baseEnd_7639189 : Nat := 3922575767539417371605515

theorem tailTrace_7639189 : CollatzResearch.WordTrace tailWord_7639189 prefixEnd_7639189 3922575767539417371605515 := by
  unfold tailWord_7639189
  simp only [CollatzResearch.WordTrace]
  refine ⟨278624112721530397456256621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185749408481020264970837747 278624112721530397456256621)
  ·
    refine ⟨104484042270573899046096233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278624112721530397456256621 104484042270573899046096233)
    ·
      refine ⟨78363031702930424284572175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104484042270573899046096233 78363031702930424284572175)
      ·
        refine ⟨117544547554395636426858263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78363031702930424284572175 117544547554395636426858263)
        ·
          refine ⟨176316821331593454640287395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117544547554395636426858263 176316821331593454640287395)
          ·
            refine ⟨264475231997390181960431093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176316821331593454640287395 264475231997390181960431093)
            ·
              refine ⟨24794552999755329558790415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264475231997390181960431093 24794552999755329558790415)
              ·
                refine ⟨37191829499632994338185623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24794552999755329558790415 37191829499632994338185623)
                ·
                  refine ⟨55787744249449491507278435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37191829499632994338185623 55787744249449491507278435)
                  ·
                    refine ⟨83681616374174237260917653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55787744249449491507278435 83681616374174237260917653)
                    ·
                      refine ⟨3922575767539417371605515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83681616374174237260917653 3922575767539417371605515)
                      ·
                        rfl

theorem cell23_7639189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_7639189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639189 prefixEnd_7639189 := by exact prefixLift 7639189
  have htrace : WordTrace (prefixWord ++ tailWord_7639189) baseStart_7639189 baseEnd_7639189 := by
    simpa [prefixWord, tailWord_7639189, baseEnd_7639189] using wordTrace_append hprefix tailTrace_7639189
  have hstable : (prefixWord ++ tailWord_7639189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639189).length < 2 ^ (prefixWord ++ tailWord_7639189).sum := by decide
  have hdescent : baseEnd_7639189 < baseStart_7639189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639204 : List Nat := [2, 3, 1, 2, 5, 1, 1, 3, 1, 1, 3]
def baseStart_7639204 : Nat := 118140960795 + 7639204 * 2 ^ 59
def prefixEnd_7639204 : Nat := 4983230072969 + 3 ^ 40 * 7639204 * 2
def baseEnd_7639204 : Nat := 3922583469749234812917947

theorem tailTrace_7639204 : CollatzResearch.WordTrace tailWord_7639204 prefixEnd_7639204 3922583469749234812917947 := by
  unfold tailWord_7639204
  simp only [CollatzResearch.WordTrace]
  refine ⟨139312329908238027509026333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185749773210984036678701777 139312329908238027509026333)
  ·
    refine ⟨52242123715589260315884875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139312329908238027509026333 52242123715589260315884875)
    ·
      refine ⟨78363185573383890473827313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52242123715589260315884875 78363185573383890473827313)
      ·
        refine ⟨58772389180037917855370485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78363185573383890473827313 58772389180037917855370485)
        ·
          refine ⟨5509911485628554798940983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58772389180037917855370485 5509911485628554798940983)
          ·
            refine ⟨8264867228442832198411475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5509911485628554798940983 8264867228442832198411475)
            ·
              refine ⟨12397300842664248297617213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8264867228442832198411475 12397300842664248297617213)
              ·
                refine ⟨4648987815999093111606455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12397300842664248297617213 4648987815999093111606455)
                ·
                  refine ⟨6973481723998639667409683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4648987815999093111606455 6973481723998639667409683)
                  ·
                    refine ⟨10460222585997959501114525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6973481723998639667409683 10460222585997959501114525)
                    ·
                      refine ⟨3922583469749234812917947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10460222585997959501114525 3922583469749234812917947)
                      ·
                        rfl

theorem cell23_7639204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_7639204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639204 prefixEnd_7639204 := by exact prefixLift 7639204
  have htrace : WordTrace (prefixWord ++ tailWord_7639204) baseStart_7639204 baseEnd_7639204 := by
    simpa [prefixWord, tailWord_7639204, baseEnd_7639204] using wordTrace_append hprefix tailTrace_7639204
  have hstable : (prefixWord ++ tailWord_7639204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639204).length < 2 ^ (prefixWord ++ tailWord_7639204).sum := by decide
  have hdescent : baseEnd_7639204 < baseStart_7639204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639213 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_7639213 : Nat := 118140960795 + 7639213 * 2 ^ 59
def prefixEnd_7639213 : Nat := 4983230072969 + 3 ^ 40 * 7639213 * 2
def baseEnd_7639213 : Nat := 3922588091075125277705405

theorem tailTrace_7639213 : CollatzResearch.WordTrace tailWord_7639213 prefixEnd_7639213 3922588091075125277705405 := by
  unfold tailWord_7639213
  simp only [CollatzResearch.WordTrace]
  refine ⟨278624988073443449555130293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185749992048962299703420195 278624988073443449555130293)
  ·
    refine ⟨26121092631885323395793465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278624988073443449555130293 26121092631885323395793465)
    ·
      refine ⟨19590819473913992546845099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26121092631885323395793465 19590819473913992546845099)
      ·
        refine ⟨29386229210870988820267649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19590819473913992546845099 29386229210870988820267649)
        ·
          refine ⟨22039671908153241615200737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29386229210870988820267649 22039671908153241615200737)
          ·
            refine ⟨16529753931114931211400553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22039671908153241615200737 16529753931114931211400553)
            ·
              refine ⟨12397315448336198408550415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16529753931114931211400553 12397315448336198408550415)
              ·
                refine ⟨18595973172504297612825623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12397315448336198408550415 18595973172504297612825623)
                ·
                  refine ⟨27893959758756446419238435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18595973172504297612825623 27893959758756446419238435)
                  ·
                    refine ⟨41840939638134669628857653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27893959758756446419238435 41840939638134669628857653)
                    ·
                      refine ⟨3922588091075125277705405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41840939638134669628857653 3922588091075125277705405)
                      ·
                        rfl

theorem cell23_7639213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_7639213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639213 prefixEnd_7639213 := by exact prefixLift 7639213
  have htrace : WordTrace (prefixWord ++ tailWord_7639213) baseStart_7639213 baseEnd_7639213 := by
    simpa [prefixWord, tailWord_7639213, baseEnd_7639213] using wordTrace_append hprefix tailTrace_7639213
  have hstable : (prefixWord ++ tailWord_7639213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639213).length < 2 ^ (prefixWord ++ tailWord_7639213).sum := by decide
  have hdescent : baseEnd_7639213 < baseStart_7639213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639227 : List Nat := [1, 1, 1, 1, 1, 2, 9, 2, 1, 2, 2]
def baseStart_7639227 : Nat := 118140960795 + 7639227 * 2 ^ 59
def prefixEnd_7639227 : Nat := 4983230072969 + 3 ^ 40 * 7639227 * 2
def baseEnd_7639227 : Nat := 3922595279804288222930341

theorem tailTrace_7639227 : CollatzResearch.WordTrace tailWord_7639227 prefixEnd_7639227 3922595279804288222930341 := by
  unfold tailWord_7639227
  simp only [CollatzResearch.WordTrace]
  refine ⟨278625498695392729946139935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185750332463595153297426623 278625498695392729946139935)
  ·
    refine ⟨417938248043089094919209903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278625498695392729946139935 417938248043089094919209903)
    ·
      refine ⟨626907372064633642378814855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417938248043089094919209903 626907372064633642378814855)
      ·
        refine ⟨940361058096950463568222283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626907372064633642378814855 940361058096950463568222283)
        ·
          refine ⟨1410541587145425695352333425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940361058096950463568222283 1410541587145425695352333425)
          ·
            refine ⟨1057906190359069271514250069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1410541587145425695352333425 1057906190359069271514250069)
            ·
              refine ⟨6198669084135171512778809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1057906190359069271514250069 6198669084135171512778809)
              ·
                refine ⟨4649001813101378634584107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6198669084135171512778809 4649001813101378634584107)
                ·
                  refine ⟨6973502719652067951876161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4649001813101378634584107 6973502719652067951876161)
                  ·
                    refine ⟨5230127039739050963907121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6973502719652067951876161 5230127039739050963907121)
                    ·
                      refine ⟨3922595279804288222930341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5230127039739050963907121 3922595279804288222930341)
                      ·
                        rfl

theorem cell23_7639227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 1, 2, 2].length) (baseStart_7639227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639227 prefixEnd_7639227 := by exact prefixLift 7639227
  have htrace : WordTrace (prefixWord ++ tailWord_7639227) baseStart_7639227 baseEnd_7639227 := by
    simpa [prefixWord, tailWord_7639227, baseEnd_7639227] using wordTrace_append hprefix tailTrace_7639227
  have hstable : (prefixWord ++ tailWord_7639227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639227).length < 2 ^ (prefixWord ++ tailWord_7639227).sum := by decide
  have hdescent : baseEnd_7639227 < baseStart_7639227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639229 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_7639229 : Nat := 118140960795 + 7639229 * 2 ^ 59
def prefixEnd_7639229 : Nat := 4983230072969 + 3 ^ 40 * 7639229 * 2
def baseEnd_7639229 : Nat := 1307532102255199071701777

theorem tailTrace_7639229 : CollatzResearch.WordTrace tailWord_7639229 prefixEnd_7639229 1307532102255199071701777 := by
  unfold tailWord_7639229
  simp only [CollatzResearch.WordTrace]
  refine ⟨278625571641385484287712741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185750381094256989525141827 278625571641385484287712741)
  ·
    refine ⟨52242294682759778303946139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278625571641385484287712741 52242294682759778303946139)
    ·
      refine ⟨78363442024139667455919209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52242294682759778303946139 78363442024139667455919209)
      ·
        refine ⟨58772581518104750591939407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78363442024139667455919209 58772581518104750591939407)
        ·
          refine ⟨88158872277157125887909111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58772581518104750591939407 88158872277157125887909111)
          ·
            refine ⟨132238308415735688831863667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88158872277157125887909111 132238308415735688831863667)
            ·
              refine ⟨198357462623603533247795501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132238308415735688831863667 198357462623603533247795501)
              ·
                refine ⟨74384048483851324967923313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198357462623603533247795501 74384048483851324967923313)
                ·
                  refine ⟨55788036362888493725942485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74384048483851324967923313 55788036362888493725942485)
                  ·
                    refine ⟨1307532102255199071701777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55788036362888493725942485 1307532102255199071701777)
                    ·
                      rfl

theorem cell23_7639229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_7639229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639229 prefixEnd_7639229 := by exact prefixLift 7639229
  have htrace : WordTrace (prefixWord ++ tailWord_7639229) baseStart_7639229 baseEnd_7639229 := by
    simpa [prefixWord, tailWord_7639229, baseEnd_7639229] using wordTrace_append hprefix tailTrace_7639229
  have hstable : (prefixWord ++ tailWord_7639229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639229).length < 2 ^ (prefixWord ++ tailWord_7639229).sum := by decide
  have hdescent : baseEnd_7639229 < baseStart_7639229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639233 : List Nat := [1, 2, 6, 1, 2, 1, 2, 8]
def baseStart_7639233 : Nat := 118140960795 + 7639233 * 2 ^ 59
def prefixEnd_7639233 : Nat := 4983230072969 + 3 ^ 40 * 7639233 * 2
def baseEnd_7639233 : Nat := 145281420766230192572419

theorem tailTrace_7639233 : CollatzResearch.WordTrace tailWord_7639233 prefixEnd_7639233 145281420766230192572419 := by
  unfold tailWord_7639233
  simp only [CollatzResearch.WordTrace]
  refine ⟨278625717533370992970858353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185750478355580661980572235 278625717533370992970858353)
  ·
    refine ⟨208969288150028244728143765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278625717533370992970858353 208969288150028244728143765)
    ·
      refine ⟨9795435382032573971631739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 208969288150028244728143765 9795435382032573971631739)
      ·
        refine ⟨14693153073048860957447609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9795435382032573971631739 14693153073048860957447609)
        ·
          refine ⟨11019864804786645718085707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14693153073048860957447609 11019864804786645718085707)
          ·
            refine ⟨16529797207179968577128561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11019864804786645718085707 16529797207179968577128561)
            ·
              refine ⟨12397347905384976432846421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16529797207179968577128561 12397347905384976432846421)
              ·
                refine ⟨145281420766230192572419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12397347905384976432846421 145281420766230192572419)
                ·
                  rfl

theorem cell23_7639233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 8].length) (baseStart_7639233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639233 prefixEnd_7639233 := by exact prefixLift 7639233
  have htrace : WordTrace (prefixWord ++ tailWord_7639233) baseStart_7639233 baseEnd_7639233 := by
    simpa [prefixWord, tailWord_7639233, baseEnd_7639233] using wordTrace_append hprefix tailTrace_7639233
  have hstable : (prefixWord ++ tailWord_7639233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639233).length < 2 ^ (prefixWord ++ tailWord_7639233).sum := by decide
  have hdescent : baseEnd_7639233 < baseStart_7639233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639243 : List Nat := [1, 1, 1, 1, 3, 2, 5, 3, 2, 1, 3]
def baseStart_7639243 : Nat := 118140960795 + 7639243 * 2 ^ 59
def prefixEnd_7639243 : Nat := 4983230072969 + 3 ^ 40 * 7639243 * 2
def baseEnd_7639243 : Nat := 3922603495494760160330267

theorem tailTrace_7639243 : CollatzResearch.WordTrace tailWord_7639243 prefixEnd_7639243 3922603495494760160330267 := by
  unfold tailWord_7639243
  simp only [CollatzResearch.WordTrace]
  refine ⟨278626082263334764678722383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185750721508889843119148255 278626082263334764678722383)
  ·
    refine ⟨417939123395002147018083575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278626082263334764678722383 417939123395002147018083575)
    ·
      refine ⟨626908685092503220527125363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417939123395002147018083575 626908685092503220527125363)
      ·
        refine ⟨940363027638754830790688045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626908685092503220527125363 940363027638754830790688045)
        ·
          refine ⟨352636135364533061546508017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 940363027638754830790688045 352636135364533061546508017)
          ·
            refine ⟨264477101523399796159881013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352636135364533061546508017 264477101523399796159881013)
            ·
              refine ⟨24794728267818730889988845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264477101523399796159881013 24794728267818730889988845)
              ·
                refine ⟨9298023100432024083745817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24794728267818730889988845 9298023100432024083745817)
                ·
                  refine ⟨6973517325324018062809363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9298023100432024083745817 6973517325324018062809363)
                  ·
                    refine ⟨10460275987986027094214045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6973517325324018062809363 10460275987986027094214045)
                    ·
                      refine ⟨3922603495494760160330267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10460275987986027094214045 3922603495494760160330267)
                      ·
                        rfl

theorem cell23_7639243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 1, 3].length) (baseStart_7639243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639243 prefixEnd_7639243 := by exact prefixLift 7639243
  have htrace : WordTrace (prefixWord ++ tailWord_7639243) baseStart_7639243 baseEnd_7639243 := by
    simpa [prefixWord, tailWord_7639243, baseEnd_7639243] using wordTrace_append hprefix tailTrace_7639243
  have hstable : (prefixWord ++ tailWord_7639243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639243).length < 2 ^ (prefixWord ++ tailWord_7639243).sum := by decide
  have hdescent : baseEnd_7639243 < baseStart_7639243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639277 : List Nat := [1, 5, 1, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_7639277 : Nat := 118140960795 + 7639277 * 2 ^ 59
def prefixEnd_7639277 : Nat := 4983230072969 + 3 ^ 40 * 7639277 * 2
def baseEnd_7639277 : Nat := 3922620953837013027305111

theorem tailTrace_7639277 : CollatzResearch.WordTrace tailWord_7639277 prefixEnd_7639277 3922620953837013027305111 := by
  unfold tailWord_7639277
  simp only [CollatzResearch.WordTrace]
  refine ⟨278627322345211588485460085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185751548230141058990306723 278627322345211588485460085)
  ·
    refine ⟨26121311469863586420511883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278627322345211588485460085 26121311469863586420511883)
    ·
      refine ⟨39181967204795379630767825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26121311469863586420511883 39181967204795379630767825)
      ·
        refine ⟨29386475403596534723075869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39181967204795379630767825 29386475403596534723075869)
        ·
          refine ⟨11019928276348700521153451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29386475403596534723075869 11019928276348700521153451)
          ·
            refine ⟨16529892414523050781730177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11019928276348700521153451 16529892414523050781730177)
            ·
              refine ⟨12397419310892288086297633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16529892414523050781730177 12397419310892288086297633)
              ·
                refine ⟨9298064483169216064723225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12397419310892288086297633 9298064483169216064723225)
                ·
                  refine ⟨6973548362376912048542419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9298064483169216064723225 6973548362376912048542419)
                  ·
                    refine ⟨10460322543565368072813629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6973548362376912048542419 10460322543565368072813629)
                    ·
                      refine ⟨3922620953837013027305111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10460322543565368072813629 3922620953837013027305111)
                      ·
                        rfl

theorem cell23_7639277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_7639277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639277 prefixEnd_7639277 := by exact prefixLift 7639277
  have htrace : WordTrace (prefixWord ++ tailWord_7639277) baseStart_7639277 baseEnd_7639277 := by
    simpa [prefixWord, tailWord_7639277, baseEnd_7639277] using wordTrace_append hprefix tailTrace_7639277
  have hstable : (prefixWord ++ tailWord_7639277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639277).length < 2 ^ (prefixWord ++ tailWord_7639277).sum := by decide
  have hdescent : baseEnd_7639277 < baseStart_7639277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639286 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_7639286 : Nat := 118140960795 + 7639286 * 2 ^ 59
def prefixEnd_7639286 : Nat := 4983230072969 + 3 ^ 40 * 7639286 * 2
def baseEnd_7639286 : Nat := 3922625575162903492092569

theorem tailTrace_7639286 : CollatzResearch.WordTrace tailWord_7639286 prefixEnd_7639286 3922625575162903492092569 := by
  unfold tailWord_7639286
  simp only [CollatzResearch.WordTrace]
  refine ⟨17414228162636186438908607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185751767068119322015025141 17414228162636186438908607)
  ·
    refine ⟨26121342243954279658362911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17414228162636186438908607 26121342243954279658362911)
    ·
      refine ⟨39182013365931419487544367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26121342243954279658362911 39182013365931419487544367)
      ·
        refine ⟨58773020048897129231316551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39182013365931419487544367 58773020048897129231316551)
        ·
          refine ⟨88159530073345693846974827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58773020048897129231316551 88159530073345693846974827)
          ·
            refine ⟨132239295110018540770462241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88159530073345693846974827 132239295110018540770462241)
            ·
              refine ⟨99179471332513905577846681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132239295110018540770462241 99179471332513905577846681)
              ·
                refine ⟨74384603499385429183385011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99179471332513905577846681 74384603499385429183385011)
                ·
                  refine ⟨111576905249078143775077517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74384603499385429183385011 111576905249078143775077517)
                  ·
                    refine ⟨41841339468404303915654069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111576905249078143775077517 41841339468404303915654069)
                    ·
                      refine ⟨3922625575162903492092569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41841339468404303915654069 3922625575162903492092569)
                      ·
                        rfl

theorem cell23_7639286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_7639286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639286 prefixEnd_7639286 := by exact prefixLift 7639286
  have htrace : WordTrace (prefixWord ++ tailWord_7639286) baseStart_7639286 baseEnd_7639286 := by
    simpa [prefixWord, tailWord_7639286, baseEnd_7639286] using wordTrace_append hprefix tailTrace_7639286
  have hstable : (prefixWord ++ tailWord_7639286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639286).length < 2 ^ (prefixWord ++ tailWord_7639286).sum := by decide
  have hdescent : baseEnd_7639286 < baseStart_7639286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639339 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 8]
def baseStart_7639339 : Nat := 118140960795 + 7639339 * 2 ^ 59
def prefixEnd_7639339 : Nat := 4983230072969 + 3 ^ 40 * 7639339 * 2
def baseEnd_7639339 : Nat := 3922652789637591784729825

theorem tailTrace_7639339 : CollatzResearch.WordTrace tailWord_7639339 prefixEnd_7639339 3922652789637591784729825 := by
  unfold tailWord_7639339
  simp only [CollatzResearch.WordTrace]
  refine ⟨278629583670986973074217071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185753055780657982049478047 278629583670986973074217071)
  ·
    refine ⟨417944375506480459611325607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278629583670986973074217071 417944375506480459611325607)
    ·
      refine ⟨626916563259720689416988411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417944375506480459611325607 626916563259720689416988411)
      ·
        refine ⟨940374844889581034125482617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626916563259720689416988411 940374844889581034125482617)
        ·
          refine ⟨705281133667185775594111963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 940374844889581034125482617 705281133667185775594111963)
          ·
            refine ⟨1057921700500778663391167945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705281133667185775594111963 1057921700500778663391167945)
            ·
              refine ⟨793441275375583997543375959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1057921700500778663391167945 793441275375583997543375959)
              ·
                refine ⟨1190161913063375996315063939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793441275375583997543375959 1190161913063375996315063939)
                ·
                  refine ⟨1785242869595063994472595909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190161913063375996315063939 1785242869595063994472595909)
                  ·
                    refine ⟨334733038049074498963611733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1785242869595063994472595909 334733038049074498963611733)
                    ·
                      refine ⟨3922652789637591784729825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 334733038049074498963611733 3922652789637591784729825)
                      ·
                        rfl

theorem cell23_7639339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 8].length) (baseStart_7639339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639339 prefixEnd_7639339 := by exact prefixLift 7639339
  have htrace : WordTrace (prefixWord ++ tailWord_7639339) baseStart_7639339 baseEnd_7639339 := by
    simpa [prefixWord, tailWord_7639339, baseEnd_7639339] using wordTrace_append hprefix tailTrace_7639339
  have hstable : (prefixWord ++ tailWord_7639339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639339).length < 2 ^ (prefixWord ++ tailWord_7639339).sum := by decide
  have hdescent : baseEnd_7639339 < baseStart_7639339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639356 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_7639356 : Nat := 118140960795 + 7639356 * 2 ^ 59
def prefixEnd_7639356 : Nat := 4983230072969 + 3 ^ 40 * 7639356 * 2
def baseEnd_7639356 : Nat := 3922661518808718218217247

theorem tailTrace_7639356 : CollatzResearch.WordTrace tailWord_7639356 prefixEnd_7639356 3922661518808718218217247 := by
  unfold tailWord_7639356
  simp only [CollatzResearch.WordTrace]
  refine ⟨139315101855962692488792961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185753469141283589985057281 139315101855962692488792961)
  ·
    refine ⟨104486326391972019366594721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139315101855962692488792961 104486326391972019366594721)
    ·
      refine ⟨78364744793979014524946041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104486326391972019366594721 78364744793979014524946041)
      ·
        refine ⟨58773558595484260893709531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78364744793979014524946041 58773558595484260893709531)
        ·
          refine ⟨88160337893226391340564297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58773558595484260893709531 88160337893226391340564297)
          ·
            refine ⟨66120253419919793505423223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88160337893226391340564297 66120253419919793505423223)
            ·
              refine ⟨99180380129879690258134835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66120253419919793505423223 99180380129879690258134835)
              ·
                refine ⟨148770570194819535387202253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99180380129879690258134835 148770570194819535387202253)
                ·
                  refine ⟨55788963823057325770200845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148770570194819535387202253 55788963823057325770200845)
                  ·
                    refine ⟨20920861433646497163825317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55788963823057325770200845 20920861433646497163825317)
                    ·
                      refine ⟨3922661518808718218217247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20920861433646497163825317 3922661518808718218217247)
                      ·
                        rfl

theorem cell23_7639356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_7639356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639356 prefixEnd_7639356 := by exact prefixLift 7639356
  have htrace : WordTrace (prefixWord ++ tailWord_7639356) baseStart_7639356 baseEnd_7639356 := by
    simpa [prefixWord, tailWord_7639356, baseEnd_7639356] using wordTrace_append hprefix tailTrace_7639356
  have hstable : (prefixWord ++ tailWord_7639356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639356).length < 2 ^ (prefixWord ++ tailWord_7639356).sum := by decide
  have hdescent : baseEnd_7639356 < baseStart_7639356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639396 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 8]
def baseStart_7639396 : Nat := 118140960795 + 7639396 * 2 ^ 59
def prefixEnd_7639396 : Nat := 4983230072969 + 3 ^ 40 * 7639396 * 2
def baseEnd_7639396 : Nat := 435853562003877562413007

theorem tailTrace_7639396 : CollatzResearch.WordTrace tailWord_7639396 prefixEnd_7639396 435853562003877562413007 := by
  unfold tailWord_7639396
  simp only [CollatzResearch.WordTrace]
  refine ⟨139315831315890235904521021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185754441754520314539361361 139315831315890235904521021)
  ·
    refine ⟨52243436743458838464195383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139315831315890235904521021 52243436743458838464195383)
    ·
      refine ⟨78365155115188257696293075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52243436743458838464195383 78365155115188257696293075)
      ·
        refine ⟨117547732672782386544439613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78365155115188257696293075 117547732672782386544439613)
        ·
          refine ⟨44080399752293394954164855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117547732672782386544439613 44080399752293394954164855)
          ·
            refine ⟨66120599628440092431247283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44080399752293394954164855 66120599628440092431247283)
            ·
              refine ⟨99180899442660138646870925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66120599628440092431247283 99180899442660138646870925)
              ·
                refine ⟨37192837290997551992576597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99180899442660138646870925 37192837290997551992576597)
                ·
                  refine ⟨435853562003877562413007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37192837290997551992576597 435853562003877562413007)
                  ·
                    rfl

theorem cell23_7639396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_7639396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639396 prefixEnd_7639396 := by exact prefixLift 7639396
  have htrace : WordTrace (prefixWord ++ tailWord_7639396) baseStart_7639396 baseEnd_7639396 := by
    simpa [prefixWord, tailWord_7639396, baseEnd_7639396] using wordTrace_append hprefix tailTrace_7639396
  have hstable : (prefixWord ++ tailWord_7639396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639396).length < 2 ^ (prefixWord ++ tailWord_7639396).sum := by decide
  have hdescent : baseEnd_7639396 < baseStart_7639396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639400 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 3, 4]
def baseStart_7639400 : Nat := 118140960795 + 7639400 * 2 ^ 59
def prefixEnd_7639400 : Nat := 4983230072969 + 3 ^ 40 * 7639400 * 2
def baseEnd_7639400 : Nat := 1307561370652505348689015

theorem tailTrace_7639400 : CollatzResearch.WordTrace tailWord_7639400 prefixEnd_7639400 1307561370652505348689015 := by
  unfold tailWord_7639400
  simp only [CollatzResearch.WordTrace]
  refine ⟨139315904261882990246093827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185754539015843986994791769 139315904261882990246093827)
  ·
    refine ⟨208973856392824485369140741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139315904261882990246093827 208973856392824485369140741)
    ·
      refine ⟨39182598073654591006713889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208973856392824485369140741 39182598073654591006713889)
      ·
        refine ⟨29386948555240943255035417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39182598073654591006713889 29386948555240943255035417)
        ·
          refine ⟨22040211416430707441276563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29386948555240943255035417 22040211416430707441276563)
          ·
            refine ⟨33060317124646061161914845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22040211416430707441276563 33060317124646061161914845)
            ·
              refine ⟨12397618921742272935718067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33060317124646061161914845 12397618921742272935718067)
              ·
                refine ⟨18596428382613409403577101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12397618921742272935718067 18596428382613409403577101)
                ·
                  refine ⟨6973660643480028526341413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18596428382613409403577101 6973660643480028526341413)
                  ·
                    refine ⟨1307561370652505348689015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6973660643480028526341413 1307561370652505348689015)
                    ·
                      rfl

theorem cell23_7639400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_7639400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639400 prefixEnd_7639400 := by exact prefixLift 7639400
  have htrace : WordTrace (prefixWord ++ tailWord_7639400) baseStart_7639400 baseEnd_7639400 := by
    simpa [prefixWord, tailWord_7639400, baseEnd_7639400] using wordTrace_append hprefix tailTrace_7639400
  have hstable : (prefixWord ++ tailWord_7639400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639400).length < 2 ^ (prefixWord ++ tailWord_7639400).sum := by decide
  have hdescent : baseEnd_7639400 < baseStart_7639400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639473 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 1, 6]
def baseStart_7639473 : Nat := 118140960795 + 7639473 * 2 ^ 59
def prefixEnd_7639473 : Nat := 4983230072969 + 3 ^ 40 * 7639473 * 2
def baseEnd_7639473 : Nat := 1307573865348431420151403

theorem tailTrace_7639473 : CollatzResearch.WordTrace tailWord_7639473 prefixEnd_7639473 1307573865348431420151403 := by
  unfold tailWord_7639473
  simp only [CollatzResearch.WordTrace]
  refine ⟨278634471052501513959595073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185756314035001009306396715 278634471052501513959595073)
  ·
    refine ⟨208975853289376135469696305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278634471052501513959595073 208975853289376135469696305)
    ·
      refine ⟨156731889967032101602272229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208975853289376135469696305 156731889967032101602272229)
      ·
        refine ⟨29387229368818519050426043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156731889967032101602272229 29387229368818519050426043)
        ·
          refine ⟨44080844053227778575639065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29387229368818519050426043 44080844053227778575639065)
          ·
            refine ⟨33060633039920833931729299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44080844053227778575639065 33060633039920833931729299)
            ·
              refine ⟨49590949559881250897593949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33060633039920833931729299 49590949559881250897593949)
              ·
                refine ⟨18596606084955469086597731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49590949559881250897593949 18596606084955469086597731)
                ·
                  refine ⟨27894909127433203629896597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18596606084955469086597731 27894909127433203629896597)
                  ·
                    refine ⟨1307573865348431420151403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27894909127433203629896597 1307573865348431420151403)
                    ·
                      rfl

theorem cell23_7639473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_7639473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639473 prefixEnd_7639473 := by exact prefixLift 7639473
  have htrace : WordTrace (prefixWord ++ tailWord_7639473) baseStart_7639473 baseEnd_7639473 := by
    simpa [prefixWord, tailWord_7639473, baseEnd_7639473] using wordTrace_append hprefix tailTrace_7639473
  have hstable : (prefixWord ++ tailWord_7639473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639473).length < 2 ^ (prefixWord ++ tailWord_7639473).sum := by decide
  have hdescent : baseEnd_7639473 < baseStart_7639473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639484 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 2, 3, 2]
def baseStart_7639484 : Nat := 118140960795 + 7639484 * 2 ^ 59
def prefixEnd_7639484 : Nat := 4983230072969 + 3 ^ 40 * 7639484 * 2
def baseEnd_7639484 : Nat := 3922727244332493717416659

theorem tailTrace_7639484 : CollatzResearch.WordTrace tailWord_7639484 prefixEnd_7639484 3922727244332493717416659 := by
  unfold tailWord_7639484
  simp only [CollatzResearch.WordTrace]
  refine ⟨139317436127730831419122753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185756581503641108558830337 139317436127730831419122753)
  ·
    refine ⟨104488077095798123564342065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139317436127730831419122753 104488077095798123564342065)
    ·
      refine ⟨78366057821848592673256549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104488077095798123564342065 78366057821848592673256549)
      ·
        refine ⟨14693635841596611126235603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78366057821848592673256549 14693635841596611126235603)
        ·
          refine ⟨22040453762394916689353405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14693635841596611126235603 22040453762394916689353405)
          ·
            refine ⟨8265170160898093758507527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22040453762394916689353405 8265170160898093758507527)
            ·
              refine ⟨12397755241347140637761291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8265170160898093758507527 12397755241347140637761291)
              ·
                refine ⟨18596632862020710956641937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12397755241347140637761291 18596632862020710956641937)
                ·
                  refine ⟨13947474646515533217481453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18596632862020710956641937 13947474646515533217481453)
                  ·
                    refine ⟨5230302992443324956555545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13947474646515533217481453 5230302992443324956555545)
                    ·
                      refine ⟨3922727244332493717416659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5230302992443324956555545 3922727244332493717416659)
                      ·
                        rfl

theorem cell23_7639484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_7639484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639484 prefixEnd_7639484 := by exact prefixLift 7639484
  have htrace : WordTrace (prefixWord ++ tailWord_7639484) baseStart_7639484 baseEnd_7639484 := by
    simpa [prefixWord, tailWord_7639484, baseEnd_7639484] using wordTrace_append hprefix tailTrace_7639484
  have hstable : (prefixWord ++ tailWord_7639484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639484).length < 2 ^ (prefixWord ++ tailWord_7639484).sum := by decide
  have hdescent : baseEnd_7639484 < baseStart_7639484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639510 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_7639510 : Nat := 118140960795 + 7639510 * 2 ^ 59
def prefixEnd_7639510 : Nat := 4983230072969 + 3 ^ 40 * 7639510 * 2
def baseEnd_7639510 : Nat := 3922740594829510615691539

theorem tailTrace_7639510 : CollatzResearch.WordTrace tailWord_7639510 prefixEnd_7639510 3922740594829510615691539 := by
  unfold tailWord_7639510
  simp only [CollatzResearch.WordTrace]
  refine ⟨17414738784585466829918249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185757213702244979519127989 17414738784585466829918249)
  ·
    refine ⟨13061054088439100122438687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17414738784585466829918249 13061054088439100122438687)
    ·
      refine ⟨19591581132658650183658031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13061054088439100122438687 19591581132658650183658031)
      ·
        refine ⟨29387371698987975275487047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19591581132658650183658031 29387371698987975275487047)
        ·
          refine ⟨44081057548481962913230571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29387371698987975275487047 44081057548481962913230571)
          ·
            refine ⟨66121586322722944369845857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44081057548481962913230571 66121586322722944369845857)
            ·
              refine ⟨49591189742042208277384393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66121586322722944369845857 49591189742042208277384393)
              ·
                refine ⟨37193392306531656208038295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49591189742042208277384393 37193392306531656208038295)
                ·
                  refine ⟨55790088459797484312057443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37193392306531656208038295 55790088459797484312057443)
                  ·
                    refine ⟨83685132689696226468086165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55790088459797484312057443 83685132689696226468086165)
                    ·
                      refine ⟨3922740594829510615691539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83685132689696226468086165 3922740594829510615691539)
                      ·
                        rfl

theorem cell23_7639510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_7639510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639510 prefixEnd_7639510 := by exact prefixLift 7639510
  have htrace : WordTrace (prefixWord ++ tailWord_7639510) baseStart_7639510 baseEnd_7639510 := by
    simpa [prefixWord, tailWord_7639510, baseEnd_7639510] using wordTrace_append hprefix tailTrace_7639510
  have hstable : (prefixWord ++ tailWord_7639510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639510).length < 2 ^ (prefixWord ++ tailWord_7639510).sum := by decide
  have hdescent : baseEnd_7639510 < baseStart_7639510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639514 : List Nat := [3, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2]
def baseStart_7639514 : Nat := 118140960795 + 7639514 * 2 ^ 59
def prefixEnd_7639514 : Nat := 4983230072969 + 3 ^ 40 * 7639514 * 2
def baseEnd_7639514 : Nat := 3922742648752128600041521

theorem tailTrace_7639514 : CollatzResearch.WordTrace tailWord_7639514 prefixEnd_7639514 3922742648752128600041521 := by
  unfold tailWord_7639514
  simp only [CollatzResearch.WordTrace]
  refine ⟨69658991611338244490459399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185757310963568651974558397 69658991611338244490459399)
  ·
    refine ⟨104488487417007366735689099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69658991611338244490459399 104488487417007366735689099)
    ·
      refine ⟨156732731125511050103533649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104488487417007366735689099 156732731125511050103533649)
      ·
        refine ⟨117549548344133287577650237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156732731125511050103533649 117549548344133287577650237)
        ·
          refine ⟨44081080629049982841618839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117549548344133287577650237 44081080629049982841618839)
          ·
            refine ⟨66121620943574974262428259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44081080629049982841618839 66121620943574974262428259)
            ·
              refine ⟨99182431415362461393642389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66121620943574974262428259 99182431415362461393642389)
              ·
                refine ⟨4649176472595115377826987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99182431415362461393642389 4649176472595115377826987)
                ·
                  refine ⟨6973764708892673066740481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4649176472595115377826987 6973764708892673066740481)
                  ·
                    refine ⟨5230323531669504800055361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6973764708892673066740481 5230323531669504800055361)
                    ·
                      refine ⟨3922742648752128600041521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5230323531669504800055361 3922742648752128600041521)
                      ·
                        rfl

theorem cell23_7639514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_7639514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639514 prefixEnd_7639514 := by exact prefixLift 7639514
  have htrace : WordTrace (prefixWord ++ tailWord_7639514) baseStart_7639514 baseEnd_7639514 := by
    simpa [prefixWord, tailWord_7639514, baseEnd_7639514] using wordTrace_append hprefix tailTrace_7639514
  have hstable : (prefixWord ++ tailWord_7639514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639514).length < 2 ^ (prefixWord ++ tailWord_7639514).sum := by decide
  have hdescent : baseEnd_7639514 < baseStart_7639514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639557 : List Nat := [1, 3, 1, 1, 2, 2, 4, 3, 1, 3, 2]
def baseStart_7639557 : Nat := 118140960795 + 7639557 * 2 ^ 59
def prefixEnd_7639557 : Nat := 4983230072969 + 3 ^ 40 * 7639557 * 2
def baseEnd_7639557 : Nat := 3922764728420271931803823

theorem tailTrace_7639557 : CollatzResearch.WordTrace tailWord_7639557 prefixEnd_7639557 3922764728420271931803823 := by
  unfold tailWord_7639557
  simp only [CollatzResearch.WordTrace]
  refine ⟨278637534784197196305652925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185758356522798130870435283 278637534784197196305652925)
  ·
    refine ⟨104489075544073948614619847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278637534784197196305652925 104489075544073948614619847)
    ·
      refine ⟨156733613316110922921929771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104489075544073948614619847 156733613316110922921929771)
      ·
        refine ⟨235100419974166384382894657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156733613316110922921929771 235100419974166384382894657)
        ·
          refine ⟨176325314980624788287170993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235100419974166384382894657 176325314980624788287170993)
          ·
            refine ⟨132243986235468591215378245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176325314980624788287170993 132243986235468591215378245)
            ·
              refine ⟨24795747419150360852883421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132243986235468591215378245 24795747419150360852883421)
              ·
                refine ⟨9298405282181385319831283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24795747419150360852883421 9298405282181385319831283)
                ·
                  refine ⟨13947607923272077979746925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9298405282181385319831283 13947607923272077979746925)
                  ·
                    refine ⟨5230352971227029242405097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13947607923272077979746925 5230352971227029242405097)
                    ·
                      refine ⟨3922764728420271931803823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5230352971227029242405097 3922764728420271931803823)
                      ·
                        rfl

theorem cell23_7639557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 3, 2].length) (baseStart_7639557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639557 prefixEnd_7639557 := by exact prefixLift 7639557
  have htrace : WordTrace (prefixWord ++ tailWord_7639557) baseStart_7639557 baseEnd_7639557 := by
    simpa [prefixWord, tailWord_7639557, baseEnd_7639557] using wordTrace_append hprefix tailTrace_7639557
  have hstable : (prefixWord ++ tailWord_7639557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639557).length < 2 ^ (prefixWord ++ tailWord_7639557).sum := by decide
  have hdescent : baseEnd_7639557 < baseStart_7639557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639573 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_7639573 : Nat := 118140960795 + 7639573 * 2 ^ 59
def prefixEnd_7639573 : Nat := 4983230072969 + 3 ^ 40 * 7639573 * 2
def baseEnd_7639573 : Nat := 3922772944110743869203749

theorem tailTrace_7639573 : CollatzResearch.WordTrace tailWord_7639573 prefixEnd_7639573 3922772944110743869203749 := by
  unfold tailWord_7639573
  simp only [CollatzResearch.WordTrace]
  refine ⟨278638118352139231038235373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185758745568092820692156915 278638118352139231038235373)
  ·
    refine ⟨104489294382052211639338265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278638118352139231038235373 104489294382052211639338265)
    ·
      refine ⟨78366970786539158729503699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104489294382052211639338265 78366970786539158729503699)
      ·
        refine ⟨117550456179808738094255549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78366970786539158729503699 117550456179808738094255549)
        ·
          refine ⟨44081421067428276785345831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117550456179808738094255549 44081421067428276785345831)
          ·
            refine ⟨66122131601142415178018747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44081421067428276785345831 66122131601142415178018747)
            ·
              refine ⟨99183197401713622767028121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66122131601142415178018747 99183197401713622767028121)
              ·
                refine ⟨74387398051285217075271091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99183197401713622767028121 74387398051285217075271091)
                ·
                  refine ⟨111581097076927825612906637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74387398051285217075271091 111581097076927825612906637)
                  ·
                    refine ⟨41842911403847934604839989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111581097076927825612906637 41842911403847934604839989)
                    ·
                      refine ⟨3922772944110743869203749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41842911403847934604839989 3922772944110743869203749)
                      ·
                        rfl

theorem cell23_7639573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_7639573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639573 prefixEnd_7639573 := by exact prefixLift 7639573
  have htrace : WordTrace (prefixWord ++ tailWord_7639573) baseStart_7639573 baseEnd_7639573 := by
    simpa [prefixWord, tailWord_7639573, baseEnd_7639573] using wordTrace_append hprefix tailTrace_7639573
  have hstable : (prefixWord ++ tailWord_7639573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639573).length < 2 ^ (prefixWord ++ tailWord_7639573).sum := by decide
  have hdescent : baseEnd_7639573 < baseStart_7639573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639581 : List Nat := [1, 4, 2, 2, 1, 4, 2, 1, 2, 1, 3]
def baseStart_7639581 : Nat := 118140960795 + 7639581 * 2 ^ 59
def prefixEnd_7639581 : Nat := 4983230072969 + 3 ^ 40 * 7639581 * 2
def baseEnd_7639581 : Nat := 3922777051955979837903713

theorem tailTrace_7639581 : CollatzResearch.WordTrace tailWord_7639581 prefixEnd_7639581 3922777051955979837903713 := by
  unfold tailWord_7639581
  simp only [CollatzResearch.WordTrace]
  refine ⟨278638410136110248404526597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185758940090740165603017731 278638410136110248404526597)
  ·
    refine ⟨52244701900520671575848737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278638410136110248404526597 52244701900520671575848737)
    ·
      refine ⟨39183526425390503681886553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52244701900520671575848737 39183526425390503681886553)
      ·
        refine ⟨29387644819042877761414915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39183526425390503681886553 29387644819042877761414915)
        ·
          refine ⟨44081467228564316642122373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29387644819042877761414915 44081467228564316642122373)
          ·
            refine ⟨8265275105355809370397945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44081467228564316642122373 8265275105355809370397945)
            ·
              refine ⟨6198956329016857027798459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8265275105355809370397945 6198956329016857027798459)
              ·
                refine ⟨9298434493525285541697689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6198956329016857027798459 9298434493525285541697689)
                ·
                  refine ⟨6973825870143964156273267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9298434493525285541697689 6973825870143964156273267)
                  ·
                    refine ⟨10460738805215946234409901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6973825870143964156273267 10460738805215946234409901)
                    ·
                      refine ⟨3922777051955979837903713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10460738805215946234409901 3922777051955979837903713)
                      ·
                        rfl

theorem cell23_7639581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_7639581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639581 prefixEnd_7639581 := by exact prefixLift 7639581
  have htrace : WordTrace (prefixWord ++ tailWord_7639581) baseStart_7639581 baseEnd_7639581 := by
    simpa [prefixWord, tailWord_7639581, baseEnd_7639581] using wordTrace_append hprefix tailTrace_7639581
  have hstable : (prefixWord ++ tailWord_7639581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639581).length < 2 ^ (prefixWord ++ tailWord_7639581).sum := by decide
  have hdescent : baseEnd_7639581 < baseStart_7639581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639583 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 4]
def baseStart_7639583 : Nat := 118140960795 + 7639583 * 2 ^ 59
def prefixEnd_7639583 : Nat := 4983230072969 + 3 ^ 40 * 7639583 * 2
def baseEnd_7639583 : Nat := 3922778078917288830078703

theorem tailTrace_7639583 : CollatzResearch.WordTrace tailWord_7639583 prefixEnd_7639583 3922778078917288830078703 := by
  unfold tailWord_7639583
  simp only [CollatzResearch.WordTrace]
  refine ⟨278638483082103002746099403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185758988721402001830732935 278638483082103002746099403)
  ·
    refine ⟨417957724623154504119149105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278638483082103002746099403 417957724623154504119149105)
    ·
      refine ⟨313468293467365878089361829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417957724623154504119149105 313468293467365878089361829)
      ·
        refine ⟨58775305025131102141755343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313468293467365878089361829 58775305025131102141755343)
        ·
          refine ⟨88162957537696653212633015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58775305025131102141755343 88162957537696653212633015)
          ·
            refine ⟨132244436306544979818949523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88162957537696653212633015 132244436306544979818949523)
            ·
              refine ⟨198366654459817469728424285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132244436306544979818949523 198366654459817469728424285)
              ·
                refine ⟨74387495422431551148159107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198366654459817469728424285 74387495422431551148159107)
                ·
                  refine ⟨111581243133647326722238661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74387495422431551148159107 111581243133647326722238661)
                  ·
                    refine ⟨20921483087558873760419749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111581243133647326722238661 20921483087558873760419749)
                    ·
                      refine ⟨3922778078917288830078703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20921483087558873760419749 3922778078917288830078703)
                      ·
                        rfl

theorem cell23_7639583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_7639583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639583 prefixEnd_7639583 := by exact prefixLift 7639583
  have htrace : WordTrace (prefixWord ++ tailWord_7639583) baseStart_7639583 baseEnd_7639583 := by
    simpa [prefixWord, tailWord_7639583, baseEnd_7639583] using wordTrace_append hprefix tailTrace_7639583
  have hstable : (prefixWord ++ tailWord_7639583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639583).length < 2 ^ (prefixWord ++ tailWord_7639583).sum := by decide
  have hdescent : baseEnd_7639583 < baseStart_7639583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639591 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_7639591 : Nat := 118140960795 + 7639591 * 2 ^ 59
def prefixEnd_7639591 : Nat := 4983230072969 + 3 ^ 40 * 7639591 * 2
def baseEnd_7639591 : Nat := 3922782186762524798778667

theorem tailTrace_7639591 : CollatzResearch.WordTrace tailWord_7639591 prefixEnd_7639591 3922782186762524798778667 := by
  unfold tailWord_7639591
  simp only [CollatzResearch.WordTrace]
  refine ⟨278638774866074020112390627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185759183244049346741593751 278638774866074020112390627)
  ·
    refine ⟨417958162299111030168585941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278638774866074020112390627 417958162299111030168585941)
    ·
      refine ⟨9795894428885414769576233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 417958162299111030168585941 9795894428885414769576233)
      ·
        refine ⟨7346920821664061077182175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9795894428885414769576233 7346920821664061077182175)
        ·
          refine ⟨11020381232496091615773263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7346920821664061077182175 11020381232496091615773263)
          ·
            refine ⟨16530571848744137423659895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11020381232496091615773263 16530571848744137423659895)
            ·
              refine ⟨24795857773116206135489843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16530571848744137423659895 24795857773116206135489843)
              ·
                refine ⟨37193786659674309203234765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24795857773116206135489843 37193786659674309203234765)
                ·
                  refine ⟨13947669997377865951213037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37193786659674309203234765 13947669997377865951213037)
                  ·
                    refine ⟨5230376249016699731704889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13947669997377865951213037 5230376249016699731704889)
                    ·
                      refine ⟨3922782186762524798778667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5230376249016699731704889 3922782186762524798778667)
                      ·
                        rfl

theorem cell23_7639591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_7639591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639591 prefixEnd_7639591 := by exact prefixLift 7639591
  have htrace : WordTrace (prefixWord ++ tailWord_7639591) baseStart_7639591 baseEnd_7639591 := by
    simpa [prefixWord, tailWord_7639591, baseEnd_7639591] using wordTrace_append hprefix tailTrace_7639591
  have hstable : (prefixWord ++ tailWord_7639591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639591).length < 2 ^ (prefixWord ++ tailWord_7639591).sum := by decide
  have hdescent : baseEnd_7639591 < baseStart_7639591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639627 : List Nat := [1, 1, 1, 1, 3, 1, 8, 2, 5]
def baseStart_7639627 : Nat := 118140960795 + 7639627 * 2 ^ 59
def prefixEnd_7639627 : Nat := 4983230072969 + 3 ^ 40 * 7639627 * 2
def baseEnd_7639627 : Nat := 435866741340676295325389

theorem tailTrace_7639627 : CollatzResearch.WordTrace tailWord_7639627 prefixEnd_7639627 435866741340676295325389 := by
  unfold tailWord_7639627
  simp only [CollatzResearch.WordTrace]
  refine ⟨278640087893943598260701135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185760058595962398840467423 278640087893943598260701135)
  ·
    refine ⟨417960131840915397391051703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278640087893943598260701135 417960131840915397391051703)
    ·
      refine ⟨626940197761373096086577555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417960131840915397391051703 626940197761373096086577555)
      ·
        refine ⟨940410296642059644129866333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626940197761373096086577555 940410296642059644129866333)
        ·
          refine ⟨352653861240772366548699875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 940410296642059644129866333 352653861240772366548699875)
          ·
            refine ⟨528980791861158549823049813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352653861240772366548699875 528980791861158549823049813)
            ·
              refine ⟨6198993654622951755738865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 528980791861158549823049813 6198993654622951755738865)
              ·
                refine ⟨4649245240967213816804149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6198993654622951755738865 4649245240967213816804149)
                ·
                  refine ⟨435866741340676295325389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4649245240967213816804149 435866741340676295325389)
                  ·
                    rfl

theorem cell23_7639627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 5].length) (baseStart_7639627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639627 prefixEnd_7639627 := by exact prefixLift 7639627
  have htrace : WordTrace (prefixWord ++ tailWord_7639627) baseStart_7639627 baseEnd_7639627 := by
    simpa [prefixWord, tailWord_7639627, baseEnd_7639627] using wordTrace_append hprefix tailTrace_7639627
  have hstable : (prefixWord ++ tailWord_7639627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639627).length < 2 ^ (prefixWord ++ tailWord_7639627).sum := by decide
  have hdescent : baseEnd_7639627 < baseStart_7639627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639687 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 3, 4]
def baseStart_7639687 : Nat := 118140960795 + 7639687 * 2 ^ 59
def prefixEnd_7639687 : Nat := 4983230072969 + 3 ^ 40 * 7639687 * 2
def baseEnd_7639687 : Nat := 1307610493635118807726075

theorem tailTrace_7639687 : CollatzResearch.WordTrace tailWord_7639687 prefixEnd_7639687 1307610493635118807726075 := by
  unfold tailWord_7639687
  simp only [CollatzResearch.WordTrace]
  refine ⟨278642276273726228507885315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185761517515817485671923543 278642276273726228507885315)
  ·
    refine ⟨417963414410589342761827973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278642276273726228507885315 417963414410589342761827973)
    ·
      refine ⟨78368140201985501767842745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417963414410589342761827973 78368140201985501767842745)
      ·
        refine ⟨58776105151489126325882059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78368140201985501767842745 58776105151489126325882059)
        ·
          refine ⟨88164157727233689488823089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58776105151489126325882059 88164157727233689488823089)
          ·
            refine ⟨66123118295425267116617317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88164157727233689488823089 66123118295425267116617317)
            ·
              refine ⟨12398084680392237584365747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66123118295425267116617317 12398084680392237584365747)
              ·
                refine ⟨18597127020588356376548621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12398084680392237584365747 18597127020588356376548621)
                ·
                  refine ⟨6973922632720633641205733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18597127020588356376548621 6973922632720633641205733)
                  ·
                    refine ⟨1307610493635118807726075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6973922632720633641205733 1307610493635118807726075)
                    ·
                      rfl

theorem cell23_7639687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_7639687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639687 prefixEnd_7639687 := by exact prefixLift 7639687
  have htrace : WordTrace (prefixWord ++ tailWord_7639687) baseStart_7639687 baseEnd_7639687 := by
    simpa [prefixWord, tailWord_7639687, baseEnd_7639687] using wordTrace_append hprefix tailTrace_7639687
  have hstable : (prefixWord ++ tailWord_7639687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639687).length < 2 ^ (prefixWord ++ tailWord_7639687).sum := by decide
  have hdescent : baseEnd_7639687 < baseStart_7639687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639730 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_7639730 : Nat := 118140960795 + 7639730 * 2 ^ 59
def prefixEnd_7639730 : Nat := 4983230072969 + 3 ^ 40 * 7639730 * 2
def baseEnd_7639730 : Nat := 1307617853524499918313509

theorem tailTrace_7639730 : CollatzResearch.WordTrace tailWord_7639730 prefixEnd_7639730 1307617853524499918313509 := by
  unfold tailWord_7639730
  simp only [CollatzResearch.WordTrace]
  refine ⟨69660961153142611712925161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185762563075046964567800429 69660961153142611712925161)
  ·
    refine ⟨52245720864856958784693871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69660961153142611712925161 52245720864856958784693871)
    ·
      refine ⟨78368581297285438177040807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52245720864856958784693871 78368581297285438177040807)
      ·
        refine ⟨117552871945928157265561211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78368581297285438177040807 117552871945928157265561211)
        ·
          refine ⟨176329307918892235898341817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117552871945928157265561211 176329307918892235898341817)
          ·
            refine ⟨132246980939169176923756363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176329307918892235898341817 132246980939169176923756363)
            ·
              refine ⟨198370471408753765385634545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132246980939169176923756363 198370471408753765385634545)
              ·
                refine ⟨148777853556565324039225909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198370471408753765385634545 148777853556565324039225909)
                ·
                  refine ⟨13947923770927999128677429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148777853556565324039225909 13947923770927999128677429)
                  ·
                    refine ⟨1307617853524499918313509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13947923770927999128677429 1307617853524499918313509)
                    ·
                      rfl

theorem cell23_7639730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_7639730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639730 prefixEnd_7639730 := by exact prefixLift 7639730
  have htrace : WordTrace (prefixWord ++ tailWord_7639730) baseStart_7639730 baseEnd_7639730 := by
    simpa [prefixWord, tailWord_7639730, baseEnd_7639730] using wordTrace_append hprefix tailTrace_7639730
  have hstable : (prefixWord ++ tailWord_7639730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639730).length < 2 ^ (prefixWord ++ tailWord_7639730).sum := by decide
  have hdescent : baseEnd_7639730 < baseStart_7639730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639744 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 3, 1, 3]
def baseStart_7639744 : Nat := 118140960795 + 7639744 * 2 ^ 59
def prefixEnd_7639744 : Nat := 4983230072969 + 3 ^ 40 * 7639744 * 2
def baseEnd_7639744 : Nat := 3922860749302662700165463

theorem tailTrace_7639744 : CollatzResearch.WordTrace tailWord_7639744 prefixEnd_7639744 3922860749302662700165463 := by
  unfold tailWord_7639744
  simp only [CollatzResearch.WordTrace]
  refine ⟨139322177617259863621355143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185762903489679818161806857 139322177617259863621355143)
  ·
    refine ⟨208983266425889795432032715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139322177617259863621355143 208983266425889795432032715)
    ·
      refine ⟨313474899638834693148049073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208983266425889795432032715 313474899638834693148049073)
      ·
        refine ⟨235106174729126019861036805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313474899638834693148049073 235106174729126019861036805)
        ·
          refine ⟨44082407761711128723944401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235106174729126019861036805 44082407761711128723944401)
          ·
            refine ⟨33061805821283346542958301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44082407761711128723944401 33061805821283346542958301)
            ·
              refine ⟨12398177182981254953609363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33061805821283346542958301 12398177182981254953609363)
              ·
                refine ⟨18597265774471882430414045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12398177182981254953609363 18597265774471882430414045)
                ·
                  refine ⟨6973974665426955911405267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18597265774471882430414045 6973974665426955911405267)
                  ·
                    refine ⟨10460961998140433867107901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6973974665426955911405267 10460961998140433867107901)
                    ·
                      refine ⟨3922860749302662700165463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10460961998140433867107901 3922860749302662700165463)
                      ·
                        rfl

theorem cell23_7639744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_7639744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639744 prefixEnd_7639744 := by exact prefixLift 7639744
  have htrace : WordTrace (prefixWord ++ tailWord_7639744) baseStart_7639744 baseEnd_7639744 := by
    simpa [prefixWord, tailWord_7639744, baseEnd_7639744] using wordTrace_append hprefix tailTrace_7639744
  have hstable : (prefixWord ++ tailWord_7639744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639744).length < 2 ^ (prefixWord ++ tailWord_7639744).sum := by decide
  have hdescent : baseEnd_7639744 < baseStart_7639744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639764 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_7639764 : Nat := 118140960795 + 7639764 * 2 ^ 59
def prefixEnd_7639764 : Nat := 4983230072969 + 3 ^ 40 * 7639764 * 2
def baseEnd_7639764 : Nat := 1307623672971917540638457

theorem tailTrace_7639764 : CollatzResearch.WordTrace tailWord_7639764 prefixEnd_7639764 1307623672971917540638457 := by
  unfold tailWord_7639764
  simp only [CollatzResearch.WordTrace]
  refine ⟨139322542347223635329219173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185763389796298180438958897 139322542347223635329219173)
  ·
    refine ⟨26122976690104431624228595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139322542347223635329219173 26122976690104431624228595)
    ·
      refine ⟨39184465035156647436342893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26122976690104431624228595 39184465035156647436342893)
      ·
        refine ⟨14694174388183742788628585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39184465035156647436342893 14694174388183742788628585)
        ·
          refine ⟨11020630791137807091471439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14694174388183742788628585 11020630791137807091471439)
          ·
            refine ⟨16530946186706710637207159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11020630791137807091471439 16530946186706710637207159)
            ·
              refine ⟨24796419280060065955810739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16530946186706710637207159 24796419280060065955810739)
              ·
                refine ⟨37194628920090098933716109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24796419280060065955810739 37194628920090098933716109)
                ·
                  refine ⟨13947985845033787100143541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37194628920090098933716109 13947985845033787100143541)
                  ·
                    refine ⟨1307623672971917540638457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13947985845033787100143541 1307623672971917540638457)
                    ·
                      rfl

theorem cell23_7639764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_7639764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639764 prefixEnd_7639764 := by exact prefixLift 7639764
  have htrace : WordTrace (prefixWord ++ tailWord_7639764) baseStart_7639764 baseEnd_7639764 := by
    simpa [prefixWord, tailWord_7639764, baseEnd_7639764] using wordTrace_append hprefix tailTrace_7639764
  have hstable : (prefixWord ++ tailWord_7639764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639764).length < 2 ^ (prefixWord ++ tailWord_7639764).sum := by decide
  have hdescent : baseEnd_7639764 < baseStart_7639764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639767 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 4]
def baseStart_7639767 : Nat := 118140960795 + 7639767 * 2 ^ 59
def prefixEnd_7639767 : Nat := 4983230072969 + 3 ^ 40 * 7639767 * 2
def baseEnd_7639767 : Nat := 3922872559357716110177857

theorem tailTrace_7639767 : CollatzResearch.WordTrace tailWord_7639767 prefixEnd_7639767 3922872559357716110177857 := by
  unfold tailWord_7639767
  simp only [CollatzResearch.WordTrace]
  refine ⟨278645194113436402170797555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185763462742290934780531703 278645194113436402170797555)
  ·
    refine ⟨417967791170154603256196333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278645194113436402170797555 417967791170154603256196333)
    ·
      refine ⟨156737921688807976221073625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417967791170154603256196333 156737921688807976221073625)
      ·
        refine ⟨117553441266605982165805219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156737921688807976221073625 117553441266605982165805219)
        ·
          refine ⟨176330161899908973248707829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117553441266605982165805219 176330161899908973248707829)
          ·
            refine ⟨16530952678116466242066359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176330161899908973248707829 16530952678116466242066359)
            ·
              refine ⟨24796429017174699363099539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16530952678116466242066359 24796429017174699363099539)
              ·
                refine ⟨37194643525762049044649309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24796429017174699363099539 37194643525762049044649309)
                ·
                  refine ⟨13947991322160768391743491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37194643525762049044649309 13947991322160768391743491)
                  ·
                    refine ⟨20921986983241152587615237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13947991322160768391743491 20921986983241152587615237)
                    ·
                      refine ⟨3922872559357716110177857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20921986983241152587615237 3922872559357716110177857)
                      ·
                        rfl

theorem cell23_7639767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_7639767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639767 prefixEnd_7639767 := by exact prefixLift 7639767
  have htrace : WordTrace (prefixWord ++ tailWord_7639767) baseStart_7639767 baseEnd_7639767 := by
    simpa [prefixWord, tailWord_7639767, baseEnd_7639767] using wordTrace_append hprefix tailTrace_7639767
  have hstable : (prefixWord ++ tailWord_7639767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639767).length < 2 ^ (prefixWord ++ tailWord_7639767).sum := by decide
  have hdescent : baseEnd_7639767 < baseStart_7639767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639777 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 1, 6]
def baseStart_7639777 : Nat := 118140960795 + 7639777 * 2 ^ 59
def prefixEnd_7639777 : Nat := 4983230072969 + 3 ^ 40 * 7639777 * 2
def baseEnd_7639777 : Nat := 1307625898054753690350937

theorem tailTrace_7639777 : CollatzResearch.WordTrace tailWord_7639777 prefixEnd_7639777 1307625898054753690350937 := by
  unfold tailWord_7639777
  simp only [CollatzResearch.WordTrace]
  refine ⟨278645558843400173878661585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185763705895600115919107723 278645558843400173878661585)
  ·
    refine ⟨208984169132550130408996189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278645558843400173878661585 208984169132550130408996189)
    ·
      refine ⟨78369063424706298903373571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208984169132550130408996189 78369063424706298903373571)
      ·
        refine ⟨117553595137059448355060357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78369063424706298903373571 117553595137059448355060357)
        ·
          refine ⟨22041299088198646566573817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117553595137059448355060357 22041299088198646566573817)
          ·
            refine ⟨16530974316148984924930363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22041299088198646566573817 16530974316148984924930363)
            ·
              refine ⟨24796461474223477387395545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16530974316148984924930363 24796461474223477387395545)
              ·
                refine ⟨18597346105667608040546659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24796461474223477387395545 18597346105667608040546659)
                ·
                  refine ⟨27896019158501412060819989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18597346105667608040546659 27896019158501412060819989)
                  ·
                    refine ⟨1307625898054753690350937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27896019158501412060819989 1307625898054753690350937)
                    ·
                      rfl

theorem cell23_7639777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_7639777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639777 prefixEnd_7639777 := by exact prefixLift 7639777
  have htrace : WordTrace (prefixWord ++ tailWord_7639777) baseStart_7639777 baseEnd_7639777 := by
    simpa [prefixWord, tailWord_7639777, baseEnd_7639777] using wordTrace_append hprefix tailTrace_7639777
  have hstable : (prefixWord ++ tailWord_7639777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639777).length < 2 ^ (prefixWord ++ tailWord_7639777).sum := by decide
  have hdescent : baseEnd_7639777 < baseStart_7639777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639790 : List Nat := [4, 1, 2, 1, 1, 14]
def baseStart_7639790 : Nat := 118140960795 + 7639790 * 2 ^ 59
def prefixEnd_7639790 : Nat := 4983230072969 + 3 ^ 40 * 7639790 * 2
def baseEnd_7639790 : Nat := 16143557075772714074857

theorem tailTrace_7639790 : CollatzResearch.WordTrace tailWord_7639790 prefixEnd_7639790 16143557075772714074857 := by
  unfold tailWord_7639790
  simp only [CollatzResearch.WordTrace]
  refine ⟨34830754124044134637360603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185764021994902051399256549 34830754124044134637360603)
  ·
    refine ⟨52246131186066201956040905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34830754124044134637360603 52246131186066201956040905)
    ·
      refine ⟨39184598389549651467030679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52246131186066201956040905 39184598389549651467030679)
      ·
        refine ⟨58776897584324477200546019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39184598389549651467030679 58776897584324477200546019)
        ·
          refine ⟨88165346376486715800819029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58776897584324477200546019 88165346376486715800819029)
          ·
            refine ⟨16143557075772714074857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 88165346376486715800819029 16143557075772714074857)
            ·
              rfl

theorem cell23_7639790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 14].length) (baseStart_7639790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639790 prefixEnd_7639790 := by exact prefixLift 7639790
  have htrace : WordTrace (prefixWord ++ tailWord_7639790) baseStart_7639790 baseEnd_7639790 := by
    simpa [prefixWord, tailWord_7639790, baseEnd_7639790] using wordTrace_append hprefix tailTrace_7639790
  have hstable : (prefixWord ++ tailWord_7639790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639790).length < 2 ^ (prefixWord ++ tailWord_7639790).sum := by decide
  have hdescent : baseEnd_7639790 < baseStart_7639790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639794 : List Nat := [3, 2, 1, 3, 1, 2, 1, 4, 2, 4]
def baseStart_7639794 : Nat := 118140960795 + 7639794 * 2 ^ 59
def prefixEnd_7639794 : Nat := 4983230072969 + 3 ^ 40 * 7639794 * 2
def baseEnd_7639794 : Nat := 1307628807778462501513411

theorem tailTrace_7639794 : CollatzResearch.WordTrace tailWord_7639794 prefixEnd_7639794 1307628807778462501513411 := by
  unfold tailWord_7639794
  simp only [CollatzResearch.WordTrace]
  refine ⟨69661544721084646445507609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185764119256225723854686957 69661544721084646445507609)
  ·
    refine ⟨52246158540813484834130707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69661544721084646445507609 52246158540813484834130707)
    ·
      refine ⟨78369237811220227251196061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52246158540813484834130707 78369237811220227251196061)
      ·
        refine ⟨29388464179207585219198523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78369237811220227251196061 29388464179207585219198523)
        ·
          refine ⟨44082696268811377828797785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29388464179207585219198523 44082696268811377828797785)
          ·
            refine ⟨33062022201608533371598339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44082696268811377828797785 33062022201608533371598339)
            ·
              refine ⟨49593033302412800057397509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33062022201608533371598339 49593033302412800057397509)
              ·
                refine ⟨9298693744202400010762033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49593033302412800057397509 9298693744202400010762033)
                ·
                  refine ⟨6974020308151800008071525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9298693744202400010762033 6974020308151800008071525)
                  ·
                    refine ⟨1307628807778462501513411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6974020308151800008071525 1307628807778462501513411)
                    ·
                      rfl

theorem cell23_7639794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_7639794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639794 prefixEnd_7639794 := by exact prefixLift 7639794
  have htrace : WordTrace (prefixWord ++ tailWord_7639794) baseStart_7639794 baseEnd_7639794 := by
    simpa [prefixWord, tailWord_7639794, baseEnd_7639794] using wordTrace_append hprefix tailTrace_7639794
  have hstable : (prefixWord ++ tailWord_7639794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639794).length < 2 ^ (prefixWord ++ tailWord_7639794).sum := by decide
  have hdescent : baseEnd_7639794 < baseStart_7639794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639817 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 1, 3, 3]
def baseStart_7639817 : Nat := 118140960795 + 7639817 * 2 ^ 59
def prefixEnd_7639817 : Nat := 4983230072969 + 3 ^ 40 * 7639817 * 2
def baseEnd_7639817 : Nat := 3922898233390440914552627

theorem tailTrace_7639817 : CollatzResearch.WordTrace tailWord_7639817 prefixEnd_7639817 3922898233390440914552627 := by
  unfold tailWord_7639817
  simp only [CollatzResearch.WordTrace]
  refine ⟨278647017763255260710117705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185764678508836840473411803 278647017763255260710117705)
  ·
    refine ⟨208985263322441445532588279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278647017763255260710117705 208985263322441445532588279)
    ·
      refine ⟨313477894983662168298882419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208985263322441445532588279 313477894983662168298882419)
      ·
        refine ⟨470216842475493252448323629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313477894983662168298882419 470216842475493252448323629)
        ·
          refine ⟨176331315928309969668121361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 470216842475493252448323629 176331315928309969668121361)
          ·
            refine ⟨132248486946232477251091021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176331315928309969668121361 132248486946232477251091021)
            ·
              refine ⟨49593182604837178969159133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132248486946232477251091021 49593182604837178969159133)
              ·
                refine ⟨18597443476813942113434675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49593182604837178969159133 18597443476813942113434675)
                ·
                  refine ⟨27896165215220913170152013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18597443476813942113434675 27896165215220913170152013)
                  ·
                    refine ⟨10461061955707842438807005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27896165215220913170152013 10461061955707842438807005)
                    ·
                      refine ⟨3922898233390440914552627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10461061955707842438807005 3922898233390440914552627)
                      ·
                        rfl

theorem cell23_7639817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 3, 3].length) (baseStart_7639817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639817 prefixEnd_7639817 := by exact prefixLift 7639817
  have htrace : WordTrace (prefixWord ++ tailWord_7639817) baseStart_7639817 baseEnd_7639817 := by
    simpa [prefixWord, tailWord_7639817, baseEnd_7639817] using wordTrace_append hprefix tailTrace_7639817
  have hstable : (prefixWord ++ tailWord_7639817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639817).length < 2 ^ (prefixWord ++ tailWord_7639817).sum := by decide
  have hdescent : baseEnd_7639817 < baseStart_7639817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639820 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 4, 7]
def baseStart_7639820 : Nat := 118140960795 + 7639820 * 2 ^ 59
def prefixEnd_7639820 : Nat := 4983230072969 + 3 ^ 40 * 7639820 * 2
def baseEnd_7639820 : Nat := 1307633257944134800938371

theorem tailTrace_7639820 : CollatzResearch.WordTrace tailWord_7639820 prefixEnd_7639820 1307633257944134800938371 := by
  unfold tailWord_7639820
  simp only [CollatzResearch.WordTrace]
  refine ⟨139323563591122196111238457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185764751454829594814984609 139323563591122196111238457)
  ·
    refine ⟨104492672693341647083428843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139323563591122196111238457 104492672693341647083428843)
    ·
      refine ⟨156739009040012470625143265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104492672693341647083428843 156739009040012470625143265)
      ·
        refine ⟨117554256780009352968857449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156739009040012470625143265 117554256780009352968857449)
        ·
          refine ⟨88165692585007014726643087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117554256780009352968857449 88165692585007014726643087)
          ·
            refine ⟨132248538877510522089964631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88165692585007014726643087 132248538877510522089964631)
            ·
              refine ⟨198372808316265783134946947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132248538877510522089964631 198372808316265783134946947)
              ·
                refine ⟨297559212474398674702420421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198372808316265783134946947 297559212474398674702420421)
                ·
                  refine ⟨55792352338949751506703829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297559212474398674702420421 55792352338949751506703829)
                  ·
                    refine ⟨1307633257944134800938371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55792352338949751506703829 1307633257944134800938371)
                    ·
                      rfl

theorem cell23_7639820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_7639820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639820 prefixEnd_7639820 := by exact prefixLift 7639820
  have htrace : WordTrace (prefixWord ++ tailWord_7639820) baseStart_7639820 baseEnd_7639820 := by
    simpa [prefixWord, tailWord_7639820, baseEnd_7639820] using wordTrace_append hprefix tailTrace_7639820
  have hstable : (prefixWord ++ tailWord_7639820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639820).length < 2 ^ (prefixWord ++ tailWord_7639820).sum := by decide
  have hdescent : baseEnd_7639820 < baseStart_7639820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639834 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3]
def baseStart_7639834 : Nat := 118140960795 + 7639834 * 2 ^ 59
def prefixEnd_7639834 : Nat := 4983230072969 + 3 ^ 40 * 7639834 * 2
def baseEnd_7639834 : Nat := 3922906962561567348040049

theorem tailTrace_7639834 : CollatzResearch.WordTrace tailWord_7639834 prefixEnd_7639834 3922906962561567348040049 := by
  unfold tailWord_7639834
  simp only [CollatzResearch.WordTrace]
  refine ⟨69661909451048418153371639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185765091869462448408991037 69661909451048418153371639)
  ·
    refine ⟨104492864176572627230057459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69661909451048418153371639 104492864176572627230057459)
    ·
      refine ⟨156739296264858940845086189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104492864176572627230057459 156739296264858940845086189)
      ·
        refine ⟨58777236099322102816907321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156739296264858940845086189 58777236099322102816907321)
        ·
          refine ⟨44082927074491577112680491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58777236099322102816907321 44082927074491577112680491)
          ·
            refine ⟨66124390611737365669020737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44082927074491577112680491 66124390611737365669020737)
            ·
              refine ⟨49593292958803024251765553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66124390611737365669020737 49593292958803024251765553)
              ·
                refine ⟨37194969719102268188824165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49593292958803024251765553 37194969719102268188824165)
                ·
                  refine ⟨6974056822331675285404531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37194969719102268188824165 6974056822331675285404531)
                  ·
                    refine ⟨10461085233497512928106797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6974056822331675285404531 10461085233497512928106797)
                    ·
                      refine ⟨3922906962561567348040049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10461085233497512928106797 3922906962561567348040049)
                      ·
                        rfl

theorem cell23_7639834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_7639834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639834 prefixEnd_7639834 := by exact prefixLift 7639834
  have htrace : WordTrace (prefixWord ++ tailWord_7639834) baseStart_7639834 baseEnd_7639834 := by
    simpa [prefixWord, tailWord_7639834, baseEnd_7639834] using wordTrace_append hprefix tailTrace_7639834
  have hstable : (prefixWord ++ tailWord_7639834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639834).length < 2 ^ (prefixWord ++ tailWord_7639834).sum := by decide
  have hdescent : baseEnd_7639834 < baseStart_7639834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639925 : List Nat := [1, 3, 4, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_7639925 : Nat := 118140960795 + 7639925 * 2 ^ 59
def prefixEnd_7639925 : Nat := 4983230072969 + 3 ^ 40 * 7639925 * 2
def baseEnd_7639925 : Nat := 3922953689301126492002131

theorem tailTrace_7639925 : CollatzResearch.WordTrace tailWord_7639925 prefixEnd_7639925 3922953689301126492002131 := by
  unfold tailWord_7639925
  simp only [CollatzResearch.WordTrace]
  refine ⟨278650956846863995155049229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185767304564575996770032819 278650956846863995155049229)
  ·
    refine ⟨104494108817573998183143461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278650956846863995155049229 104494108817573998183143461)
    ·
      refine ⟨19592645403295124659339399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104494108817573998183143461 19592645403295124659339399)
      ·
        refine ⟨29388968104942686989009099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19592645403295124659339399 29388968104942686989009099)
        ·
          refine ⟨44083452157414030483513649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29388968104942686989009099 44083452157414030483513649)
          ·
            refine ⟨33062589118060522862635237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44083452157414030483513649 33062589118060522862635237)
            ·
              refine ⟨6199235459636348036744107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33062589118060522862635237 6199235459636348036744107)
              ·
                refine ⟨9298853189454522055116161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6199235459636348036744107 9298853189454522055116161)
                ·
                  refine ⟨6974139892090891541337121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9298853189454522055116161 6974139892090891541337121)
                  ·
                    refine ⟨5230604919068168656002841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6974139892090891541337121 5230604919068168656002841)
                    ·
                      refine ⟨3922953689301126492002131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5230604919068168656002841 3922953689301126492002131)
                      ·
                        rfl

theorem cell23_7639925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_7639925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639925 prefixEnd_7639925 := by exact prefixLift 7639925
  have htrace : WordTrace (prefixWord ++ tailWord_7639925) baseStart_7639925 baseEnd_7639925 := by
    simpa [prefixWord, tailWord_7639925, baseEnd_7639925] using wordTrace_append hprefix tailTrace_7639925
  have hstable : (prefixWord ++ tailWord_7639925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639925).length < 2 ^ (prefixWord ++ tailWord_7639925).sum := by decide
  have hdescent : baseEnd_7639925 < baseStart_7639925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639944 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 2, 5]
def baseStart_7639944 : Nat := 118140960795 + 7639944 * 2 ^ 59
def prefixEnd_7639944 : Nat := 4983230072969 + 3 ^ 40 * 7639944 * 2
def baseEnd_7639944 : Nat := 1307654481811187305888181

theorem tailTrace_7639944 : CollatzResearch.WordTrace tailWord_7639944 prefixEnd_7639944 1307654481811187305888181 := by
  unfold tailWord_7639944
  simp only [CollatzResearch.WordTrace]
  refine ⟨139325824916897580699995443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185767766555863440933327257 139325824916897580699995443)
  ·
    refine ⟨208988737375346371049993165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139325824916897580699995443 208988737375346371049993165)
    ·
      refine ⟨78370776515754889143747437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208988737375346371049993165 78370776515754889143747437)
      ·
        refine ⟨29389041193408083428905289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78370776515754889143747437 29389041193408083428905289)
        ·
          refine ⟨22041780895056062571678967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29389041193408083428905289 22041780895056062571678967)
          ·
            refine ⟨33062671342584093857518451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22041780895056062571678967 33062671342584093857518451)
            ·
              refine ⟨49594007013876140786277677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33062671342584093857518451 49594007013876140786277677)
              ·
                refine ⟨18597752630203552794854129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49594007013876140786277677 18597752630203552794854129)
                ·
                  refine ⟨13948314472652664596140597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18597752630203552794854129 13948314472652664596140597)
                  ·
                    refine ⟨1307654481811187305888181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13948314472652664596140597 1307654481811187305888181)
                    ·
                      rfl

theorem cell23_7639944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_7639944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639944 prefixEnd_7639944 := by exact prefixLift 7639944
  have htrace : WordTrace (prefixWord ++ tailWord_7639944) baseStart_7639944 baseEnd_7639944 := by
    simpa [prefixWord, tailWord_7639944, baseEnd_7639944] using wordTrace_append hprefix tailTrace_7639944
  have hstable : (prefixWord ++ tailWord_7639944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639944).length < 2 ^ (prefixWord ++ tailWord_7639944).sum := by decide
  have hdescent : baseEnd_7639944 < baseStart_7639944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7639947 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 4]
def baseStart_7639947 : Nat := 118140960795 + 7639947 * 2 ^ 59
def prefixEnd_7639947 : Nat := 4983230072969 + 3 ^ 40 * 7639947 * 2
def baseEnd_7639947 : Nat := 3922964985875525405927029

theorem tailTrace_7639947 : CollatzResearch.WordTrace tailWord_7639947 prefixEnd_7639947 3922964985875525405927029 := by
  unfold tailWord_7639947
  simp only [CollatzResearch.WordTrace]
  refine ⟨278651759252784292912350095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185767839501856195274900063 278651759252784292912350095)
  ·
    refine ⟨417977638879176439368525143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278651759252784292912350095 417977638879176439368525143)
    ·
      refine ⟨626966458318764659052787715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417977638879176439368525143 626966458318764659052787715)
      ·
        refine ⟨940449687478146988579181573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626966458318764659052787715 940449687478146988579181573)
        ·
          refine ⟨176334316402152560358596545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 940449687478146988579181573 176334316402152560358596545)
          ·
            refine ⟨132250737301614420268947409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176334316402152560358596545 132250737301614420268947409)
            ·
              refine ⟨99188052976210815201710557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132250737301614420268947409 99188052976210815201710557)
              ·
                refine ⟨37195519866079055700641459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99188052976210815201710557 37195519866079055700641459)
                ·
                  refine ⟨55793279799118583550962189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37195519866079055700641459 55793279799118583550962189)
                  ·
                    refine ⟨20922479924669468831610821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55793279799118583550962189 20922479924669468831610821)
                    ·
                      refine ⟨3922964985875525405927029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20922479924669468831610821 3922964985875525405927029)
                      ·
                        rfl

theorem cell23_7639947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 4].length) (baseStart_7639947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7639947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7639947 prefixEnd_7639947 := by exact prefixLift 7639947
  have htrace : WordTrace (prefixWord ++ tailWord_7639947) baseStart_7639947 baseEnd_7639947 := by
    simpa [prefixWord, tailWord_7639947, baseEnd_7639947] using wordTrace_append hprefix tailTrace_7639947
  have hstable : (prefixWord ++ tailWord_7639947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7639947).length < 2 ^ (prefixWord ++ tailWord_7639947).sum := by decide
  have hdescent : baseEnd_7639947 < baseStart_7639947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7639947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640065 : List Nat := [1, 2, 4, 1, 2, 2, 3, 3, 1, 1, 3]
def baseStart_7640065 : Nat := 118140960795 + 7640065 * 2 ^ 59
def prefixEnd_7640065 : Nat := 4983230072969 + 3 ^ 40 * 7640065 * 2
def baseEnd_7640065 : Nat := 3923025576592755944251487

theorem tailTrace_7640065 : CollatzResearch.WordTrace tailWord_7640065 prefixEnd_7640065 3923025576592755944251487 := by
  unfold tailWord_7640065
  simp only [CollatzResearch.WordTrace]
  refine ⟨278656063066356799065145649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185770708710904532710097099 278656063066356799065145649)
  ·
    refine ⟨208992047299767599298859237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278656063066356799065145649 208992047299767599298859237)
    ·
      refine ⟨39186008868706424868536107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208992047299767599298859237 39186008868706424868536107)
      ·
        refine ⟨58779013303059637302804161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39186008868706424868536107 58779013303059637302804161)
        ·
          refine ⟨44084259977294727977103121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58779013303059637302804161 44084259977294727977103121)
          ·
            refine ⟨33063194982971045982827341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44084259977294727977103121 33063194982971045982827341)
            ·
              refine ⟨12398698118614142243560253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33063194982971045982827341 12398698118614142243560253)
              ·
                refine ⟨4649511794480303341335095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12398698118614142243560253 4649511794480303341335095)
                ·
                  refine ⟨6974267691720455012002643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4649511794480303341335095 6974267691720455012002643)
                  ·
                    refine ⟨10461401537580682518003965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6974267691720455012002643 10461401537580682518003965)
                    ·
                      refine ⟨3923025576592755944251487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10461401537580682518003965 3923025576592755944251487)
                      ·
                        rfl

theorem cell23_7640065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_7640065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640065 prefixEnd_7640065 := by exact prefixLift 7640065
  have htrace : WordTrace (prefixWord ++ tailWord_7640065) baseStart_7640065 baseEnd_7640065 := by
    simpa [prefixWord, tailWord_7640065, baseEnd_7640065] using wordTrace_append hprefix tailTrace_7640065
  have hstable : (prefixWord ++ tailWord_7640065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640065).length < 2 ^ (prefixWord ++ tailWord_7640065).sum := by decide
  have hdescent : baseEnd_7640065 < baseStart_7640065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640071 : List Nat := [1, 1, 4, 3, 1, 1, 1, 5, 1, 1, 4]
def baseStart_7640071 : Nat := 118140960795 + 7640071 * 2 ^ 59
def prefixEnd_7640071 : Nat := 4983230072969 + 3 ^ 40 * 7640071 * 2
def baseEnd_7640071 : Nat := 3923028657476682920776459

theorem tailTrace_7640071 : CollatzResearch.WordTrace tailWord_7640071 prefixEnd_7640071 3923028657476682920776459 := by
  unfold tailWord_7640071
  simp only [CollatzResearch.WordTrace]
  refine ⟨278656281904335062089864067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185770854602890041393242711 278656281904335062089864067)
  ·
    refine ⟨417984422856502593134796101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278656281904335062089864067 417984422856502593134796101)
    ·
      refine ⟨78372079285594236212774269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417984422856502593134796101 78372079285594236212774269)
      ·
        refine ⟨29389529732097838579790351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78372079285594236212774269 29389529732097838579790351)
        ·
          refine ⟨44084294598146757869685527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29389529732097838579790351 44084294598146757869685527)
          ·
            refine ⟨66126441897220136804528291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44084294598146757869685527 66126441897220136804528291)
            ·
              refine ⟨99189662845830205206792437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66126441897220136804528291 99189662845830205206792437)
              ·
                refine ⟨9299030891796581738136791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99189662845830205206792437 9299030891796581738136791)
                ·
                  refine ⟨13948546337694872607205187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9299030891796581738136791 13948546337694872607205187)
                  ·
                    refine ⟨20922819506542308910807781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13948546337694872607205187 20922819506542308910807781)
                    ·
                      refine ⟨3923028657476682920776459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20922819506542308910807781 3923028657476682920776459)
                      ·
                        rfl

theorem cell23_7640071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_7640071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640071 prefixEnd_7640071 := by exact prefixLift 7640071
  have htrace : WordTrace (prefixWord ++ tailWord_7640071) baseStart_7640071 baseEnd_7640071 := by
    simpa [prefixWord, tailWord_7640071, baseEnd_7640071] using wordTrace_append hprefix tailTrace_7640071
  have hstable : (prefixWord ++ tailWord_7640071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640071).length < 2 ^ (prefixWord ++ tailWord_7640071).sum := by decide
  have hdescent : baseEnd_7640071 < baseStart_7640071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640098 : List Nat := [3, 3, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_7640098 : Nat := 118140960795 + 7640098 * 2 ^ 59
def prefixEnd_7640098 : Nat := 4983230072969 + 3 ^ 40 * 7640098 * 2
def baseEnd_7640098 : Nat := 1307680840484784771712945

theorem tailTrace_7640098 : CollatzResearch.WordTrace tailWord_7640098 prefixEnd_7640098 1307680840484784771712945 := by
  unfold tailWord_7640098
  simp only [CollatzResearch.WordTrace]
  refine ⟨69664316668809311425274237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185771511116824830467397965 69664316668809311425274237)
  ·
    refine ⟨26124118750803491784477839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69664316668809311425274237 26124118750803491784477839)
    ·
      refine ⟨39186178126205237676716759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26124118750803491784477839 39186178126205237676716759)
      ·
        refine ⟨58779267189307856515075139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39186178126205237676716759 58779267189307856515075139)
        ·
          refine ⟨88168900783961784772612709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58779267189307856515075139 88168900783961784772612709)
          ·
            refine ⟨16531668896992834644864883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88168900783961784772612709 16531668896992834644864883)
            ·
              refine ⟨24797503345489251967297325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16531668896992834644864883 24797503345489251967297325)
              ·
                refine ⟨9299063754558469487736497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24797503345489251967297325 9299063754558469487736497)
                ·
                  refine ⟨6974297815918852115802373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9299063754558469487736497 6974297815918852115802373)
                  ·
                    refine ⟨1307680840484784771712945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6974297815918852115802373 1307680840484784771712945)
                    ·
                      rfl

theorem cell23_7640098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_7640098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640098 prefixEnd_7640098 := by exact prefixLift 7640098
  have htrace : WordTrace (prefixWord ++ tailWord_7640098) baseStart_7640098 baseEnd_7640098 := by
    simpa [prefixWord, tailWord_7640098, baseEnd_7640098] using wordTrace_append hprefix tailTrace_7640098
  have hstable : (prefixWord ++ tailWord_7640098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640098).length < 2 ^ (prefixWord ++ tailWord_7640098).sum := by decide
  have hdescent : baseEnd_7640098 < baseStart_7640098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640118 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_7640118 : Nat := 118140960795 + 7640118 * 2 ^ 59
def prefixEnd_7640118 : Nat := 4983230072969 + 3 ^ 40 * 7640118 * 2
def baseEnd_7640118 : Nat := 3923052791067444236888743

theorem tailTrace_7640118 : CollatzResearch.WordTrace tailWord_7640118 prefixEnd_7640118 3923052791067444236888743 := by
  unfold tailWord_7640118
  simp only [CollatzResearch.WordTrace]
  refine ⟨17416124758447799319801563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185771997423443192744550005 17416124758447799319801563)
  ·
    refine ⟨26124187137671698979702345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17416124758447799319801563 26124187137671698979702345)
    ·
      refine ⟨19593140353253774234776759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26124187137671698979702345 19593140353253774234776759)
      ·
        refine ⟨29389710529880661352165139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19593140353253774234776759 29389710529880661352165139)
        ·
          refine ⟨44084565794820992028247709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29389710529880661352165139 44084565794820992028247709)
          ·
            refine ⟨16531712173057872010592891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44084565794820992028247709 16531712173057872010592891)
            ·
              refine ⟨24797568259586808015889337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16531712173057872010592891 24797568259586808015889337)
              ·
                refine ⟨18598176194690106011917003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24797568259586808015889337 18598176194690106011917003)
                ·
                  refine ⟨27897264292035159017875505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18598176194690106011917003 27897264292035159017875505)
                  ·
                    refine ⟨20922948219026369263406629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27897264292035159017875505 20922948219026369263406629)
                    ·
                      refine ⟨3923052791067444236888743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20922948219026369263406629 3923052791067444236888743)
                      ·
                        rfl

theorem cell23_7640118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_7640118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640118 prefixEnd_7640118 := by exact prefixLift 7640118
  have htrace : WordTrace (prefixWord ++ tailWord_7640118) baseStart_7640118 baseEnd_7640118 := by
    simpa [prefixWord, tailWord_7640118, baseEnd_7640118] using wordTrace_append hprefix tailTrace_7640118
  have hstable : (prefixWord ++ tailWord_7640118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640118).length < 2 ^ (prefixWord ++ tailWord_7640118).sum := by decide
  have hdescent : baseEnd_7640118 < baseStart_7640118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640121 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 3, 3, 3]
def baseStart_7640121 : Nat := 118140960795 + 7640121 * 2 ^ 59
def prefixEnd_7640121 : Nat := 4983230072969 + 3 ^ 40 * 7640121 * 2
def baseEnd_7640121 : Nat := 3923054331509407725151229

theorem tailTrace_7640121 : CollatzResearch.WordTrace tailWord_7640121 prefixEnd_7640121 3923054331509407725151229 := by
  unfold tailWord_7640121
  simp only [CollatzResearch.WordTrace]
  refine ⟨278658105554153920629184217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185772070369435947086122811 278658105554153920629184217)
  ·
    refine ⟨208993579165615440471888163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278658105554153920629184217 208993579165615440471888163)
    ·
      refine ⟨313490368748423160707832245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208993579165615440471888163 313490368748423160707832245)
      ·
        refine ⟨29389722070164671316359273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 313490368748423160707832245 29389722070164671316359273)
        ·
          refine ⟨22042291552623503487269455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29389722070164671316359273 22042291552623503487269455)
          ·
            refine ⟨33063437328935255230904183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22042291552623503487269455 33063437328935255230904183)
            ·
              refine ⟨49595155993402882846356275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33063437328935255230904183 49595155993402882846356275)
              ·
                refine ⟨74392733990104324269534413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49595155993402882846356275 74392733990104324269534413)
                ·
                  refine ⟨27897275246289121601075405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74392733990104324269534413 27897275246289121601075405)
                  ·
                    refine ⟨10461478217358420600403277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27897275246289121601075405 10461478217358420600403277)
                    ·
                      refine ⟨3923054331509407725151229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10461478217358420600403277 3923054331509407725151229)
                      ·
                        rfl

theorem cell23_7640121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_7640121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640121 prefixEnd_7640121 := by exact prefixLift 7640121
  have htrace : WordTrace (prefixWord ++ tailWord_7640121) baseStart_7640121 baseEnd_7640121 := by
    simpa [prefixWord, tailWord_7640121, baseEnd_7640121] using wordTrace_append hprefix tailTrace_7640121
  have hstable : (prefixWord ++ tailWord_7640121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640121).length < 2 ^ (prefixWord ++ tailWord_7640121).sum := by decide
  have hdescent : baseEnd_7640121 < baseStart_7640121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640125 : List Nat := [1, 4, 1, 3, 1, 3, 3, 1, 1, 2, 3]
def baseStart_7640125 : Nat := 118140960795 + 7640125 * 2 ^ 59
def prefixEnd_7640125 : Nat := 4983230072969 + 3 ^ 40 * 7640125 * 2
def baseEnd_7640125 : Nat := 3923056385432025709501211

theorem tailTrace_7640125 : CollatzResearch.WordTrace tailWord_7640125 prefixEnd_7640125 3923056385432025709501211 := by
  unfold tailWord_7640125
  simp only [CollatzResearch.WordTrace]
  refine ⟨278658251446139429312329829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185772167630759619541553219 278658251446139429312329829)
  ·
    refine ⟨52248422146151142996061843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278658251446139429312329829 52248422146151142996061843)
    ·
      refine ⟨78372633219226714494092765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52248422146151142996061843 78372633219226714494092765)
      ·
        refine ⟨29389737457210017935284787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78372633219226714494092765 29389737457210017935284787)
        ·
          refine ⟨44084606185815026902927181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29389737457210017935284787 44084606185815026902927181)
          ·
            refine ⟨16531727319680635088597693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44084606185815026902927181 16531727319680635088597693)
            ·
              refine ⟨6199397744880238158224135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16531727319680635088597693 6199397744880238158224135)
              ·
                refine ⟨9299096617320357237336203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6199397744880238158224135 9299096617320357237336203)
                ·
                  refine ⟨13948644925980535856004305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9299096617320357237336203 13948644925980535856004305)
                  ·
                    refine ⟨10461483694485401892003229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13948644925980535856004305 10461483694485401892003229)
                    ·
                      refine ⟨3923056385432025709501211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10461483694485401892003229 3923056385432025709501211)
                      ·
                        rfl

theorem cell23_7640125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_7640125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640125 prefixEnd_7640125 := by exact prefixLift 7640125
  have htrace : WordTrace (prefixWord ++ tailWord_7640125) baseStart_7640125 baseEnd_7640125 := by
    simpa [prefixWord, tailWord_7640125, baseEnd_7640125] using wordTrace_append hprefix tailTrace_7640125
  have hstable : (prefixWord ++ tailWord_7640125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640125).length < 2 ^ (prefixWord ++ tailWord_7640125).sum := by decide
  have hdescent : baseEnd_7640125 < baseStart_7640125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640138 : List Nat := [3, 1, 2, 1, 1, 2, 3, 4, 2, 1, 3]
def baseStart_7640138 : Nat := 118140960795 + 7640138 * 2 ^ 59
def prefixEnd_7640138 : Nat := 4983230072969 + 3 ^ 40 * 7640138 * 2
def baseEnd_7640138 : Nat := 3923063060680534158638651

theorem tailTrace_7640138 : CollatzResearch.WordTrace tailWord_7640138 prefixEnd_7640138 3923063060680534158638651 := by
  unfold tailWord_7640138
  simp only [CollatzResearch.WordTrace]
  refine ⟨69664681398773083133138267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185772483730061555021702045 69664681398773083133138267)
  ·
    refine ⟨104497022098159624699707401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69664681398773083133138267 104497022098159624699707401)
    ·
      refine ⟨78372766573619718524780551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104497022098159624699707401 78372766573619718524780551)
      ·
        refine ⟨117559149860429577787170827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78372766573619718524780551 117559149860429577787170827)
        ·
          refine ⟨176338724790644366680756241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117559149860429577787170827 176338724790644366680756241)
          ·
            refine ⟨132254043592983275010567181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176338724790644366680756241 132254043592983275010567181)
            ·
              refine ⟨49595266347368728128962693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132254043592983275010567181 49595266347368728128962693)
              ·
                refine ⟨9299112440131636524180505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49595266347368728128962693 9299112440131636524180505)
                ·
                  refine ⟨6974334330098727393135379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9299112440131636524180505 6974334330098727393135379)
                  ·
                    refine ⟨10461501495148091089703069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6974334330098727393135379 10461501495148091089703069)
                    ·
                      refine ⟨3923063060680534158638651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10461501495148091089703069 3923063060680534158638651)
                      ·
                        rfl

theorem cell23_7640138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_7640138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640138 prefixEnd_7640138 := by exact prefixLift 7640138
  have htrace : WordTrace (prefixWord ++ tailWord_7640138) baseStart_7640138 baseEnd_7640138 := by
    simpa [prefixWord, tailWord_7640138, baseEnd_7640138] using wordTrace_append hprefix tailTrace_7640138
  have hstable : (prefixWord ++ tailWord_7640138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640138).length < 2 ^ (prefixWord ++ tailWord_7640138).sum := by decide
  have hdescent : baseEnd_7640138 < baseStart_7640138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640141 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_7640141 : Nat := 118140960795 + 7640141 * 2 ^ 59
def prefixEnd_7640141 : Nat := 4983230072969 + 3 ^ 40 * 7640141 * 2
def baseEnd_7640141 : Nat := 1307688200374165882300379

theorem tailTrace_7640141 : CollatzResearch.WordTrace tailWord_7640141 prefixEnd_7640141 1307688200374165882300379 := by
  unfold tailWord_7640141
  simp only [CollatzResearch.WordTrace]
  refine ⟨278658835014081464044912277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185772556676054309363274851 278658835014081464044912277)
  ·
    refine ⟨13062132891285068627105263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 278658835014081464044912277 13062132891285068627105263)
    ·
      refine ⟨19593199336927602940657895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13062132891285068627105263 19593199336927602940657895)
      ·
        refine ⟨29389799005391404410986843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19593199336927602940657895 29389799005391404410986843)
        ·
          refine ⟨44084698508087106616480265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29389799005391404410986843 44084698508087106616480265)
          ·
            refine ⟨33063523881065329962360199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44084698508087106616480265 33063523881065329962360199)
            ·
              refine ⟨49595285821597994943540299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33063523881065329962360199 49595285821597994943540299)
              ·
                refine ⟨74392928732396992415310449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49595285821597994943540299 74392928732396992415310449)
                ·
                  refine ⟨55794696549297744311482837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74392928732396992415310449 55794696549297744311482837)
                  ·
                    refine ⟨1307688200374165882300379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55794696549297744311482837 1307688200374165882300379)
                    ·
                      rfl

theorem cell23_7640141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_7640141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640141 prefixEnd_7640141 := by exact prefixLift 7640141
  have htrace : WordTrace (prefixWord ++ tailWord_7640141) baseStart_7640141 baseEnd_7640141 := by
    simpa [prefixWord, tailWord_7640141, baseEnd_7640141] using wordTrace_append hprefix tailTrace_7640141
  have hstable : (prefixWord ++ tailWord_7640141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640141).length < 2 ^ (prefixWord ++ tailWord_7640141).sum := by decide
  have hdescent : baseEnd_7640141 < baseStart_7640141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640148 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 3, 3, 2]
def baseStart_7640148 : Nat := 118140960795 + 7640148 * 2 ^ 59
def prefixEnd_7640148 : Nat := 4983230072969 + 3 ^ 40 * 7640148 * 2
def baseEnd_7640148 : Nat := 3923068195487079119513605

theorem tailTrace_7640148 : CollatzResearch.WordTrace tailWord_7640148 prefixEnd_7640148 3923068195487079119513605 := by
  unfold tailWord_7640148
  simp only [CollatzResearch.WordTrace]
  refine ⟨139329545162528052120208549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185772726883370736160278065 139329545162528052120208549)
  ·
    refine ⟨26124289717974009772539103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139329545162528052120208549 26124289717974009772539103)
    ·
      refine ⟨39186434576961014658808655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26124289717974009772539103 39186434576961014658808655)
      ·
        refine ⟨58779651865441521988212983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39186434576961014658808655 58779651865441521988212983)
        ·
          refine ⟨88169477798162282982319475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58779651865441521988212983 88169477798162282982319475)
          ·
            refine ⟨132254216697243424473479213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88169477798162282982319475 132254216697243424473479213)
            ·
              refine ⟨49595331261466284177554705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132254216697243424473479213 49595331261466284177554705)
              ·
                refine ⟨37196498446099713133166029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49595331261466284177554705 37196498446099713133166029)
                ·
                  refine ⟨13948686917287392424937261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37196498446099713133166029 13948686917287392424937261)
                  ·
                    refine ⟨5230757593982772159351473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13948686917287392424937261 5230757593982772159351473)
                    ·
                      refine ⟨3923068195487079119513605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5230757593982772159351473 3923068195487079119513605)
                      ·
                        rfl

theorem cell23_7640148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_7640148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640148 prefixEnd_7640148 := by exact prefixLift 7640148
  have htrace : WordTrace (prefixWord ++ tailWord_7640148) baseStart_7640148 baseEnd_7640148 := by
    simpa [prefixWord, tailWord_7640148, baseEnd_7640148] using wordTrace_append hprefix tailTrace_7640148
  have hstable : (prefixWord ++ tailWord_7640148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640148).length < 2 ^ (prefixWord ++ tailWord_7640148).sum := by decide
  have hdescent : baseEnd_7640148 < baseStart_7640148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640178 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 1, 4, 2]
def baseStart_7640178 : Nat := 118140960795 + 7640178 * 2 ^ 59
def prefixEnd_7640178 : Nat := 4983230072969 + 3 ^ 40 * 7640178 * 2
def baseEnd_7640178 : Nat := 3923083599906714002138467

theorem tailTrace_7640178 : CollatzResearch.WordTrace tailWord_7640178 prefixEnd_7640178 3923083599906714002138467 := by
  unfold tailWord_7640178
  simp only [CollatzResearch.WordTrace]
  refine ⟨69665046128736854841002297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185773456343298279576006125 69665046128736854841002297)
  ·
    refine ⟨52248784596552641130751723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69665046128736854841002297 52248784596552641130751723)
    ·
      refine ⟨78373176894828961696127585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52248784596552641130751723 78373176894828961696127585)
      ·
        refine ⟨58779882671121721272095689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78373176894828961696127585 58779882671121721272095689)
        ·
          refine ⟨44084912003341290954071767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58779882671121721272095689 44084912003341290954071767)
          ·
            refine ⟨66127368005011936431107651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44084912003341290954071767 66127368005011936431107651)
            ·
              refine ⟨99191052007517904646661477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66127368005011936431107651 99191052007517904646661477)
              ·
                refine ⟨18598322251409607121249027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99191052007517904646661477 18598322251409607121249027)
                ·
                  refine ⟨27897483377114410681873541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18598322251409607121249027 27897483377114410681873541)
                  ·
                    refine ⟨5230778133208952002851289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27897483377114410681873541 5230778133208952002851289)
                    ·
                      refine ⟨3923083599906714002138467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5230778133208952002851289 3923083599906714002138467)
                      ·
                        rfl

theorem cell23_7640178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_7640178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640178 prefixEnd_7640178 := by exact prefixLift 7640178
  have htrace : WordTrace (prefixWord ++ tailWord_7640178) baseStart_7640178 baseEnd_7640178 := by
    simpa [prefixWord, tailWord_7640178, baseEnd_7640178] using wordTrace_append hprefix tailTrace_7640178
  have hstable : (prefixWord ++ tailWord_7640178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640178).length < 2 ^ (prefixWord ++ tailWord_7640178).sum := by decide
  have hdescent : baseEnd_7640178 < baseStart_7640178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640201 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 7]
def baseStart_7640201 : Nat := 118140960795 + 7640201 * 2 ^ 59
def prefixEnd_7640201 : Nat := 4983230072969 + 3 ^ 40 * 7640201 * 2
def baseEnd_7640201 : Nat := 435899489995751934683429

theorem tailTrace_7640201 : CollatzResearch.WordTrace tailWord_7640201 prefixEnd_7640201 435899489995751934683429 := by
  unfold tailWord_7640201
  simp only [CollatzResearch.WordTrace]
  refine ⟨278661023393864094292096457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185774015595909396194730971 278661023393864094292096457)
  ·
    refine ⟨208995767545398070719072343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278661023393864094292096457 208995767545398070719072343)
    ·
      refine ⟨313493651318097106078608515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208995767545398070719072343 313493651318097106078608515)
      ·
        refine ⟨470240476977145659117912773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313493651318097106078608515 470240476977145659117912773)
        ·
          refine ⟨88170089433214811084608645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 470240476977145659117912773 88170089433214811084608645)
          ·
            refine ⟨16531891768727777078364121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88170089433214811084608645 16531891768727777078364121)
            ·
              refine ⟨12398918826545832808773091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16531891768727777078364121 12398918826545832808773091)
              ·
                refine ⟨18598378239818749213159637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12398918826545832808773091 18598378239818749213159637)
                ·
                  refine ⟨435899489995751934683429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18598378239818749213159637 435899489995751934683429)
                  ·
                    rfl

theorem cell23_7640201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 7].length) (baseStart_7640201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640201 prefixEnd_7640201 := by exact prefixLift 7640201
  have htrace : WordTrace (prefixWord ++ tailWord_7640201) baseStart_7640201 baseEnd_7640201 := by
    simpa [prefixWord, tailWord_7640201, baseEnd_7640201] using wordTrace_append hprefix tailTrace_7640201
  have hstable : (prefixWord ++ tailWord_7640201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640201).length < 2 ^ (prefixWord ++ tailWord_7640201).sum := by decide
  have hdescent : baseEnd_7640201 < baseStart_7640201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640211 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 3]
def baseStart_7640211 : Nat := 118140960795 + 7640211 * 2 ^ 59
def prefixEnd_7640211 : Nat := 4983230072969 + 3 ^ 40 * 7640211 * 2
def baseEnd_7640211 : Nat := 3923100544768312373025815

theorem tailTrace_7640211 : CollatzResearch.WordTrace tailWord_7640211 prefixEnd_7640211 3923100544768312373025815 := by
  unfold tailWord_7640211
  simp only [CollatzResearch.WordTrace]
  refine ⟨278661388123827865999960487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185774258749218577333306991 278661388123827865999960487)
  ·
    refine ⟨417992082185741798999940731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278661388123827865999960487 417992082185741798999940731)
    ·
      refine ⟨626988123278612698499911097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417992082185741798999940731 626988123278612698499911097)
      ·
        refine ⟨470241092458959523874933323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626988123278612698499911097 470241092458959523874933323)
        ·
          refine ⟨705361638688439285812399985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470241092458959523874933323 705361638688439285812399985)
          ·
            refine ⟨529021229016329464359299989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705361638688439285812399985 529021229016329464359299989)
            ·
              refine ⟨24797870110140443641842187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 529021229016329464359299989 24797870110140443641842187)
              ·
                refine ⟨37196805165210665462763281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24797870110140443641842187 37196805165210665462763281)
                ·
                  refine ⟨27897603873907999097072461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37196805165210665462763281 27897603873907999097072461)
                  ·
                    refine ⟨10461601452715499661402173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27897603873907999097072461 10461601452715499661402173)
                    ·
                      refine ⟨3923100544768312373025815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10461601452715499661402173 3923100544768312373025815)
                      ·
                        rfl

theorem cell23_7640211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 3].length) (baseStart_7640211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640211 prefixEnd_7640211 := by exact prefixLift 7640211
  have htrace : WordTrace (prefixWord ++ tailWord_7640211) baseStart_7640211 baseEnd_7640211 := by
    simpa [prefixWord, tailWord_7640211, baseEnd_7640211] using wordTrace_append hprefix tailTrace_7640211
  have hstable : (prefixWord ++ tailWord_7640211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640211).length < 2 ^ (prefixWord ++ tailWord_7640211).sum := by decide
  have hdescent : baseEnd_7640211 < baseStart_7640211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640271 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 3]
def baseStart_7640271 : Nat := 118140960795 + 7640271 * 2 ^ 59
def prefixEnd_7640271 : Nat := 4983230072969 + 3 ^ 40 * 7640271 * 2
def baseEnd_7640271 : Nat := 3923131353607582138275539

theorem tailTrace_7640271 : CollatzResearch.WordTrace tailWord_7640271 prefixEnd_7640271 3923131353607582138275539 := by
  unfold tailWord_7640271
  simp only [CollatzResearch.WordTrace]
  refine ⟨278663576503610496247144667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185775717669073664164763111 278663576503610496247144667)
  ·
    refine ⟨417995364755415744370717001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278663576503610496247144667 417995364755415744370717001)
    ·
      refine ⟨313496523566561808278037751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417995364755415744370717001 313496523566561808278037751)
      ·
        refine ⟨470244785349842712417056627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313496523566561808278037751 470244785349842712417056627)
        ·
          refine ⟨705367178024764068625584941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470244785349842712417056627 705367178024764068625584941)
          ·
            refine ⟨264512691759286525734594353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 705367178024764068625584941 264512691759286525734594353)
            ·
              refine ⟨198384518819464894300945765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264512691759286525734594353 198384518819464894300945765)
              ·
                refine ⟨37197097278649667681427331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198384518819464894300945765 37197097278649667681427331)
                ·
                  refine ⟨55795645917974501522140997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37197097278649667681427331 55795645917974501522140997)
                  ·
                    refine ⟨10461683609620219035401437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55795645917974501522140997 10461683609620219035401437)
                    ·
                      refine ⟨3923131353607582138275539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10461683609620219035401437 3923131353607582138275539)
                      ·
                        rfl

theorem cell23_7640271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 3].length) (baseStart_7640271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640271 prefixEnd_7640271 := by exact prefixLift 7640271
  have htrace : WordTrace (prefixWord ++ tailWord_7640271) baseStart_7640271 baseEnd_7640271 := by
    simpa [prefixWord, tailWord_7640271, baseEnd_7640271] using wordTrace_append hprefix tailTrace_7640271
  have hstable : (prefixWord ++ tailWord_7640271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640271).length < 2 ^ (prefixWord ++ tailWord_7640271).sum := by decide
  have hdescent : baseEnd_7640271 < baseStart_7640271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640288 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 3]
def baseStart_7640288 : Nat := 118140960795 + 7640288 * 2 ^ 59
def prefixEnd_7640288 : Nat := 4983230072969 + 3 ^ 40 * 7640288 * 2
def baseEnd_7640288 : Nat := 3923140082778708571762961

theorem tailTrace_7640288 : CollatzResearch.WordTrace tailWord_7640288 prefixEnd_7640288 3923140082778708571762961 := by
  unfold tailWord_7640288
  simp only [CollatzResearch.WordTrace]
  refine ⟨139332098272274454075256759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185776131029699272100342345 139332098272274454075256759)
  ·
    refine ⟨208998147408411681112885139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139332098272274454075256759 208998147408411681112885139)
    ·
      refine ⟨313497221112617521669327709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208998147408411681112885139 313497221112617521669327709)
      ·
        refine ⟨117561457917231570625997891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313497221112617521669327709 117561457917231570625997891)
        ·
          refine ⟨176342186875847355938996837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117561457917231570625997891 176342186875847355938996837)
          ·
            refine ⟨33064160039221379238561907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176342186875847355938996837 33064160039221379238561907)
            ·
              refine ⟨49596240058832068857842861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33064160039221379238561907 49596240058832068857842861)
              ·
                refine ⟨18598590022062025821691073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49596240058832068857842861 18598590022062025821691073)
                ·
                  refine ⟨13948942516546519366268305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18598590022062025821691073 13948942516546519366268305)
                  ·
                    refine ⟨10461706887409889524701229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13948942516546519366268305 10461706887409889524701229)
                    ·
                      refine ⟨3923140082778708571762961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10461706887409889524701229 3923140082778708571762961)
                      ·
                        rfl

theorem cell23_7640288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_7640288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640288 prefixEnd_7640288 := by exact prefixLift 7640288
  have htrace : WordTrace (prefixWord ++ tailWord_7640288) baseStart_7640288 baseEnd_7640288 := by
    simpa [prefixWord, tailWord_7640288, baseEnd_7640288] using wordTrace_append hprefix tailTrace_7640288
  have hstable : (prefixWord ++ tailWord_7640288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640288).length < 2 ^ (prefixWord ++ tailWord_7640288).sum := by decide
  have hdescent : baseEnd_7640288 < baseStart_7640288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640355 : List Nat := [1, 1, 1, 4, 2, 3, 4, 1, 1, 5]
def baseStart_7640355 : Nat := 118140960795 + 7640355 * 2 ^ 59
def prefixEnd_7640355 : Nat := 4983230072969 + 3 ^ 40 * 7640355 * 2
def baseEnd_7640355 : Nat := 1307724828660853269875051

theorem tailTrace_7640355 : CollatzResearch.WordTrace tailWord_7640355 prefixEnd_7640355 1307724828660853269875051 := by
  unfold tailWord_7640355
  simp only [CollatzResearch.WordTrace]
  refine ⟨278666640235306178593202519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185777760156870785728801679 278666640235306178593202519)
  ·
    refine ⟨417999960352959267889803779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278666640235306178593202519 417999960352959267889803779)
    ·
      refine ⟨626999940529438901834705669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417999960352959267889803779 626999940529438901834705669)
      ·
        refine ⟨117562488849269794094007313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 626999940529438901834705669 117562488849269794094007313)
        ·
          refine ⟨88171866636952345570505485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117562488849269794094007313 88171866636952345570505485)
          ·
            refine ⟨33064449988857129588939557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88171866636952345570505485 33064449988857129588939557)
            ·
              refine ⟨6199584372910711797926167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33064449988857129588939557 6199584372910711797926167)
              ·
                refine ⟨9299376559366067696889251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6199584372910711797926167 9299376559366067696889251)
                ·
                  refine ⟨13949064839049101545333877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9299376559366067696889251 13949064839049101545333877)
                  ·
                    refine ⟨1307724828660853269875051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13949064839049101545333877 1307724828660853269875051)
                    ·
                      rfl

theorem cell23_7640355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 1, 5].length) (baseStart_7640355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640355 prefixEnd_7640355 := by exact prefixLift 7640355
  have htrace : WordTrace (prefixWord ++ tailWord_7640355) baseStart_7640355 baseEnd_7640355 := by
    simpa [prefixWord, tailWord_7640355, baseEnd_7640355] using wordTrace_append hprefix tailTrace_7640355
  have hstable : (prefixWord ++ tailWord_7640355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640355).length < 2 ^ (prefixWord ++ tailWord_7640355).sum := by decide
  have hdescent : baseEnd_7640355 < baseStart_7640355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640368 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 4, 4]
def baseStart_7640368 : Nat := 118140960795 + 7640368 * 2 ^ 59
def prefixEnd_7640368 : Nat := 4983230072969 + 3 ^ 40 * 7640368 * 2
def baseEnd_7640368 : Nat := 1307727053743689419587531

theorem tailTrace_7640368 : CollatzResearch.WordTrace tailWord_7640368 prefixEnd_7640368 1307727053743689419587531 := by
  unfold tailWord_7640368
  simp only [CollatzResearch.WordTrace]
  refine ⟨139333557192129540906712879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185778076256172721208950505 139333557192129540906712879)
  ·
    refine ⟨209000335788194311360069319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139333557192129540906712879 209000335788194311360069319)
    ·
      refine ⟨313500503682291467040103979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209000335788194311360069319 313500503682291467040103979)
      ·
        refine ⟨470250755523437200560155969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313500503682291467040103979 470250755523437200560155969)
        ·
          refine ⟨352688066642577900420116977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470250755523437200560155969 352688066642577900420116977)
          ·
            refine ⟨264516049981933425315087733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352688066642577900420116977 264516049981933425315087733)
            ·
              refine ⟨24798379685806258623289475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264516049981933425315087733 24798379685806258623289475)
              ·
                refine ⟨37197569528709387934934213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24798379685806258623289475 37197569528709387934934213)
                ·
                  refine ⟨6974544286633010237800165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37197569528709387934934213 6974544286633010237800165)
                  ·
                    refine ⟨1307727053743689419587531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6974544286633010237800165 1307727053743689419587531)
                    ·
                      rfl

theorem cell23_7640368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 4, 4].length) (baseStart_7640368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640368 prefixEnd_7640368 := by exact prefixLift 7640368
  have htrace : WordTrace (prefixWord ++ tailWord_7640368) baseStart_7640368 baseEnd_7640368 := by
    simpa [prefixWord, tailWord_7640368, baseEnd_7640368] using wordTrace_append hprefix tailTrace_7640368
  have hstable : (prefixWord ++ tailWord_7640368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640368).length < 2 ^ (prefixWord ++ tailWord_7640368).sum := by decide
  have hdescent : baseEnd_7640368 < baseStart_7640368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640378 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5]
def baseStart_7640378 : Nat := 118140960795 + 7640378 * 2 ^ 59
def prefixEnd_7640378 : Nat := 4983230072969 + 3 ^ 40 * 7640378 * 2
def baseEnd_7640378 : Nat := 3923186296037613219637547

theorem tailTrace_7640378 : CollatzResearch.WordTrace tailWord_7640378 prefixEnd_7640378 3923186296037613219637547 := by
  unfold tailWord_7640378
  simp only [CollatzResearch.WordTrace]
  refine ⟨69666869778555713380322447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185778319409481902347526525 69666869778555713380322447)
  ·
    refine ⟨104500304667833570070483671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69666869778555713380322447 104500304667833570070483671)
    ·
      refine ⟨156750457001750355105725507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104500304667833570070483671 156750457001750355105725507)
      ·
        refine ⟨235125685502625532658588261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156750457001750355105725507 235125685502625532658588261)
        ·
          refine ⟨44086066031742287373485299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235125685502625532658588261 44086066031742287373485299)
          ·
            refine ⟨66129099047613431060227949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44086066031742287373485299 66129099047613431060227949)
            ·
              refine ⟨24798412142855036647585481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66129099047613431060227949 24798412142855036647585481)
              ·
                refine ⟨18598809107141277485689111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24798412142855036647585481 18598809107141277485689111)
                ·
                  refine ⟨27898213660711916228533667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18598809107141277485689111 27898213660711916228533667)
                  ·
                    refine ⟨41847320491067874342800501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27898213660711916228533667 41847320491067874342800501)
                    ·
                      refine ⟨3923186296037613219637547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41847320491067874342800501 3923186296037613219637547)
                      ·
                        rfl

theorem cell23_7640378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_7640378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640378 prefixEnd_7640378 := by exact prefixLift 7640378
  have htrace : WordTrace (prefixWord ++ tailWord_7640378) baseStart_7640378 baseEnd_7640378 := by
    simpa [prefixWord, tailWord_7640378, baseEnd_7640378] using wordTrace_append hprefix tailTrace_7640378
  have hstable : (prefixWord ++ tailWord_7640378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640378).length < 2 ^ (prefixWord ++ tailWord_7640378).sum := by decide
  have hdescent : baseEnd_7640378 < baseStart_7640378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640385 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 1, 6]
def baseStart_7640385 : Nat := 118140960795 + 7640385 * 2 ^ 59
def prefixEnd_7640385 : Nat := 4983230072969 + 3 ^ 40 * 7640385 * 2
def baseEnd_7640385 : Nat := 1307729963467398230750005

theorem tailTrace_7640385 : CollatzResearch.WordTrace tailWord_7640385 prefixEnd_7640385 1307729963467398230750005 := by
  unfold tailWord_7640385
  simp only [CollatzResearch.WordTrace]
  refine ⟨278667734425197493716794609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185778489616798329144529739 278667734425197493716794609)
  ·
    refine ⟨209000800818898120287595957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278667734425197493716794609 209000800818898120287595957)
    ·
      refine ⟨19593825076771698776962121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209000800818898120287595957 19593825076771698776962121)
      ·
        refine ⟨14695368807578774082721591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19593825076771698776962121 14695368807578774082721591)
        ·
          refine ⟨22043053211368161124082387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14695368807578774082721591 22043053211368161124082387)
          ·
            refine ⟨33064579817052241686123581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22043053211368161124082387 33064579817052241686123581)
            ·
              refine ⟨12399217431394590632296343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33064579817052241686123581 12399217431394590632296343)
              ·
                refine ⟨18598826147091885948444515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12399217431394590632296343 18598826147091885948444515)
                ·
                  refine ⟨27898239220637828922666773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18598826147091885948444515 27898239220637828922666773)
                  ·
                    refine ⟨1307729963467398230750005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27898239220637828922666773 1307729963467398230750005)
                    ·
                      rfl

theorem cell23_7640385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_7640385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640385 prefixEnd_7640385 := by exact prefixLift 7640385
  have htrace : WordTrace (prefixWord ++ tailWord_7640385) baseStart_7640385 baseEnd_7640385 := by
    simpa [prefixWord, tailWord_7640385, baseEnd_7640385] using wordTrace_append hprefix tailTrace_7640385
  have hstable : (prefixWord ++ tailWord_7640385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640385).length < 2 ^ (prefixWord ++ tailWord_7640385).sum := by decide
  have hdescent : baseEnd_7640385 < baseStart_7640385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640408 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 3, 3, 3]
def baseStart_7640408 : Nat := 118140960795 + 7640408 * 2 ^ 59
def prefixEnd_7640408 : Nat := 4983230072969 + 3 ^ 40 * 7640408 * 2
def baseEnd_7640408 : Nat := 3923201700457248102262409

theorem tailTrace_7640408 : CollatzResearch.WordTrace tailWord_7640408 prefixEnd_7640408 3923201700457248102262409 := by
  unfold tailWord_7640408
  simp only [CollatzResearch.WordTrace]
  refine ⟨139334286652057084322440939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185779048869409445763254585 139334286652057084322440939)
  ·
    refine ⟨209001429978085626483661409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139334286652057084322440939 209001429978085626483661409)
    ·
      refine ⟨156751072483564219862746057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209001429978085626483661409 156751072483564219862746057)
      ·
        refine ⟨117563304362673164897059543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156751072483564219862746057 117563304362673164897059543)
        ·
          refine ⟨176344956544009747345589315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117563304362673164897059543 176344956544009747345589315)
          ·
            refine ⟨264517434816014621018383973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176344956544009747345589315 264517434816014621018383973)
            ·
              refine ⟨49597019028002741440946995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264517434816014621018383973 49597019028002741440946995)
              ·
                refine ⟨74395528542004112161420493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49597019028002741440946995 74395528542004112161420493)
                ·
                  refine ⟨27898323203251542060532685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74395528542004112161420493 27898323203251542060532685)
                  ·
                    refine ⟨10461871201219328272699757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27898323203251542060532685 10461871201219328272699757)
                    ·
                      refine ⟨3923201700457248102262409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10461871201219328272699757 3923201700457248102262409)
                      ·
                        rfl

theorem cell23_7640408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_7640408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640408 prefixEnd_7640408 := by exact prefixLift 7640408
  have htrace : WordTrace (prefixWord ++ tailWord_7640408) baseStart_7640408 baseEnd_7640408 := by
    simpa [prefixWord, tailWord_7640408, baseEnd_7640408] using wordTrace_append hprefix tailTrace_7640408
  have hstable : (prefixWord ++ tailWord_7640408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640408).length < 2 ^ (prefixWord ++ tailWord_7640408).sum := by decide
  have hdescent : baseEnd_7640408 < baseStart_7640408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640409 : List Nat := [1, 2, 1, 2, 2, 2, 5, 3, 1, 2, 2]
def baseStart_7640409 : Nat := 118140960795 + 7640409 * 2 ^ 59
def prefixEnd_7640409 : Nat := 4983230072969 + 3 ^ 40 * 7640409 * 2
def baseEnd_7640409 : Nat := 3923202213937902598349905

theorem tailTrace_7640409 : CollatzResearch.WordTrace tailWord_7640409 prefixEnd_7640409 3923202213937902598349905 := by
  unfold tailWord_7640409
  simp only [CollatzResearch.WordTrace]
  refine ⟨278668609777110545815668281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185779073184740363877112187 278668609777110545815668281)
  ·
    refine ⟨209001457332832909361751211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278668609777110545815668281 209001457332832909361751211)
    ·
      refine ⟨313502185999249364042626817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209001457332832909361751211 313502185999249364042626817)
      ·
        refine ⟨235126639499437023031970113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313502185999249364042626817 235126639499437023031970113)
        ·
          refine ⟨176344979624577767273977585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235126639499437023031970113 176344979624577767273977585)
          ·
            refine ⟨132258734718433325455483189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176344979624577767273977585 132258734718433325455483189)
            ·
              refine ⟨12399256379853124261451549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132258734718433325455483189 12399256379853124261451549)
              ·
                refine ⟨4649721142444921598044331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12399256379853124261451549 4649721142444921598044331)
                ·
                  refine ⟨6974581713667382397066497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4649721142444921598044331 6974581713667382397066497)
                  ·
                    refine ⟨5230936285250536797799873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6974581713667382397066497 5230936285250536797799873)
                    ·
                      refine ⟨3923202213937902598349905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5230936285250536797799873 3923202213937902598349905)
                      ·
                        rfl

theorem cell23_7640409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 1, 2, 2].length) (baseStart_7640409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640409 prefixEnd_7640409 := by exact prefixLift 7640409
  have htrace : WordTrace (prefixWord ++ tailWord_7640409) baseStart_7640409 baseEnd_7640409 := by
    simpa [prefixWord, tailWord_7640409, baseEnd_7640409] using wordTrace_append hprefix tailTrace_7640409
  have hstable : (prefixWord ++ tailWord_7640409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640409).length < 2 ^ (prefixWord ++ tailWord_7640409).sum := by decide
  have hdescent : baseEnd_7640409 < baseStart_7640409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640426 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 3, 2, 2]
def baseStart_7640426 : Nat := 118140960795 + 7640426 * 2 ^ 59
def prefixEnd_7640426 : Nat := 4983230072969 + 3 ^ 40 * 7640426 * 2
def baseEnd_7640426 : Nat := 3923210943109029031837327

theorem tailTrace_7640426 : CollatzResearch.WordTrace tailWord_7640426 prefixEnd_7640426 3923210943109029031837327 := by
  unfold tailWord_7640426
  simp only [CollatzResearch.WordTrace]
  refine ⟨69667307454512239429759283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185779486545365971812691421 69667307454512239429759283)
  ·
    refine ⟨104500961181768359144638925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69667307454512239429759283 104500961181768359144638925)
    ·
      refine ⟨39187860443163134679239597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104500961181768359144638925 39187860443163134679239597)
      ·
        refine ⟨14695447666186175504714849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39187860443163134679239597 14695447666186175504714849)
        ·
          refine ⟨11021585749639631628536137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14695447666186175504714849 11021585749639631628536137)
          ·
            refine ⟨8266189312229723721402103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11021585749639631628536137 8266189312229723721402103)
            ·
              refine ⟨12399283968344585582103155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8266189312229723721402103 12399283968344585582103155)
              ·
                refine ⟨18598925952516878373154733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12399283968344585582103155 18598925952516878373154733)
                ·
                  refine ⟨6974597232193829389933025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18598925952516878373154733 6974597232193829389933025)
                  ·
                    refine ⟨5230947924145372042449769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6974597232193829389933025 5230947924145372042449769)
                    ·
                      refine ⟨3923210943109029031837327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5230947924145372042449769 3923210943109029031837327)
                      ·
                        rfl

theorem cell23_7640426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_7640426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640426 prefixEnd_7640426 := by exact prefixLift 7640426
  have htrace : WordTrace (prefixWord ++ tailWord_7640426) baseStart_7640426 baseEnd_7640426 := by
    simpa [prefixWord, tailWord_7640426, baseEnd_7640426] using wordTrace_append hprefix tailTrace_7640426
  have hstable : (prefixWord ++ tailWord_7640426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640426).length < 2 ^ (prefixWord ++ tailWord_7640426).sum := by decide
  have hdescent : baseEnd_7640426 < baseStart_7640426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640452 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 3, 3, 2]
def baseStart_7640452 : Nat := 118140960795 + 7640452 * 2 ^ 59
def prefixEnd_7640452 : Nat := 4983230072969 + 3 ^ 40 * 7640452 * 2
def baseEnd_7640452 : Nat := 3923224293606045930112207

theorem tailTrace_7640452 : CollatzResearch.WordTrace tailWord_7640452 prefixEnd_7640452 3923224293606045930112207 := by
  unfold tailWord_7640452
  simp only [CollatzResearch.WordTrace]
  refine ⟨139335089057977382079741805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185780118743969842772989073 139335089057977382079741805)
  ·
    refine ⟨52250658396741518279903177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139335089057977382079741805 52250658396741518279903177)
    ·
      refine ⟨39187993797556138709927383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52250658396741518279903177 39187993797556138709927383)
      ·
        refine ⟨58781990696334208064891075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39187993797556138709927383 58781990696334208064891075)
        ·
          refine ⟨88172986044501312097336613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58781990696334208064891075 88172986044501312097336613)
          ·
            refine ⟨16532434883343996018250615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88172986044501312097336613 16532434883343996018250615)
            ·
              refine ⟨24798652325015994027375923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16532434883343996018250615 24798652325015994027375923)
              ·
                refine ⟨37197978487523991041063885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24798652325015994027375923 37197978487523991041063885)
                ·
                  refine ⟨13949241932821496640398957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37197978487523991041063885 13949241932821496640398957)
                  ·
                    refine ⟨5230965724808061240149609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13949241932821496640398957 5230965724808061240149609)
                    ·
                      refine ⟨3923224293606045930112207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5230965724808061240149609 3923224293606045930112207)
                      ·
                        rfl

theorem cell23_7640452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_7640452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640452 prefixEnd_7640452 := by exact prefixLift 7640452
  have htrace : WordTrace (prefixWord ++ tailWord_7640452) baseStart_7640452 baseEnd_7640452 := by
    simpa [prefixWord, tailWord_7640452, baseEnd_7640452] using wordTrace_append hprefix tailTrace_7640452
  have hstable : (prefixWord ++ tailWord_7640452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640452).length < 2 ^ (prefixWord ++ tailWord_7640452).sum := by decide
  have hdescent : baseEnd_7640452 < baseStart_7640452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640465 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 1, 4, 2]
def baseStart_7640465 : Nat := 118140960795 + 7640465 * 2 ^ 59
def prefixEnd_7640465 : Nat := 4983230072969 + 3 ^ 40 * 7640465 * 2
def baseEnd_7640465 : Nat := 3923230968854554379249647

theorem tailTrace_7640465 : CollatzResearch.WordTrace tailWord_7640465 prefixEnd_7640465 3923230968854554379249647 := by
  unfold tailWord_7640465
  simp only [CollatzResearch.WordTrace]
  refine ⟨278670652264907667379706849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185780434843271778253137899 278670652264907667379706849)
  ·
    refine ⟨209002989198680750534780137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278670652264907667379706849 209002989198680750534780137)
    ·
      refine ⟨156752241899010562901085103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209002989198680750534780137 156752241899010562901085103)
      ·
        refine ⟨235128362848515844351627655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156752241899010562901085103 235128362848515844351627655)
        ·
          refine ⟨352692544272773766527441483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235128362848515844351627655 352692544272773766527441483)
          ·
            refine ⟨529038816409160649791162225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352692544272773766527441483 529038816409160649791162225)
            ·
              refine ⟨396779112306870487343371669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529038816409160649791162225 396779112306870487343371669)
              ·
                refine ⟨18599020889384554094220547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 396779112306870487343371669 18599020889384554094220547)
                ·
                  refine ⟨27898531334076831141330821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18599020889384554094220547 27898531334076831141330821)
                  ·
                    refine ⟨5230974625139405838999529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27898531334076831141330821 5230974625139405838999529)
                    ·
                      refine ⟨3923230968854554379249647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5230974625139405838999529 3923230968854554379249647)
                      ·
                        rfl

theorem cell23_7640465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 4, 2].length) (baseStart_7640465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640465 prefixEnd_7640465 := by exact prefixLift 7640465
  have htrace : WordTrace (prefixWord ++ tailWord_7640465) baseStart_7640465 baseEnd_7640465 := by
    simpa [prefixWord, tailWord_7640465, baseEnd_7640465] using wordTrace_append hprefix tailTrace_7640465
  have hstable : (prefixWord ++ tailWord_7640465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640465).length < 2 ^ (prefixWord ++ tailWord_7640465).sum := by decide
  have hdescent : baseEnd_7640465 < baseStart_7640465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640476 : List Nat := [2, 2, 3, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_7640476 : Nat := 118140960795 + 7640476 * 2 ^ 59
def prefixEnd_7640476 : Nat := 4983230072969 + 3 ^ 40 * 7640476 * 2
def baseEnd_7640476 : Nat := 3923236617141753836212097

theorem tailTrace_7640476 : CollatzResearch.WordTrace tailWord_7640476 prefixEnd_7640476 3923236617141753836212097 := by
  unfold tailWord_7640476
  simp only [CollatzResearch.WordTrace]
  refine ⟨139335526733933908129178641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185780702311911877505571521 139335526733933908129178641)
  ·
    refine ⟨104501645050450431096883981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139335526733933908129178641 104501645050450431096883981)
    ·
      refine ⟨39188116893918911661331493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104501645050450431096883981 39188116893918911661331493)
      ·
        refine ⟨7347771917609795936499655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39188116893918911661331493 7347771917609795936499655)
        ·
          refine ⟨11021657876414693904749483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7347771917609795936499655 11021657876414693904749483)
          ·
            refine ⟨16532486814622040857124225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11021657876414693904749483 16532486814622040857124225)
            ·
              refine ⟨12399365110966530642843169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16532486814622040857124225 12399365110966530642843169)
              ·
                refine ⟨9299523833224897982132377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12399365110966530642843169 9299523833224897982132377)
                ·
                  refine ⟨6974642874918673486599283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9299523833224897982132377 6974642874918673486599283)
                  ·
                    refine ⟨10461964312378010229898925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6974642874918673486599283 10461964312378010229898925)
                    ·
                      refine ⟨3923236617141753836212097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10461964312378010229898925 3923236617141753836212097)
                      ·
                        rfl

theorem cell23_7640476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_7640476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640476 prefixEnd_7640476 := by exact prefixLift 7640476
  have htrace : WordTrace (prefixWord ++ tailWord_7640476) baseStart_7640476 baseEnd_7640476 := by
    simpa [prefixWord, tailWord_7640476, baseEnd_7640476] using wordTrace_append hprefix tailTrace_7640476
  have hstable : (prefixWord ++ tailWord_7640476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640476).length < 2 ^ (prefixWord ++ tailWord_7640476).sum := by decide
  have hdescent : baseEnd_7640476 < baseStart_7640476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640505 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 7]
def baseStart_7640505 : Nat := 118140960795 + 7640505 * 2 ^ 59
def prefixEnd_7640505 : Nat := 4983230072969 + 3 ^ 40 * 7640505 * 2
def baseEnd_7640505 : Nat := 435916834231192691416607

theorem tailTrace_7640505 : CollatzResearch.WordTrace tailWord_7640505 prefixEnd_7640505 435916834231192691416607 := by
  unfold tailWord_7640505
  simp only [CollatzResearch.WordTrace]
  refine ⟨278672111184762754211162969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185781407456508502807441979 278672111184762754211162969)
  ·
    refine ⟨209004083388572065658372227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278672111184762754211162969 209004083388572065658372227)
    ·
      refine ⟨313506125082858098487558341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209004083388572065658372227 313506125082858098487558341)
      ·
        refine ⟨58782398453035893466417189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313506125082858098487558341 58782398453035893466417189)
        ·
          refine ⟨11021699709944230024953223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58782398453035893466417189 11021699709944230024953223)
          ·
            refine ⟨16532549564916345037429835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11021699709944230024953223 16532549564916345037429835)
            ·
              refine ⟨24798824347374517556144753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16532549564916345037429835 24798824347374517556144753)
              ·
                refine ⟨18599118260530888167108565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24798824347374517556144753 18599118260530888167108565)
                ·
                  refine ⟨435916834231192691416607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18599118260530888167108565 435916834231192691416607)
                  ·
                    rfl

theorem cell23_7640505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 7].length) (baseStart_7640505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640505 prefixEnd_7640505 := by exact prefixLift 7640505
  have htrace : WordTrace (prefixWord ++ tailWord_7640505) baseStart_7640505 baseEnd_7640505 := by
    simpa [prefixWord, tailWord_7640505, baseEnd_7640505] using wordTrace_append hprefix tailTrace_7640505
  have hstable : (prefixWord ++ tailWord_7640505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640505).length < 2 ^ (prefixWord ++ tailWord_7640505).sum := by decide
  have hdescent : baseEnd_7640505 < baseStart_7640505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640522 : List Nat := [3, 1, 2, 1, 2, 4, 2, 3, 5]
def baseStart_7640522 : Nat := 118140960795 + 7640522 * 2 ^ 59
def prefixEnd_7640522 : Nat := 4983230072969 + 3 ^ 40 * 7640522 * 2
def baseEnd_7640522 : Nat := 435917804139095628470765

theorem tailTrace_7640522 : CollatzResearch.WordTrace tailWord_7640522 prefixEnd_7640522 435917804139095628470765 := by
  unfold tailWord_7640522
  simp only [CollatzResearch.WordTrace]
  refine ⟨69668182806425291528632955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185781820817134110743021213 69668182806425291528632955)
  ·
    refine ⟨104502274209637937292949433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69668182806425291528632955 104502274209637937292949433)
    ·
      refine ⟨78376705657228452969712075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104502274209637937292949433 78376705657228452969712075)
      ·
        refine ⟨117565058485842679454568113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78376705657228452969712075 117565058485842679454568113)
        ·
          refine ⟨88173793864382009590926085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117565058485842679454568113 88173793864382009590926085)
          ·
            refine ⟨16532586349571626798298641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88173793864382009590926085 16532586349571626798298641)
            ·
              refine ⟨12399439762178720098723981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16532586349571626798298641 12399439762178720098723981)
              ·
                refine ⟨4649789910817020037021493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12399439762178720098723981 4649789910817020037021493)
                ·
                  refine ⟨435917804139095628470765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4649789910817020037021493 435917804139095628470765)
                  ·
                    rfl

theorem cell23_7640522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 5].length) (baseStart_7640522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640522 prefixEnd_7640522 := by exact prefixLift 7640522
  have htrace : WordTrace (prefixWord ++ tailWord_7640522) baseStart_7640522 baseEnd_7640522 := by
    simpa [prefixWord, tailWord_7640522, baseEnd_7640522] using wordTrace_append hprefix tailTrace_7640522
  have hstable : (prefixWord ++ tailWord_7640522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640522).length < 2 ^ (prefixWord ++ tailWord_7640522).sum := by decide
  have hdescent : baseEnd_7640522 < baseStart_7640522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640555 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 1, 6, 2]
def baseStart_7640555 : Nat := 118140960795 + 7640555 * 2 ^ 59
def prefixEnd_7640555 : Nat := 4983230072969 + 3 ^ 40 * 7640555 * 2
def baseEnd_7640555 : Nat := 3923277182113459027124233

theorem tailTrace_7640555 : CollatzResearch.WordTrace tailWord_7640555 prefixEnd_7640555 3923277182113459027124233 := by
  unfold tailWord_7640555
  simp only [CollatzResearch.WordTrace]
  refine ⟨278673934834581612750483119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185782623223054408500322079 278673934834581612750483119)
  ·
    refine ⟨418010902251872419125724679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278673934834581612750483119 418010902251872419125724679)
    ·
      refine ⟨627016353377808628688587019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418010902251872419125724679 627016353377808628688587019)
      ·
        refine ⟨940524530066712943032880529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627016353377808628688587019 940524530066712943032880529)
        ·
          refine ⟨705393397550034707274660397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 940524530066712943032880529 705393397550034707274660397)
          ·
            refine ⟨264522524081263015227997649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 705393397550034707274660397 264522524081263015227997649)
            ·
              refine ⟨198391893060947261420998237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264522524081263015227997649 198391893060947261420998237)
              ·
                refine ⟨74396959897855223032874339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198391893060947261420998237 74396959897855223032874339)
                ·
                  refine ⟨111595439846782834549311509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74396959897855223032874339 111595439846782834549311509)
                  ·
                    refine ⟨5231036242817945369498977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111595439846782834549311509 5231036242817945369498977)
                    ·
                      refine ⟨3923277182113459027124233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231036242817945369498977 3923277182113459027124233)
                      ·
                        rfl

theorem cell23_7640555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 6, 2].length) (baseStart_7640555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640555 prefixEnd_7640555 := by exact prefixLift 7640555
  have htrace : WordTrace (prefixWord ++ tailWord_7640555) baseStart_7640555 baseEnd_7640555 := by
    simpa [prefixWord, tailWord_7640555, baseEnd_7640555] using wordTrace_append hprefix tailTrace_7640555
  have hstable : (prefixWord ++ tailWord_7640555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640555).length < 2 ^ (prefixWord ++ tailWord_7640555).sum := by decide
  have hdescent : baseEnd_7640555 < baseStart_7640555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640646 : List Nat := [6, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_7640646 : Nat := 118140960795 + 7640646 * 2 ^ 59
def prefixEnd_7640646 : Nat := 4983230072969 + 3 ^ 40 * 7640646 * 2
def baseEnd_7640646 : Nat := 435924878761446463454035

theorem tailTrace_7640646 : CollatzResearch.WordTrace tailWord_7640646 prefixEnd_7640646 435924878761446463454035 := by
  unfold tailWord_7640646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8708664183664122977876431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185784835918167956861363861 8708664183664122977876431)
  ·
    refine ⟨13062996275496184466814647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8708664183664122977876431 13062996275496184466814647)
    ·
      refine ⟨19594494413244276700221971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13062996275496184466814647 19594494413244276700221971)
      ·
        refine ⟨29391741619866415050332957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19594494413244276700221971 29391741619866415050332957)
        ·
          refine ⟨11021903107449905643874859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29391741619866415050332957 11021903107449905643874859)
          ·
            refine ⟨16532854661174858465812289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11021903107449905643874859 16532854661174858465812289)
            ·
              refine ⟨12399640995881143849359217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16532854661174858465812289 12399640995881143849359217)
              ·
                refine ⟨9299730746910857887019413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12399640995881143849359217 9299730746910857887019413)
                ·
                  refine ⟨435924878761446463454035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9299730746910857887019413 435924878761446463454035)
                  ·
                    rfl

theorem cell23_7640646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_7640646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640646 prefixEnd_7640646 := by exact prefixLift 7640646
  have htrace : WordTrace (prefixWord ++ tailWord_7640646) baseStart_7640646 baseEnd_7640646 := by
    simpa [prefixWord, tailWord_7640646, baseEnd_7640646] using wordTrace_append hprefix tailTrace_7640646
  have hstable : (prefixWord ++ tailWord_7640646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640646).length < 2 ^ (prefixWord ++ tailWord_7640646).sum := by decide
  have hdescent : baseEnd_7640646 < baseStart_7640646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640665 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 1, 1, 5]
def baseStart_7640665 : Nat := 118140960795 + 7640665 * 2 ^ 59
def prefixEnd_7640665 : Nat := 4983230072969 + 3 ^ 40 * 7640665 * 2
def baseEnd_7640665 : Nat := 3923333664985453596748727

theorem tailTrace_7640665 : CollatzResearch.WordTrace tailWord_7640665 prefixEnd_7640665 3923333664985453596748727 := by
  unfold tailWord_7640665
  simp only [CollatzResearch.WordTrace]
  refine ⟨278677946864183101536987449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185785297909455401024658299 278677946864183101536987449)
  ·
    refine ⟨209008460148137326152740587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278677946864183101536987449 209008460148137326152740587)
    ·
      refine ⟨313512690222205989229110881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209008460148137326152740587 313512690222205989229110881)
      ·
        refine ⟨235134517666654491921833161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313512690222205989229110881 235134517666654491921833161)
        ·
          refine ⟨176350888249990868941374871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235134517666654491921833161 176350888249990868941374871)
          ·
            refine ⟨264526332374986303412062307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176350888249990868941374871 264526332374986303412062307)
            ·
              refine ⟨396789498562479455118093461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264526332374986303412062307 396789498562479455118093461)
              ·
                refine ⟨18599507745116224458660631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 396789498562479455118093461 18599507745116224458660631)
                ·
                  refine ⟨27899261617674336687990947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18599507745116224458660631 27899261617674336687990947)
                  ·
                    refine ⟨41848892426511505031986421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27899261617674336687990947 41848892426511505031986421)
                    ·
                      refine ⟨3923333664985453596748727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41848892426511505031986421 3923333664985453596748727)
                      ·
                        rfl

theorem cell23_7640665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_7640665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640665 prefixEnd_7640665 := by exact prefixLift 7640665
  have htrace : WordTrace (prefixWord ++ tailWord_7640665) baseStart_7640665 baseEnd_7640665 := by
    simpa [prefixWord, tailWord_7640665, baseEnd_7640665] using wordTrace_append hprefix tailTrace_7640665
  have hstable : (prefixWord ++ tailWord_7640665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640665).length < 2 ^ (prefixWord ++ tailWord_7640665).sum := by decide
  have hdescent : baseEnd_7640665 < baseStart_7640665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640679 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 5, 2, 2]
def baseStart_7640679 : Nat := 118140960795 + 7640679 * 2 ^ 59
def prefixEnd_7640679 : Nat := 4983230072969 + 3 ^ 40 * 7640679 * 2
def baseEnd_7640679 : Nat := 3923340853714616541973663

theorem tailTrace_7640679 : CollatzResearch.WordTrace tailWord_7640679 prefixEnd_7640679 3923340853714616541973663 := by
  unfold tailWord_7640679
  simp only [CollatzResearch.WordTrace]
  refine ⟨278678457486132381927997091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185785638324088254618664727 278678457486132381927997091)
  ·
    refine ⟨418017686229198572891995637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278678457486132381927997091 418017686229198572891995637)
    ·
      refine ⟨39189158083987366208624591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 418017686229198572891995637 39189158083987366208624591)
      ·
        refine ⟨58783737125981049312936887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39189158083987366208624591 58783737125981049312936887)
        ·
          refine ⟨88175605688971573969405331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58783737125981049312936887 88175605688971573969405331)
          ·
            refine ⟨132263408533457360954107997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88175605688971573969405331 132263408533457360954107997)
            ·
              refine ⟨49598778200046510357790499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132263408533457360954107997 49598778200046510357790499)
              ·
                refine ⟨74398167300069765536685749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49598778200046510357790499 74398167300069765536685749)
                ·
                  refine ⟨6974828184381540519064289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74398167300069765536685749 6974828184381540519064289)
                  ·
                    refine ⟨5231121138286155389298217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6974828184381540519064289 5231121138286155389298217)
                    ·
                      refine ⟨3923340853714616541973663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231121138286155389298217 3923340853714616541973663)
                      ·
                        rfl

theorem cell23_7640679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_7640679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640679 prefixEnd_7640679 := by exact prefixLift 7640679
  have htrace : WordTrace (prefixWord ++ tailWord_7640679) baseStart_7640679 baseEnd_7640679 := by
    simpa [prefixWord, tailWord_7640679, baseEnd_7640679] using wordTrace_append hprefix tailTrace_7640679
  have hstable : (prefixWord ++ tailWord_7640679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640679).length < 2 ^ (prefixWord ++ tailWord_7640679).sum := by decide
  have hdescent : baseEnd_7640679 < baseStart_7640679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640725 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_7640725 : Nat := 118140960795 + 7640725 * 2 ^ 59
def prefixEnd_7640725 : Nat := 4983230072969 + 3 ^ 40 * 7640725 * 2
def baseEnd_7640725 : Nat := 3923364473824723361998451

theorem tailTrace_7640725 : CollatzResearch.WordTrace tailWord_7640725 prefixEnd_7640725 3923364473824723361998451 := by
  unfold tailWord_7640725
  simp only [CollatzResearch.WordTrace]
  refine ⟨278680135243965731784171629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185786756829310487856114419 278680135243965731784171629)
  ·
    refine ⟨104505050716487149419064361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278680135243965731784171629 104505050716487149419064361)
    ·
      refine ⟨78378788037365362064298271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104505050716487149419064361 78378788037365362064298271)
      ·
        refine ⟨117568182056048043096447407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78378788037365362064298271 117568182056048043096447407)
        ·
          refine ⟨176352273084072064644671111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117568182056048043096447407 176352273084072064644671111)
          ·
            refine ⟨264528409626108096967006667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176352273084072064644671111 264528409626108096967006667)
            ·
              refine ⟨396792614439162145450510001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264528409626108096967006667 396792614439162145450510001)
              ·
                refine ⟨297594460829371609087882501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396792614439162145450510001 297594460829371609087882501)
                ·
                  refine ⟨55798961405507176703977969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297594460829371609087882501 55798961405507176703977969)
                  ·
                    refine ⟨41849221054130382527983477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55798961405507176703977969 41849221054130382527983477)
                    ·
                      refine ⟨3923364473824723361998451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41849221054130382527983477 3923364473824723361998451)
                      ·
                        rfl

theorem cell23_7640725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_7640725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640725 prefixEnd_7640725 := by exact prefixLift 7640725
  have htrace : WordTrace (prefixWord ++ tailWord_7640725) baseStart_7640725 baseEnd_7640725 := by
    simpa [prefixWord, tailWord_7640725, baseEnd_7640725] using wordTrace_append hprefix tailTrace_7640725
  have hstable : (prefixWord ++ tailWord_7640725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640725).length < 2 ^ (prefixWord ++ tailWord_7640725).sum := by decide
  have hdescent : baseEnd_7640725 < baseStart_7640725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640772 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_7640772 : Nat := 118140960795 + 7640772 * 2 ^ 59
def prefixEnd_7640772 : Nat := 4983230072969 + 3 ^ 40 * 7640772 * 2
def baseEnd_7640772 : Nat := 3923388607415484678110735

theorem tailTrace_7640772 : CollatzResearch.WordTrace tailWord_7640772 prefixEnd_7640772 3923388607415484678110735 := by
  unfold tailWord_7640772
  simp only [CollatzResearch.WordTrace]
  refine ⟨139340924737397729405566285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185787899649863639207421713 139340924737397729405566285)
  ·
    refine ⟨52252846776524148527087357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139340924737397729405566285 52252846776524148527087357)
    ·
      refine ⟨19594817541196555697657759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52252846776524148527087357 19594817541196555697657759)
      ·
        refine ⟨29392226311794833546486639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19594817541196555697657759 29392226311794833546486639)
        ·
          refine ⟨44088339467692250319729959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29392226311794833546486639 44088339467692250319729959)
          ·
            refine ⟨66132509201538375479594939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44088339467692250319729959 66132509201538375479594939)
            ·
              refine ⟨99198763802307563219392409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66132509201538375479594939 99198763802307563219392409)
              ·
                refine ⟨74399072851730672414544307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99198763802307563219392409 74399072851730672414544307)
                ·
                  refine ⟨111598609277596008621816461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74399072851730672414544307 111598609277596008621816461)
                  ·
                    refine ⟨41849478479098503233181173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111598609277596008621816461 41849478479098503233181173)
                    ·
                      refine ⟨3923388607415484678110735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41849478479098503233181173 3923388607415484678110735)
                      ·
                        rfl

theorem cell23_7640772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_7640772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640772 prefixEnd_7640772 := by exact prefixLift 7640772
  have htrace : WordTrace (prefixWord ++ tailWord_7640772) baseStart_7640772 baseEnd_7640772 := by
    simpa [prefixWord, tailWord_7640772, baseEnd_7640772] using wordTrace_append hprefix tailTrace_7640772
  have hstable : (prefixWord ++ tailWord_7640772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640772).length < 2 ^ (prefixWord ++ tailWord_7640772).sum := by decide
  have hdescent : baseEnd_7640772 < baseStart_7640772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640780 : List Nat := [2, 2, 1, 5, 2, 2, 2, 1, 2, 1, 3]
def baseStart_7640780 : Nat := 118140960795 + 7640780 * 2 ^ 59
def prefixEnd_7640780 : Nat := 4983230072969 + 3 ^ 40 * 7640780 * 2
def baseEnd_7640780 : Nat := 3923392715260720646810699

theorem tailTrace_7640780 : CollatzResearch.WordTrace tailWord_7640780 prefixEnd_7640780 3923392715260720646810699 := by
  unfold tailWord_7640780
  simp only [CollatzResearch.WordTrace]
  refine ⟨139341070629383238088711897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185788094172510984118282529 139341070629383238088711897)
  ·
    refine ⟨104505802972037428566533923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139341070629383238088711897 104505802972037428566533923)
    ·
      refine ⟨156758704458056142849800885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104505802972037428566533923 156758704458056142849800885)
      ·
        refine ⟨14696128542942763392168833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156758704458056142849800885 14696128542942763392168833)
        ·
          refine ⟨11022096407207072544126625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14696128542942763392168833 11022096407207072544126625)
          ·
            refine ⟨8266572305405304408094969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11022096407207072544126625 8266572305405304408094969)
            ·
              refine ⟨6199929229053978306071227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8266572305405304408094969 6199929229053978306071227)
              ·
                refine ⟨9299893843580967459106841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6199929229053978306071227 9299893843580967459106841)
                ·
                  refine ⟨6974920382685725594330131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9299893843580967459106841 6974920382685725594330131)
                  ·
                    refine ⟨10462380574028588391495197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6974920382685725594330131 10462380574028588391495197)
                    ·
                      refine ⟨3923392715260720646810699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10462380574028588391495197 3923392715260720646810699)
                      ·
                        rfl

theorem cell23_7640780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_7640780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640780 prefixEnd_7640780 := by exact prefixLift 7640780
  have htrace : WordTrace (prefixWord ++ tailWord_7640780) baseStart_7640780 baseEnd_7640780 := by
    simpa [prefixWord, tailWord_7640780, baseEnd_7640780] using wordTrace_append hprefix tailTrace_7640780
  have hstable : (prefixWord ++ tailWord_7640780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640780).length < 2 ^ (prefixWord ++ tailWord_7640780).sum := by decide
  have hdescent : baseEnd_7640780 < baseStart_7640780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640782 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_7640782 : Nat := 118140960795 + 7640782 * 2 ^ 59
def prefixEnd_7640782 : Nat := 4983230072969 + 3 ^ 40 * 7640782 * 2
def baseEnd_7640782 : Nat := 3923393742222029638985689

theorem tailTrace_7640782 : CollatzResearch.WordTrace tailWord_7640782 prefixEnd_7640782 3923393742222029638985689 := by
  unfold tailWord_7640782
  simp only [CollatzResearch.WordTrace]
  refine ⟨34835276775594903814874575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185788142803172820345997733 34835276775594903814874575)
  ·
    refine ⟨52252915163392355722311863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34835276775594903814874575 52252915163392355722311863)
    ·
      refine ⟨78379372745088533583467795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52252915163392355722311863 78379372745088533583467795)
      ·
        refine ⟨117569059117632800375201693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78379372745088533583467795 117569059117632800375201693)
        ·
          refine ⟨44088397169112300140700635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117569059117632800375201693 44088397169112300140700635)
          ·
            refine ⟨66132595753668450211050953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44088397169112300140700635 66132595753668450211050953)
            ·
              refine ⟨49599446815251337658288215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66132595753668450211050953 49599446815251337658288215)
              ·
                refine ⟨74399170222877006487432323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49599446815251337658288215 74399170222877006487432323)
                ·
                  refine ⟨111598755334315509731148485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74399170222877006487432323 111598755334315509731148485)
                  ·
                    refine ⟨20924766625184158074590341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111598755334315509731148485 20924766625184158074590341)
                    ·
                      refine ⟨3923393742222029638985689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20924766625184158074590341 3923393742222029638985689)
                      ·
                        rfl

theorem cell23_7640782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_7640782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640782 prefixEnd_7640782 := by exact prefixLift 7640782
  have htrace : WordTrace (prefixWord ++ tailWord_7640782) baseStart_7640782 baseEnd_7640782 := by
    simpa [prefixWord, tailWord_7640782, baseEnd_7640782] using wordTrace_append hprefix tailTrace_7640782
  have hstable : (prefixWord ++ tailWord_7640782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640782).length < 2 ^ (prefixWord ++ tailWord_7640782).sum := by decide
  have hdescent : baseEnd_7640782 < baseStart_7640782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640790 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_7640790 : Nat := 118140960795 + 7640790 * 2 ^ 59
def prefixEnd_7640790 : Nat := 4983230072969 + 3 ^ 40 * 7640790 * 2
def baseEnd_7640790 : Nat := 3923397850067265607685653

theorem tailTrace_7640790 : CollatzResearch.WordTrace tailWord_7640790 prefixEnd_7640790 3923397850067265607685653 := by
  unfold tailWord_7640790
  simp only [CollatzResearch.WordTrace]
  refine ⟨17417656624295640492830489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185788337325820165256858549 17417656624295640492830489)
  ·
    refine ⟨13063242468221730369622867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17417656624295640492830489 13063242468221730369622867)
    ·
      refine ⟨19594863702332595554434301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13063242468221730369622867 19594863702332595554434301)
      ·
        refine ⟨7348073888374723332912863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19594863702332595554434301 7348073888374723332912863)
        ·
          refine ⟨11022110832562084999369295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7348073888374723332912863 11022110832562084999369295)
          ·
            refine ⟨16533166248843127499053943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11022110832562084999369295 16533166248843127499053943)
            ·
              refine ⟨24799749373264691248580915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16533166248843127499053943 24799749373264691248580915)
              ·
                refine ⟨37199624059897036872871373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24799749373264691248580915 37199624059897036872871373)
                ·
                  refine ⟨13949859022461388827326765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37199624059897036872871373 13949859022461388827326765)
                  ·
                    refine ⟨5231197133423020810247537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13949859022461388827326765 5231197133423020810247537)
                    ·
                      refine ⟨3923397850067265607685653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231197133423020810247537 3923397850067265607685653)
                      ·
                        rfl

theorem cell23_7640790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_7640790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640790 prefixEnd_7640790 := by exact prefixLift 7640790
  have htrace : WordTrace (prefixWord ++ tailWord_7640790) baseStart_7640790 baseEnd_7640790 := by
    simpa [prefixWord, tailWord_7640790, baseEnd_7640790] using wordTrace_append hprefix tailTrace_7640790
  have hstable : (prefixWord ++ tailWord_7640790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640790).length < 2 ^ (prefixWord ++ tailWord_7640790).sum := by decide
  have hdescent : baseEnd_7640790 < baseStart_7640790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640929 : List Nat := [1, 2, 3, 1, 1, 1, 3, 5, 1, 5]
def baseStart_7640929 : Nat := 118140960795 + 7640929 * 2 ^ 59
def prefixEnd_7640929 : Nat := 4983230072969 + 3 ^ 40 * 7640929 * 2
def baseEnd_7640929 : Nat := 1307823074626080187949171

theorem tailTrace_7640929 : CollatzResearch.WordTrace tailWord_7640929 prefixEnd_7640929 1307823074626080187949171 := by
  unfold tailWord_7640929
  simp only [CollatzResearch.WordTrace]
  refine ⟨278687575735226674624597841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185791717156817783083065227 278687575735226674624597841)
  ·
    refine ⟨209015681801420005968448381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278687575735226674624597841 209015681801420005968448381)
    ·
      refine ⟨78380880675532502238168143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209015681801420005968448381 78380880675532502238168143)
      ·
        refine ⟨117571321013298753357252215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78380880675532502238168143 117571321013298753357252215)
        ·
          refine ⟨176356981519948130035878323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117571321013298753357252215 176356981519948130035878323)
          ·
            refine ⟨264535472279922195053817485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176356981519948130035878323 264535472279922195053817485)
            ·
              refine ⟨99200802104970823145181557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264535472279922195053817485 99200802104970823145181557)
              ·
                refine ⟨9300075197341014669860771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99200802104970823145181557 9300075197341014669860771)
                ·
                  refine ⟨13950112796011522004791157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9300075197341014669860771 13950112796011522004791157)
                  ·
                    refine ⟨1307823074626080187949171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13950112796011522004791157 1307823074626080187949171)
                    ·
                      rfl

theorem cell23_7640929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_7640929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640929 prefixEnd_7640929 := by exact prefixLift 7640929
  have htrace : WordTrace (prefixWord ++ tailWord_7640929) baseStart_7640929 baseEnd_7640929 := by
    simpa [prefixWord, tailWord_7640929, baseEnd_7640929] using wordTrace_append hprefix tailTrace_7640929
  have hstable : (prefixWord ++ tailWord_7640929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640929).length < 2 ^ (prefixWord ++ tailWord_7640929).sum := by decide
  have hdescent : baseEnd_7640929 < baseStart_7640929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640950 : List Nat := [5, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_7640950 : Nat := 118140960795 + 7640950 * 2 ^ 59
def prefixEnd_7640950 : Nat := 4983230072969 + 3 ^ 40 * 7640950 * 2
def baseEnd_7640950 : Nat := 435942222996887220187213

theorem tailTrace_7640950 : CollatzResearch.WordTrace tailWord_7640950 prefixEnd_7640950 435942222996887220187213 := by
  unfold tailWord_7640950
  simp only [CollatzResearch.WordTrace]
  refine ⟨17418021354259412200694519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185792227778767063474074869 17418021354259412200694519)
  ·
    refine ⟨26127032031389118301041779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17418021354259412200694519 26127032031389118301041779)
    ·
      refine ⟨39190548047083677451562669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26127032031389118301041779 39190548047083677451562669)
      ·
        refine ⟨14696455517656379044336001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39190548047083677451562669 14696455517656379044336001)
        ·
          refine ⟨11022341638242284283252001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14696455517656379044336001 11022341638242284283252001)
          ·
            refine ⟨8266756228681713212439001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11022341638242284283252001 8266756228681713212439001)
            ·
              refine ⟨6200067171511284909329251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8266756228681713212439001 6200067171511284909329251)
              ·
                refine ⟨9300100757266927363993877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6200067171511284909329251 9300100757266927363993877)
                ·
                  refine ⟨435942222996887220187213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9300100757266927363993877 435942222996887220187213)
                  ·
                    rfl

theorem cell23_7640950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_7640950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640950 prefixEnd_7640950 := by exact prefixLift 7640950
  have htrace : WordTrace (prefixWord ++ tailWord_7640950) baseStart_7640950 baseEnd_7640950 := by
    simpa [prefixWord, tailWord_7640950, baseEnd_7640950] using wordTrace_append hprefix tailTrace_7640950
  have hstable : (prefixWord ++ tailWord_7640950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640950).length < 2 ^ (prefixWord ++ tailWord_7640950).sum := by decide
  have hdescent : baseEnd_7640950 < baseStart_7640950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640952 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_7640952 : Nat := 118140960795 + 7640952 * 2 ^ 59
def prefixEnd_7640952 : Nat := 4983230072969 + 3 ^ 40 * 7640952 * 2
def baseEnd_7640952 : Nat := 3923481033933293973859907

theorem tailTrace_7640952 : CollatzResearch.WordTrace tailWord_7640952 prefixEnd_7640952 3923481033933293973859907 := by
  unfold tailWord_7640952
  simp only [CollatzResearch.WordTrace]
  refine ⟨139344207307071674776342555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185792276409428899701790073 139344207307071674776342555)
  ·
    refine ⟨209016310960607512164513833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139344207307071674776342555 209016310960607512164513833)
    ·
      refine ⟨156762233220455634123385375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209016310960607512164513833 156762233220455634123385375)
      ·
        refine ⟨235143349830683451185078063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156762233220455634123385375 235143349830683451185078063)
        ·
          refine ⟨352715024746025176777617095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235143349830683451185078063 352715024746025176777617095)
          ·
            refine ⟨529072537119037765166425643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352715024746025176777617095 529072537119037765166425643)
            ·
              refine ⟨793608805678556647749638465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529072537119037765166425643 793608805678556647749638465)
              ·
                refine ⟨595206604258917485812228849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793608805678556647749638465 595206604258917485812228849)
                ·
                  refine ⟨446404953194188114359171637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595206604258917485812228849 446404953194188114359171637)
                  ·
                    refine ⟨41850464361955135721172341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 446404953194188114359171637 41850464361955135721172341)
                    ·
                      refine ⟨3923481033933293973859907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41850464361955135721172341 3923481033933293973859907)
                      ·
                        rfl

theorem cell23_7640952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_7640952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640952 prefixEnd_7640952 := by exact prefixLift 7640952
  have htrace : WordTrace (prefixWord ++ tailWord_7640952) baseStart_7640952 baseEnd_7640952 := by
    simpa [prefixWord, tailWord_7640952, baseEnd_7640952] using wordTrace_append hprefix tailTrace_7640952
  have hstable : (prefixWord ++ tailWord_7640952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640952).length < 2 ^ (prefixWord ++ tailWord_7640952).sum := by decide
  have hdescent : baseEnd_7640952 < baseStart_7640952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640970 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 2, 3, 2]
def baseStart_7640970 : Nat := 118140960795 + 7640970 * 2 ^ 59
def prefixEnd_7640970 : Nat := 4983230072969 + 3 ^ 40 * 7640970 * 2
def baseEnd_7640970 : Nat := 3923490276585074903434825

theorem tailTrace_7640970 : CollatzResearch.WordTrace tailWord_7640970 prefixEnd_7640970 3923490276585074903434825 := by
  unfold tailWord_7640970
  simp only [CollatzResearch.WordTrace]
  refine ⟨69672267782019534656710091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185792714085385425751226909 69672267782019534656710091)
  ·
    refine ⟨104508401673029301985065137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69672267782019534656710091 104508401673029301985065137)
    ·
      refine ⟨78381301254771976488798853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104508401673029301985065137 78381301254771976488798853)
      ·
        refine ⟨14696493985269745591649785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78381301254771976488798853 14696493985269745591649785)
        ·
          refine ⟨11022370488952309193737339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14696493985269745591649785 11022370488952309193737339)
          ·
            refine ⟨16533555733428463790606009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11022370488952309193737339 16533555733428463790606009)
            ·
              refine ⟨12400166800071347842954507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16533555733428463790606009 12400166800071347842954507)
              ·
                refine ⟨18600250200107021764431761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12400166800071347842954507 18600250200107021764431761)
                ·
                  refine ⟨13950187650080266323323821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18600250200107021764431761 13950187650080266323323821)
                  ·
                    refine ⟨5231320368780099871246433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13950187650080266323323821 5231320368780099871246433)
                    ·
                      refine ⟨3923490276585074903434825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231320368780099871246433 3923490276585074903434825)
                      ·
                        rfl

theorem cell23_7640970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_7640970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640970 prefixEnd_7640970 := by exact prefixLift 7640970
  have htrace : WordTrace (prefixWord ++ tailWord_7640970) baseStart_7640970 baseEnd_7640970 := by
    simpa [prefixWord, tailWord_7640970, baseEnd_7640970] using wordTrace_append hprefix tailTrace_7640970
  have hstable : (prefixWord ++ tailWord_7640970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640970).length < 2 ^ (prefixWord ++ tailWord_7640970).sum := by decide
  have hdescent : baseEnd_7640970 < baseStart_7640970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640983 : List Nat := [1, 1, 3, 3, 1, 4, 3, 1, 1, 1, 4]
def baseStart_7640983 : Nat := 118140960795 + 7640983 * 2 ^ 59
def prefixEnd_7640983 : Nat := 4983230072969 + 3 ^ 40 * 7640983 * 2
def baseEnd_7640983 : Nat := 3923496951833583352572265

theorem tailTrace_7640983 : CollatzResearch.WordTrace tailWord_7640983 prefixEnd_7640983 3923496951833583352572265 := by
  unfold tailWord_7640983
  simp only [CollatzResearch.WordTrace]
  refine ⟨278689545277031041847063603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185793030184687361231375735 278689545277031041847063603)
  ·
    refine ⟨418034317915546562770595405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278689545277031041847063603 418034317915546562770595405)
    ·
      refine ⟨156762869218329961038973277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418034317915546562770595405 156762869218329961038973277)
      ·
        refine ⟨58786075956873735389614979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156762869218329961038973277 58786075956873735389614979)
        ·
          refine ⟨88179113935310603084422469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58786075956873735389614979 88179113935310603084422469)
          ·
            refine ⟨16533583862870738078329213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88179113935310603084422469 16533583862870738078329213)
            ·
              refine ⟨6200093948576526779373455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16533583862870738078329213 6200093948576526779373455)
              ·
                refine ⟨9300140922864790169060183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6200093948576526779373455 9300140922864790169060183)
                ·
                  refine ⟨13950211384297185253590275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9300140922864790169060183 13950211384297185253590275)
                  ·
                    refine ⟨20925317076445777880385413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13950211384297185253590275 20925317076445777880385413)
                    ·
                      refine ⟨3923496951833583352572265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20925317076445777880385413 3923496951833583352572265)
                      ·
                        rfl

theorem cell23_7640983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_7640983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640983 prefixEnd_7640983 := by exact prefixLift 7640983
  have htrace : WordTrace (prefixWord ++ tailWord_7640983) baseStart_7640983 baseEnd_7640983 := by
    simpa [prefixWord, tailWord_7640983, baseEnd_7640983] using wordTrace_append hprefix tailTrace_7640983
  have hstable : (prefixWord ++ tailWord_7640983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640983).length < 2 ^ (prefixWord ++ tailWord_7640983).sum := by decide
  have hdescent : baseEnd_7640983 < baseStart_7640983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640986 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5]
def baseStart_7640986 : Nat := 118140960795 + 7640986 * 2 ^ 59
def prefixEnd_7640986 : Nat := 4983230072969 + 3 ^ 40 * 7640986 * 2
def baseEnd_7640986 : Nat := 3923498492275546840834751

theorem tailTrace_7640986 : CollatzResearch.WordTrace tailWord_7640986 prefixEnd_7640986 3923498492275546840834751 := by
  unfold tailWord_7640986
  simp only [CollatzResearch.WordTrace]
  refine ⟨69672413674005043339855703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185793103130680115572948541 69672413674005043339855703)
  ·
    refine ⟨104508620511007565009783555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69672413674005043339855703 104508620511007565009783555)
    ·
      refine ⟨156762930766511347514675333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104508620511007565009783555 156762930766511347514675333)
      ·
        refine ⟨29393049518720877659001625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156762930766511347514675333 29393049518720877659001625)
        ·
          refine ⟨22044787139040658244251219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29393049518720877659001625 22044787139040658244251219)
          ·
            refine ⟨33067180708560987366376829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22044787139040658244251219 33067180708560987366376829)
            ·
              refine ⟨12400192765710370262391311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33067180708560987366376829 12400192765710370262391311)
              ·
                refine ⟨18600289148565555393586967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12400192765710370262391311 18600289148565555393586967)
                ·
                  refine ⟨27900433722848333090380451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18600289148565555393586967 27900433722848333090380451)
                  ·
                    refine ⟨41850650584272499635570677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27900433722848333090380451 41850650584272499635570677)
                    ·
                      refine ⟨3923498492275546840834751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41850650584272499635570677 3923498492275546840834751)
                      ·
                        rfl

theorem cell23_7640986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_7640986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640986 prefixEnd_7640986 := by exact prefixLift 7640986
  have htrace : WordTrace (prefixWord ++ tailWord_7640986) baseStart_7640986 baseEnd_7640986 := by
    simpa [prefixWord, tailWord_7640986, baseEnd_7640986] using wordTrace_append hprefix tailTrace_7640986
  have hstable : (prefixWord ++ tailWord_7640986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640986).length < 2 ^ (prefixWord ++ tailWord_7640986).sum := by decide
  have hdescent : baseEnd_7640986 < baseStart_7640986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7640994 : List Nat := [3, 3, 1, 2, 3, 2, 2, 2, 1, 1, 3]
def baseStart_7640994 : Nat := 118140960795 + 7640994 * 2 ^ 59
def prefixEnd_7640994 : Nat := 4983230072969 + 3 ^ 40 * 7640994 * 2
def baseEnd_7640994 : Nat := 3923502600120782809534715

theorem tailTrace_7640994 : CollatzResearch.WordTrace tailWord_7640994 prefixEnd_7640994 3923502600120782809534715 := by
  unfold tailWord_7640994
  simp only [CollatzResearch.WordTrace]
  refine ⟨69672486619997797681428509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185793297653327460483809357 69672486619997797681428509)
  ·
    refine ⟨26127182482499174130535691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69672486619997797681428509 26127182482499174130535691)
    ·
      refine ⟨39190773723748761195803537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26127182482499174130535691 39190773723748761195803537)
      ·
        refine ⟨29393080292811570896852653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39190773723748761195803537 29393080292811570896852653)
        ·
          refine ⟨11022405109804339086319745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29393080292811570896852653 11022405109804339086319745)
          ·
            refine ⟨8266803832353254314739809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11022405109804339086319745 8266803832353254314739809)
            ·
              refine ⟨6200102874264940736054857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8266803832353254314739809 6200102874264940736054857)
              ·
                refine ⟨4650077155698705552041143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6200102874264940736054857 4650077155698705552041143)
                ·
                  refine ⟨6975115733548058328061715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4650077155698705552041143 6975115733548058328061715)
                  ·
                    refine ⟨10462673600322087492092573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6975115733548058328061715 10462673600322087492092573)
                    ·
                      refine ⟨3923502600120782809534715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10462673600322087492092573 3923502600120782809534715)
                      ·
                        rfl

theorem cell23_7640994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_7640994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7640994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7640994 prefixEnd_7640994 := by exact prefixLift 7640994
  have htrace : WordTrace (prefixWord ++ tailWord_7640994) baseStart_7640994 baseEnd_7640994 := by
    simpa [prefixWord, tailWord_7640994, baseEnd_7640994] using wordTrace_append hprefix tailTrace_7640994
  have hstable : (prefixWord ++ tailWord_7640994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7640994).length < 2 ^ (prefixWord ++ tailWord_7640994).sum := by decide
  have hdescent : baseEnd_7640994 < baseStart_7640994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7640994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641016 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 1, 3, 3]
def baseStart_7641016 : Nat := 118140960795 + 7641016 * 2 ^ 59
def prefixEnd_7641016 : Nat := 4983230072969 + 3 ^ 40 * 7641016 * 2
def baseEnd_7641016 : Nat := 3923513896695181723459613

theorem tailTrace_7641016 : CollatzResearch.WordTrace tailWord_7641016 prefixEnd_7641016 3923513896695181723459613 := by
  unfold tailWord_7641016
  simp only [CollatzResearch.WordTrace]
  refine ⟨139345374442955744241507451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185793832590607658988676601 139345374442955744241507451)
  ·
    refine ⟨209018061664433616362261177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139345374442955744241507451 209018061664433616362261177)
    ·
      refine ⟨156763546248325212271695883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209018061664433616362261177 156763546248325212271695883)
      ·
        refine ⟨235145319372487818407543825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156763546248325212271695883 235145319372487818407543825)
        ·
          refine ⟨176358989529365863805657869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235145319372487818407543825 176358989529365863805657869)
          ·
            refine ⟨66134621073512198927121701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176358989529365863805657869 66134621073512198927121701)
            ·
              refine ⟨12400241451283537298835319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66134621073512198927121701 12400241451283537298835319)
              ·
                refine ⟨18600362176925305948252979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12400241451283537298835319 18600362176925305948252979)
                ·
                  refine ⟨27900543265387958922379469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18600362176925305948252979 27900543265387958922379469)
                  ·
                    refine ⟨10462703724520484595892301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27900543265387958922379469 10462703724520484595892301)
                    ·
                      refine ⟨3923513896695181723459613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10462703724520484595892301 3923513896695181723459613)
                      ·
                        rfl

theorem cell23_7641016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_7641016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641016 prefixEnd_7641016 := by exact prefixLift 7641016
  have htrace : WordTrace (prefixWord ++ tailWord_7641016) baseStart_7641016 baseEnd_7641016 := by
    simpa [prefixWord, tailWord_7641016, baseEnd_7641016] using wordTrace_append hprefix tailTrace_7641016
  have hstable : (prefixWord ++ tailWord_7641016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641016).length < 2 ^ (prefixWord ++ tailWord_7641016).sum := by decide
  have hdescent : baseEnd_7641016 < baseStart_7641016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641056 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 3, 4, 2]
def baseStart_7641056 : Nat := 118140960795 + 7641056 * 2 ^ 59
def prefixEnd_7641056 : Nat := 4983230072969 + 3 ^ 40 * 7641056 * 2
def baseEnd_7641056 : Nat := 3923534435921361566959429

theorem tailTrace_7641056 : CollatzResearch.WordTrace tailWord_7641056 prefixEnd_7641056 3923534435921361566959429 := by
  unfold tailWord_7641056
  simp only [CollatzResearch.WordTrace]
  refine ⟨139346103902883287657235511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185794805203844383542980681 139346103902883287657235511)
  ·
    refine ⟨209019155854324931485853267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139346103902883287657235511 209019155854324931485853267)
    ·
      refine ⟨313528733781487397228779901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209019155854324931485853267 313528733781487397228779901)
      ·
        refine ⟨117573275168057773960792463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313528733781487397228779901 117573275168057773960792463)
        ·
          refine ⟨176359912752086660941188695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117573275168057773960792463 176359912752086660941188695)
          ·
            refine ⟨264539869128129991411783043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176359912752086660941188695 264539869128129991411783043)
            ·
              refine ⟨396809803692194987117674565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264539869128129991411783043 396809803692194987117674565)
              ·
                refine ⟨74401838192286560084563981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396809803692194987117674565 74401838192286560084563981)
                ·
                  refine ⟨27900689322107460031711493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74401838192286560084563981 27900689322107460031711493)
                  ·
                    refine ⟨5231379247895148755945905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27900689322107460031711493 5231379247895148755945905)
                    ·
                      refine ⟨3923534435921361566959429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231379247895148755945905 3923534435921361566959429)
                      ·
                        rfl

theorem cell23_7641056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_7641056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641056 prefixEnd_7641056 := by exact prefixLift 7641056
  have htrace : WordTrace (prefixWord ++ tailWord_7641056) baseStart_7641056 baseEnd_7641056 := by
    simpa [prefixWord, tailWord_7641056, baseEnd_7641056] using wordTrace_append hprefix tailTrace_7641056
  have hstable : (prefixWord ++ tailWord_7641056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641056).length < 2 ^ (prefixWord ++ tailWord_7641056).sum := by decide
  have hdescent : baseEnd_7641056 < baseStart_7641056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641139 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 2, 8]
def baseStart_7641139 : Nat := 118140960795 + 7641139 * 2 ^ 59
def prefixEnd_7641139 : Nat := 4983230072969 + 3 ^ 40 * 7641139 * 2
def baseEnd_7641139 : Nat := 1307859018271894914073849

theorem tailTrace_7641139 : CollatzResearch.WordTrace tailWord_7641139 prefixEnd_7641139 1307859018271894914073849 := by
  unfold tailWord_7641139
  simp only [CollatzResearch.WordTrace]
  refine ⟨278695235064465880489742471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185796823376310586993161647 278695235064465880489742471)
  ·
    refine ⟨418042852596698820734613707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278695235064465880489742471 418042852596698820734613707)
    ·
      refine ⟨627064278895048231101920561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418042852596698820734613707 627064278895048231101920561)
      ·
        refine ⟨470298209171286173326440421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627064278895048231101920561 470298209171286173326440421)
        ·
          refine ⟨88180914219616157498707579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 470298209171286173326440421 88180914219616157498707579)
          ·
            refine ⟨132271371329424236248061369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88180914219616157498707579 132271371329424236248061369)
            ·
              refine ⟨99203528497068177186046027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132271371329424236248061369 99203528497068177186046027)
              ·
                refine ⟨148805292745602265779069041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99203528497068177186046027 148805292745602265779069041)
                ·
                  refine ⟨111603969559201699334301781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148805292745602265779069041 111603969559201699334301781)
                  ·
                    refine ⟨1307859018271894914073849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111603969559201699334301781 1307859018271894914073849)
                    ·
                      rfl

theorem cell23_7641139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 8].length) (baseStart_7641139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641139 prefixEnd_7641139 := by exact prefixLift 7641139
  have htrace : WordTrace (prefixWord ++ tailWord_7641139) baseStart_7641139 baseEnd_7641139 := by
    simpa [prefixWord, tailWord_7641139, baseEnd_7641139] using wordTrace_append hprefix tailTrace_7641139
  have hstable : (prefixWord ++ tailWord_7641139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641139).length < 2 ^ (prefixWord ++ tailWord_7641139).sum := by decide
  have hdescent : baseEnd_7641139 < baseStart_7641139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641180 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_7641180 : Nat := 118140960795 + 7641180 * 2 ^ 59
def prefixEnd_7641180 : Nat := 4983230072969 + 3 ^ 40 * 7641180 * 2
def baseEnd_7641180 : Nat := 3923598107522519081808859

theorem tailTrace_7641180 : CollatzResearch.WordTrace tailWord_7641180 prefixEnd_7641180 3923598107522519081808859 := by
  unfold tailWord_7641180
  simp only [CollatzResearch.WordTrace]
  refine ⟨139348365228658672245992497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185797820304878229661323329 139348365228658672245992497)
  ·
    refine ⟨104511273921494004184494373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139348365228658672245992497 104511273921494004184494373)
    ·
      refine ⟨19595863860280125784592695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104511273921494004184494373 19595863860280125784592695)
      ·
        refine ⟨29393795790420188676889043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19595863860280125784592695 29393795790420188676889043)
        ·
          refine ⟨44090693685630283015333565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29393795790420188676889043 44090693685630283015333565)
          ·
            refine ⟨16534010132111356130750087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44090693685630283015333565 16534010132111356130750087)
            ·
              refine ⟨24801015198167034196125131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16534010132111356130750087 24801015198167034196125131)
              ·
                refine ⟨37201522797250551294187697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24801015198167034196125131 37201522797250551294187697)
                ·
                  refine ⟨27901142097937913470640773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37201522797250551294187697 27901142097937913470640773)
                  ·
                    refine ⟨5231464143363358775745145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27901142097937913470640773 5231464143363358775745145)
                    ·
                      refine ⟨3923598107522519081808859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231464143363358775745145 3923598107522519081808859)
                      ·
                        rfl

theorem cell23_7641180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_7641180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641180 prefixEnd_7641180 := by exact prefixLift 7641180
  have htrace : WordTrace (prefixWord ++ tailWord_7641180) baseStart_7641180 baseEnd_7641180 := by
    simpa [prefixWord, tailWord_7641180, baseEnd_7641180] using wordTrace_append hprefix tailTrace_7641180
  have hstable : (prefixWord ++ tailWord_7641180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641180).length < 2 ^ (prefixWord ++ tailWord_7641180).sum := by decide
  have hdescent : baseEnd_7641180 < baseStart_7641180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641200 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 3]
def baseStart_7641200 : Nat := 118140960795 + 7641200 * 2 ^ 59
def prefixEnd_7641200 : Nat := 4983230072969 + 3 ^ 40 * 7641200 * 2
def baseEnd_7641200 : Nat := 3923608377135609003558767

theorem tailTrace_7641200 : CollatzResearch.WordTrace tailWord_7641200 prefixEnd_7641200 3923608377135609003558767 := by
  unfold tailWord_7641200
  simp only [CollatzResearch.WordTrace]
  refine ⟨139348729958622443953856527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185798306611496591938475369 139348729958622443953856527)
  ·
    refine ⟨209023094937933665930784791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139348729958622443953856527 209023094937933665930784791)
    ·
      refine ⟨313534642406900498896177187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209023094937933665930784791 313534642406900498896177187)
      ·
        refine ⟨470301963610350748344265781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313534642406900498896177187 470301963610350748344265781)
        ·
          refine ⟨44090809088470382657274917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 470301963610350748344265781 44090809088470382657274917)
          ·
            refine ⟨8267026704088196748239047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44090809088470382657274917 8267026704088196748239047)
            ·
              refine ⟨12400540056132295122358571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8267026704088196748239047 12400540056132295122358571)
              ·
                refine ⟨18600810084198442683537857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12400540056132295122358571 18600810084198442683537857)
                ·
                  refine ⟨13950607563148832012653393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18600810084198442683537857 13950607563148832012653393)
                  ·
                    refine ⟨10462955672361624009490045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13950607563148832012653393 10462955672361624009490045)
                    ·
                      refine ⟨3923608377135609003558767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10462955672361624009490045 3923608377135609003558767)
                      ·
                        rfl

theorem cell23_7641200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 3].length) (baseStart_7641200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641200 prefixEnd_7641200 := by exact prefixLift 7641200
  have htrace : WordTrace (prefixWord ++ tailWord_7641200) baseStart_7641200 baseEnd_7641200 := by
    simpa [prefixWord, tailWord_7641200, baseEnd_7641200] using wordTrace_append hprefix tailTrace_7641200
  have hstable : (prefixWord ++ tailWord_7641200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641200).length < 2 ^ (prefixWord ++ tailWord_7641200).sum := by decide
  have hdescent : baseEnd_7641200 < baseStart_7641200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641250 : List Nat := [3, 3, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_7641250 : Nat := 118140960795 + 7641250 * 2 ^ 59
def prefixEnd_7641250 : Nat := 4983230072969 + 3 ^ 40 * 7641250 * 2
def baseEnd_7641250 : Nat := 1307878017056111269311179

theorem tailTrace_7641250 : CollatzResearch.WordTrace tailWord_7641250 prefixEnd_7641250 1307878017056111269311179 := by
  unfold tailWord_7641250
  simp only [CollatzResearch.WordTrace]
  refine ⟨69674820891765936611758301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185799522378042497631355469 69674820891765936611758301)
  ·
    refine ⟨26128057834412226229409363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69674820891765936611758301 26128057834412226229409363)
    ·
      refine ⟨39192086751618339344114045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26128057834412226229409363 39192086751618339344114045)
      ·
        refine ⟨14697032531856877254042767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39192086751618339344114045 14697032531856877254042767)
        ·
          refine ⟨22045548797785315881064151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14697032531856877254042767 22045548797785315881064151)
          ·
            refine ⟨33068323196677973821596227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22045548797785315881064151 33068323196677973821596227)
            ·
              refine ⟨49602484795016960732394341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33068323196677973821596227 49602484795016960732394341)
              ·
                refine ⟨9300465899065680137323939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49602484795016960732394341 9300465899065680137323939)
                ·
                  refine ⟨13950698848598520205985909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9300465899065680137323939 13950698848598520205985909)
                  ·
                    refine ⟨1307878017056111269311179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13950698848598520205985909 1307878017056111269311179)
                    ·
                      rfl

theorem cell23_7641250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_7641250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641250 prefixEnd_7641250 := by exact prefixLift 7641250
  have htrace : WordTrace (prefixWord ++ tailWord_7641250) baseStart_7641250 baseEnd_7641250 := by
    simpa [prefixWord, tailWord_7641250, baseEnd_7641250] using wordTrace_append hprefix tailTrace_7641250
  have hstable : (prefixWord ++ tailWord_7641250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641250).length < 2 ^ (prefixWord ++ tailWord_7641250).sum := by decide
  have hdescent : baseEnd_7641250 < baseStart_7641250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641253 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 2, 6, 2]
def baseStart_7641253 : Nat := 118140960795 + 7641253 * 2 ^ 59
def prefixEnd_7641253 : Nat := 4983230072969 + 3 ^ 40 * 7641253 * 2
def baseEnd_7641253 : Nat := 3923635591610297296196023

theorem tailTrace_7641253 : CollatzResearch.WordTrace tailWord_7641253 prefixEnd_7641253 3923635591610297296196023 := by
  unfold tailWord_7641253
  simp only [CollatzResearch.WordTrace]
  refine ⟨278699392986052877959392413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185799595324035251972928275 278699392986052877959392413)
  ·
    refine ⟨104512272369769829234772155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278699392986052877959392413 104512272369769829234772155)
    ·
      refine ⟨156768408554654743852158233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104512272369769829234772155 156768408554654743852158233)
      ·
        refine ⟨117576306415991057889118675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156768408554654743852158233 117576306415991057889118675)
        ·
          refine ⟨176364459623986586833678013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117576306415991057889118675 176364459623986586833678013)
          ·
            refine ⟨66136672358994970062629255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176364459623986586833678013 66136672358994970062629255)
            ·
              refine ⟨99205008538492455093943883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66136672358994970062629255 99205008538492455093943883)
              ·
                refine ⟨148807512807738682640915825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99205008538492455093943883 148807512807738682640915825)
                ·
                  refine ⟨111605634605804011980686869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148807512807738682640915825 111605634605804011980686869)
                  ·
                    refine ⟨5231514122147063061594697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111605634605804011980686869 5231514122147063061594697)
                    ·
                      refine ⟨3923635591610297296196023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231514122147063061594697 3923635591610297296196023)
                      ·
                        rfl

theorem cell23_7641253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_7641253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641253 prefixEnd_7641253 := by exact prefixLift 7641253
  have htrace : WordTrace (prefixWord ++ tailWord_7641253) baseStart_7641253 baseEnd_7641253 := by
    simpa [prefixWord, tailWord_7641253, baseEnd_7641253] using wordTrace_append hprefix tailTrace_7641253
  have hstable : (prefixWord ++ tailWord_7641253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641253).length < 2 ^ (prefixWord ++ tailWord_7641253).sum := by decide
  have hdescent : baseEnd_7641253 < baseStart_7641253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
