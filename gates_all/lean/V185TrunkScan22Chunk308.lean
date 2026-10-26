import V185TrunkScan22Chunk307

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2747569 : List Nat := [1, 2, 2, 5, 1, 3, 2, 1, 1, 4]
def baseStart_2747569 : Nat := 118140960795 + 2747569 * 2 ^ 59
def prefixEnd_2747569 : Nat := 4983230072969 + 3 ^ 40 * 2747569 * 2
def baseEnd_2747569 : Nat := 940549018928843904901111

theorem tailTrace_2747569 : CollatzResearch.WordTrace tailWord_2747569 prefixEnd_2747569 940549018928843904901111 := by
  unfold tailWord_2747569
  simp only [CollatzResearch.WordTrace]
  refine ⟨100212074183034235271613761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66808049455356156847742507 100212074183034235271613761)
  ·
    refine ⟨75159055637275676453710321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100212074183034235271613761 75159055637275676453710321)
    ·
      refine ⟨56369291727956757340282741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75159055637275676453710321 56369291727956757340282741)
      ·
        refine ⟨5284621099495946000651507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56369291727956757340282741 5284621099495946000651507)
        ·
          refine ⟨7926931649243919000977261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5284621099495946000651507 7926931649243919000977261)
          ·
            refine ⟨2972599368466469625366473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7926931649243919000977261 2972599368466469625366473)
            ·
              refine ⟨2229449526349852219024855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2972599368466469625366473 2229449526349852219024855)
              ·
                refine ⟨3344174289524778328537283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229449526349852219024855 3344174289524778328537283)
                ·
                  refine ⟨5016261434287167492805925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344174289524778328537283 5016261434287167492805925)
                  ·
                    refine ⟨940549018928843904901111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5016261434287167492805925 940549018928843904901111)
                    ·
                      rfl

theorem cell22_2747569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_2747569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747569 prefixEnd_2747569 := by exact prefixLift 2747569
  have htrace : WordTrace (prefixWord ++ tailWord_2747569) baseStart_2747569 baseEnd_2747569 := by
    simpa [prefixWord, tailWord_2747569, baseEnd_2747569] using wordTrace_append hprefix tailTrace_2747569
  have hstable : (prefixWord ++ tailWord_2747569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747569).length < 2 ^ (prefixWord ++ tailWord_2747569).sum := by decide
  have hdescent : baseEnd_2747569 < baseStart_2747569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747582 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_2747582 : Nat := 118140960795 + 2747582 * 2 ^ 59
def prefixEnd_2747582 : Nat := 4983230072969 + 3 ^ 40 * 2747582 * 2
def baseEnd_2747582 : Nat := 940553469094516204326071

theorem tailTrace_2747582 : CollatzResearch.WordTrace tailWord_2747582 prefixEnd_2747582 940553469094516204326071 := by
  unfold tailWord_2747582
  simp only [CollatzResearch.WordTrace]
  refine ⟨12526568541498392311479625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66808365554658092327891333 12526568541498392311479625)
  ·
    refine ⟨9394926406123794233609719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12526568541498392311479625 9394926406123794233609719)
    ·
      refine ⟨14092389609185691350414579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9394926406123794233609719 14092389609185691350414579)
      ·
        refine ⟨21138584413778537025621869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14092389609185691350414579 21138584413778537025621869)
        ·
          refine ⟨7926969155166951384608201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21138584413778537025621869 7926969155166951384608201)
          ·
            refine ⟨5945226866375213538456151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7926969155166951384608201 5945226866375213538456151)
            ·
              refine ⟨8917840299562820307684227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5945226866375213538456151 8917840299562820307684227)
              ·
                refine ⟨13376760449344230461526341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8917840299562820307684227 13376760449344230461526341)
                ·
                  refine ⟨2508142584252043211536189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13376760449344230461526341 2508142584252043211536189)
                  ·
                    refine ⟨940553469094516204326071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2508142584252043211536189 940553469094516204326071)
                    ·
                      rfl

theorem cell22_2747582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_2747582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747582 prefixEnd_2747582 := by exact prefixLift 2747582
  have htrace : WordTrace (prefixWord ++ tailWord_2747582) baseStart_2747582 baseEnd_2747582 := by
    simpa [prefixWord, tailWord_2747582, baseEnd_2747582] using wordTrace_append hprefix tailTrace_2747582
  have hstable : (prefixWord ++ tailWord_2747582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747582).length < 2 ^ (prefixWord ++ tailWord_2747582).sum := by decide
  have hdescent : baseEnd_2747582 < baseStart_2747582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747644 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 3, 3]
def baseStart_2747644 : Nat := 118140960795 + 2747644 * 2 ^ 59
def prefixEnd_2747644 : Nat := 4983230072969 + 3 ^ 40 * 2747644 * 2
def baseEnd_2747644 : Nat := 940574692961568709275881

theorem tailTrace_2747644 : CollatzResearch.WordTrace tailWord_2747644 prefixEnd_2747644 940574692961568709275881 := by
  unfold tailWord_2747644
  simp only [CollatzResearch.WordTrace]
  refine ⟨50107404828881261540296993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66809873105175015387062657 50107404828881261540296993)
  ·
    refine ⟨37580553621660946155222745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50107404828881261540296993 37580553621660946155222745)
    ·
      refine ⟨28185415216245709616417059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37580553621660946155222745 28185415216245709616417059)
      ·
        refine ⟨42278122824368564424625589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28185415216245709616417059 42278122824368564424625589)
        ·
          refine ⟨3963574014784552914808649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42278122824368564424625589 3963574014784552914808649)
          ·
            refine ⟨2972680511088414686106487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3963574014784552914808649 2972680511088414686106487)
            ·
              refine ⟨4459020766632622029159731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2972680511088414686106487 4459020766632622029159731)
              ·
                refine ⟨6688531149948933043739597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4459020766632622029159731 6688531149948933043739597)
                ·
                  refine ⟨2508199181230849891402349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6688531149948933043739597 2508199181230849891402349)
                  ·
                    refine ⟨940574692961568709275881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2508199181230849891402349 940574692961568709275881)
                    ·
                      rfl

theorem cell22_2747644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_2747644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747644 prefixEnd_2747644 := by exact prefixLift 2747644
  have htrace : WordTrace (prefixWord ++ tailWord_2747644) baseStart_2747644 baseEnd_2747644 := by
    simpa [prefixWord, tailWord_2747644, baseEnd_2747644] using wordTrace_append hprefix tailTrace_2747644
  have hstable : (prefixWord ++ tailWord_2747644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747644).length < 2 ^ (prefixWord ++ tailWord_2747644).sum := by decide
  have hdescent : baseEnd_2747644 < baseStart_2747644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747751 : List Nat := [1, 1, 5, 1, 4, 2, 1, 2, 2, 3]
def baseStart_2747751 : Nat := 118140960795 + 2747751 * 2 ^ 59
def prefixEnd_2747751 : Nat := 4983230072969 + 3 ^ 40 * 2747751 * 2
def baseEnd_2747751 : Nat := 940611321248256096850553

theorem tailTrace_2747751 : CollatzResearch.WordTrace tailWord_2747751 prefixEnd_2747751 940611321248256096850553 := by
  unfold tailWord_2747751
  simp only [CollatzResearch.WordTrace]
  refine ⟨100218712268374880354739107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66812474845583253569826071 100218712268374880354739107)
  ·
    refine ⟨150328068402562320532108661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100218712268374880354739107 150328068402562320532108661)
    ·
      refine ⟨14093256412740217549885187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150328068402562320532108661 14093256412740217549885187)
      ·
        refine ⟨21139884619110326324827781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14093256412740217549885187 21139884619110326324827781)
        ·
          refine ⟨3963728366083186185905209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21139884619110326324827781 3963728366083186185905209)
          ·
            refine ⟨2972796274562389639428907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3963728366083186185905209 2972796274562389639428907)
            ·
              refine ⟨4459194411843584459143361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2972796274562389639428907 4459194411843584459143361)
              ·
                refine ⟨3344395808882688344357521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4459194411843584459143361 3344395808882688344357521)
                ·
                  refine ⟨2508296856662016258268141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3344395808882688344357521 2508296856662016258268141)
                  ·
                    refine ⟨940611321248256096850553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2508296856662016258268141 940611321248256096850553)
                    ·
                      rfl

theorem cell22_2747751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_2747751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747751 prefixEnd_2747751 := by exact prefixLift 2747751
  have htrace : WordTrace (prefixWord ++ tailWord_2747751) baseStart_2747751 baseEnd_2747751 := by
    simpa [prefixWord, tailWord_2747751, baseEnd_2747751] using wordTrace_append hprefix tailTrace_2747751
  have hstable : (prefixWord ++ tailWord_2747751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747751).length < 2 ^ (prefixWord ++ tailWord_2747751).sum := by decide
  have hdescent : baseEnd_2747751 < baseStart_2747751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747852 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 3, 5]
def baseStart_2747852 : Nat := 118140960795 + 2747852 * 2 ^ 59
def prefixEnd_2747852 : Nat := 4983230072969 + 3 ^ 40 * 2747852 * 2
def baseEnd_2747852 : Nat := 940645895612325500075243

theorem tailTrace_2747852 : CollatzResearch.WordTrace tailWord_2747852 prefixEnd_2747852 940645895612325500075243 := by
  unfold tailWord_2747852
  simp only [CollatzResearch.WordTrace]
  refine ⟨50111198020504487302082905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66814930694005983069443873 50111198020504487302082905)
  ·
    refine ⟨37583398515378365476562179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50111198020504487302082905 37583398515378365476562179)
    ·
      refine ⟨56375097773067548214843269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37583398515378365476562179 56375097773067548214843269)
      ·
        refine ⟨10570330832450165290283113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56375097773067548214843269 10570330832450165290283113)
        ·
          refine ⟨7927748124337623967712335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10570330832450165290283113 7927748124337623967712335)
          ·
            refine ⟨11891622186506435951568503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7927748124337623967712335 11891622186506435951568503)
            ·
              refine ⟨17837433279759653927352755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11891622186506435951568503 17837433279759653927352755)
              ·
                refine ⟨26756149919639480891029133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17837433279759653927352755 26756149919639480891029133)
                ·
                  refine ⟨10033556219864805334135925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26756149919639480891029133 10033556219864805334135925)
                  ·
                    refine ⟨940645895612325500075243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10033556219864805334135925 940645895612325500075243)
                    ·
                      rfl

theorem cell22_2747852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_2747852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747852 prefixEnd_2747852 := by exact prefixLift 2747852
  have htrace : WordTrace (prefixWord ++ tailWord_2747852) baseStart_2747852 baseEnd_2747852 := by
    simpa [prefixWord, tailWord_2747852, baseEnd_2747852] using wordTrace_append hprefix tailTrace_2747852
  have hstable : (prefixWord ++ tailWord_2747852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747852).length < 2 ^ (prefixWord ++ tailWord_2747852).sum := by decide
  have hdescent : baseEnd_2747852 < baseStart_2747852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747865 : List Nat := [1, 2, 1, 2, 4, 12]
def baseStart_2747865 : Nat := 118140960795 + 2747865 * 2 ^ 59
def prefixEnd_2747865 : Nat := 4983230072969 + 3 ^ 40 * 2747865 * 2
def baseEnd_2747865 : Nat := 11612967231827133327163

theorem tailTrace_2747865 : CollatzResearch.WordTrace tailWord_2747865 prefixEnd_2747865 11612967231827133327163 := by
  unfold tailWord_2747865
  simp only [CollatzResearch.WordTrace]
  refine ⟨100222870189961877824389049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66815246793307918549592699 100222870189961877824389049)
  ·
    refine ⟨75167152642471408368291787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100222870189961877824389049 75167152642471408368291787)
    ·
      refine ⟨112750728963707112552437681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75167152642471408368291787 112750728963707112552437681)
      ·
        refine ⟨84563046722780334414328261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112750728963707112552437681 84563046722780334414328261)
        ·
          refine ⟨15855571260521312702686549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84563046722780334414328261 15855571260521312702686549)
          ·
            refine ⟨11612967231827133327163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15855571260521312702686549 11612967231827133327163)
            ·
              rfl

theorem cell22_2747865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 12].length) (baseStart_2747865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747865 prefixEnd_2747865 := by exact prefixLift 2747865
  have htrace : WordTrace (prefixWord ++ tailWord_2747865) baseStart_2747865 baseEnd_2747865 := by
    simpa [prefixWord, tailWord_2747865, baseEnd_2747865] using wordTrace_append hprefix tailTrace_2747865
  have hstable : (prefixWord ++ tailWord_2747865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747865).length < 2 ^ (prefixWord ++ tailWord_2747865).sum := by decide
  have hdescent : baseEnd_2747865 < baseStart_2747865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747965 : List Nat := [1, 4, 1, 3, 3, 2, 1, 3, 1, 3]
def baseStart_2747965 : Nat := 118140960795 + 2747965 * 2 ^ 59
def prefixEnd_2747965 : Nat := 4983230072969 + 3 ^ 40 * 2747965 * 2
def baseEnd_2747965 : Nat := 940684577821630871999897

theorem tailTrace_2747965 : CollatzResearch.WordTrace tailWord_2747965 prefixEnd_2747965 940684577821630871999897 := by
  unfold tailWord_2747965
  simp only [CollatzResearch.WordTrace]
  refine ⟨100226517489599594903029349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66817678326399729935352899 100226517489599594903029349)
  ·
    refine ⟨18792472029299924044318003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100226517489599594903029349 18792472029299924044318003)
    ·
      refine ⟨28188708043949886066477005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18792472029299924044318003 28188708043949886066477005)
      ·
        refine ⟨10570765516481207274928877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28188708043949886066477005 10570765516481207274928877)
        ·
          refine ⟨3964037068680452728098329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10570765516481207274928877 3964037068680452728098329)
          ·
            refine ⟨2973027801510339546073747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3964037068680452728098329 2973027801510339546073747)
            ·
              refine ⟨4459541702265509319110621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2973027801510339546073747 4459541702265509319110621)
              ·
                refine ⟨1672328138349565994666483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4459541702265509319110621 1672328138349565994666483)
                ·
                  refine ⟨2508492207524348991999725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672328138349565994666483 2508492207524348991999725)
                  ·
                    refine ⟨940684577821630871999897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2508492207524348991999725 940684577821630871999897)
                    ·
                      rfl

theorem cell22_2747965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_2747965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747965 prefixEnd_2747965 := by exact prefixLift 2747965
  have htrace : WordTrace (prefixWord ++ tailWord_2747965) baseStart_2747965 baseEnd_2747965 := by
    simpa [prefixWord, tailWord_2747965, baseEnd_2747965] using wordTrace_append hprefix tailTrace_2747965
  have hstable : (prefixWord ++ tailWord_2747965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747965).length < 2 ^ (prefixWord ++ tailWord_2747965).sum := by decide
  have hdescent : baseEnd_2747965 < baseStart_2747965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748008 : List Nat := [2, 1, 4, 3, 1, 3, 1, 2, 1, 4]
def baseStart_2748008 : Nat := 118140960795 + 2748008 * 2 ^ 59
def prefixEnd_2748008 : Nat := 4983230072969 + 3 ^ 40 * 2748008 * 2
def baseEnd_2748008 : Nat := 940699297600393093174765

theorem tailTrace_2748008 : CollatzResearch.WordTrace tailWord_2748008 prefixEnd_2748008 940699297600393093174765 := by
  unfold tailWord_2748008
  simp only [CollatzResearch.WordTrace]
  refine ⟨50114042914221906623422339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66818723885629208831229785 50114042914221906623422339)
  ·
    refine ⟨75171064371332859935133509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50114042914221906623422339 75171064371332859935133509)
    ·
      refine ⟨14094574569624911237837533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75171064371332859935133509 14094574569624911237837533)
      ·
        refine ⟨5285465463609341714189075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14094574569624911237837533 5285465463609341714189075)
        ·
          refine ⟨7928198195414012571283613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5285465463609341714189075 7928198195414012571283613)
          ·
            refine ⟨2973074323280254714231355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7928198195414012571283613 2973074323280254714231355)
            ·
              refine ⟨4459611484920382071347033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2973074323280254714231355 4459611484920382071347033)
              ·
                refine ⟨3344708613690286553510275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4459611484920382071347033 3344708613690286553510275)
                ·
                  refine ⟨5017062920535429830265413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344708613690286553510275 5017062920535429830265413)
                  ·
                    refine ⟨940699297600393093174765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5017062920535429830265413 940699297600393093174765)
                    ·
                      rfl

theorem cell22_2748008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_2748008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748008 prefixEnd_2748008 := by exact prefixLift 2748008
  have htrace : WordTrace (prefixWord ++ tailWord_2748008) baseStart_2748008 baseEnd_2748008 := by
    simpa [prefixWord, tailWord_2748008, baseEnd_2748008] using wordTrace_append hprefix tailTrace_2748008
  have hstable : (prefixWord ++ tailWord_2748008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748008).length < 2 ^ (prefixWord ++ tailWord_2748008).sum := by decide
  have hdescent : baseEnd_2748008 < baseStart_2748008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748021 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2748021 : Nat := 118140960795 + 2748021 * 2 ^ 59
def prefixEnd_2748021 : Nat := 4983230072969 + 3 ^ 40 * 2748021 * 2
def baseEnd_2748021 : Nat := 940703747766065392599725

theorem tailTrace_2748021 : CollatzResearch.WordTrace tailWord_2748021 prefixEnd_2748021 940703747766065392599725 := by
  unfold tailWord_2748021
  simp only [CollatzResearch.WordTrace]
  refine ⟨100228559977396716467067917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66819039984931144311378611 100228559977396716467067917)
  ·
    refine ⟨37585709991523768675150469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100228559977396716467067917 37585709991523768675150469)
    ·
      refine ⟨7047320623410706626590713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37585709991523768675150469 7047320623410706626590713)
      ·
        refine ⟨5285490467558029969943035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7047320623410706626590713 5285490467558029969943035)
        ·
          refine ⟨7928235701337044954914553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5285490467558029969943035 7928235701337044954914553)
          ·
            refine ⟨5946176776002783716185915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7928235701337044954914553 5946176776002783716185915)
            ·
              refine ⟨8919265164004175574278873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5946176776002783716185915 8919265164004175574278873)
              ·
                refine ⟨6689448873003131680709155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8919265164004175574278873 6689448873003131680709155)
                ·
                  refine ⟨10034173309504697521063733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6689448873003131680709155 10034173309504697521063733)
                  ·
                    refine ⟨940703747766065392599725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10034173309504697521063733 940703747766065392599725)
                    ·
                      rfl

theorem cell22_2748021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2748021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748021 prefixEnd_2748021 := by exact prefixLift 2748021
  have htrace : WordTrace (prefixWord ++ tailWord_2748021) baseStart_2748021 baseEnd_2748021 := by
    simpa [prefixWord, tailWord_2748021, baseEnd_2748021] using wordTrace_append hprefix tailTrace_2748021
  have hstable : (prefixWord ++ tailWord_2748021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748021).length < 2 ^ (prefixWord ++ tailWord_2748021).sum := by decide
  have hdescent : baseEnd_2748021 < baseStart_2748021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748083 : List Nat := [1, 1, 1, 2, 3, 3, 4, 3, 1, 3]
def baseStart_2748083 : Nat := 118140960795 + 2748083 * 2 ^ 59
def prefixEnd_2748083 : Nat := 4983230072969 + 3 ^ 40 * 2748083 * 2
def baseEnd_2748083 : Nat := 940724971633117897549535

theorem tailTrace_2748083 : CollatzResearch.WordTrace tailWord_2748083 prefixEnd_2748083 940724971633117897549535 := by
  unfold tailWord_2748083
  simp only [CollatzResearch.WordTrace]
  refine ⟨100230821303172101055824903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66820547535448067370549935 100230821303172101055824903)
  ·
    refine ⟨150346231954758151583737355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100230821303172101055824903 150346231954758151583737355)
    ·
      refine ⟨225519347932137227375606033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150346231954758151583737355 225519347932137227375606033)
      ·
        refine ⟨169139510949102920531704525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225519347932137227375606033 169139510949102920531704525)
        ·
          refine ⟨63427316605913595199389197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169139510949102920531704525 63427316605913595199389197)
          ·
            refine ⟨23785243727217598199770949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63427316605913595199389197 23785243727217598199770949)
            ·
              refine ⟨4459733198853299662457053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23785243727217598199770949 4459733198853299662457053)
              ·
                refine ⟨1672399949569987373421395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4459733198853299662457053 1672399949569987373421395)
                ·
                  refine ⟨2508599924354981060132093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672399949569987373421395 2508599924354981060132093)
                  ·
                    refine ⟨940724971633117897549535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2508599924354981060132093 940724971633117897549535)
                    ·
                      rfl

theorem cell22_2748083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 1, 3].length) (baseStart_2748083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748083 prefixEnd_2748083 := by exact prefixLift 2748083
  have htrace : WordTrace (prefixWord ++ tailWord_2748083) baseStart_2748083 baseEnd_2748083 := by
    simpa [prefixWord, tailWord_2748083, baseEnd_2748083] using wordTrace_append hprefix tailTrace_2748083
  have hstable : (prefixWord ++ tailWord_2748083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748083).length < 2 ^ (prefixWord ++ tailWord_2748083).sum := by decide
  have hdescent : baseEnd_2748083 < baseStart_2748083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748139 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 1, 5]
def baseStart_2748139 : Nat := 118140960795 + 2748139 * 2 ^ 59
def prefixEnd_2748139 : Nat := 4983230072969 + 3 ^ 40 * 2748139 * 2
def baseEnd_2748139 : Nat := 940744141577552418149363

theorem tailTrace_2748139 : CollatzResearch.WordTrace tailWord_2748139 prefixEnd_2748139 940744141577552418149363 := by
  unfold tailWord_2748139
  simp only [CollatzResearch.WordTrace]
  refine ⟨100232863790969222619863471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66821909193979481746575647 100232863790969222619863471)
  ·
    refine ⟨150349295686453833929795207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100232863790969222619863471 150349295686453833929795207)
    ·
      refine ⟨225523943529680750894692811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150349295686453833929795207 225523943529680750894692811)
      ·
        refine ⟨338285915294521126342039217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225523943529680750894692811 338285915294521126342039217)
        ·
          refine ⟨253714436470890844756529413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338285915294521126342039217 253714436470890844756529413)
          ·
            refine ⟨47571456838292033391849265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 253714436470890844756529413 47571456838292033391849265)
            ·
              refine ⟨35678592628719025043886949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47571456838292033391849265 35678592628719025043886949)
              ·
                refine ⟨6689736117884817195728803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35678592628719025043886949 6689736117884817195728803)
                ·
                  refine ⟨10034604176827225793593205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6689736117884817195728803 10034604176827225793593205)
                  ·
                    refine ⟨940744141577552418149363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10034604176827225793593205 940744141577552418149363)
                    ·
                      rfl

theorem cell22_2748139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 5].length) (baseStart_2748139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748139 prefixEnd_2748139 := by exact prefixLift 2748139
  have htrace : WordTrace (prefixWord ++ tailWord_2748139) baseStart_2748139 baseEnd_2748139 := by
    simpa [prefixWord, tailWord_2748139, baseEnd_2748139] using wordTrace_append hprefix tailTrace_2748139
  have hstable : (prefixWord ++ tailWord_2748139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748139).length < 2 ^ (prefixWord ++ tailWord_2748139).sum := by decide
  have hdescent : baseEnd_2748139 < baseStart_2748139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748156 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 4, 3]
def baseStart_2748156 : Nat := 118140960795 + 2748156 * 2 ^ 59
def prefixEnd_2748156 : Nat := 4983230072969 + 3 ^ 40 * 2748156 * 2
def baseEnd_2748156 : Nat := 940749961024970040474311

theorem tailTrace_2748156 : CollatzResearch.WordTrace tailWord_2748156 prefixEnd_2748156 940749961024970040474311 := by
  unfold tailWord_2748156
  simp only [CollatzResearch.WordTrace]
  refine ⟨50116741915953817261616161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66822322554605089682154881 50116741915953817261616161)
  ·
    refine ⟨37587556436965362946212121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50116741915953817261616161 37587556436965362946212121)
    ·
      refine ⟨28190667327724022209659091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37587556436965362946212121 28190667327724022209659091)
      ·
        refine ⟨42286000991586033314488637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28190667327724022209659091 42286000991586033314488637)
        ·
          refine ⟨15857250371844762492933239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42286000991586033314488637 15857250371844762492933239)
          ·
            refine ⟨23785875557767143739399859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15857250371844762492933239 23785875557767143739399859)
            ·
              refine ⟨35678813336650715609099789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23785875557767143739399859 35678813336650715609099789)
              ·
                refine ⟨13379555001244018353412421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35678813336650715609099789 13379555001244018353412421)
                ·
                  refine ⟨2508666562733253441264829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13379555001244018353412421 2508666562733253441264829)
                  ·
                    refine ⟨940749961024970040474311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2508666562733253441264829 940749961024970040474311)
                    ·
                      rfl

theorem cell22_2748156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_2748156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748156 prefixEnd_2748156 := by exact prefixLift 2748156
  have htrace : WordTrace (prefixWord ++ tailWord_2748156) baseStart_2748156 baseEnd_2748156 := by
    simpa [prefixWord, tailWord_2748156, baseEnd_2748156] using wordTrace_append hprefix tailTrace_2748156
  have hstable : (prefixWord ++ tailWord_2748156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748156).length < 2 ^ (prefixWord ++ tailWord_2748156).sum := by decide
  have hdescent : baseEnd_2748156 < baseStart_2748156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748184 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 2, 7]
def baseStart_2748184 : Nat := 118140960795 + 2748184 * 2 ^ 59
def prefixEnd_2748184 : Nat := 4983230072969 + 3 ^ 40 * 2748184 * 2
def baseEnd_2748184 : Nat := 940759545997187300774225

theorem tailTrace_2748184 : CollatzResearch.WordTrace tailWord_2748184 prefixEnd_2748184 940759545997187300774225 := by
  unfold tailWord_2748184
  simp only [CollatzResearch.WordTrace]
  refine ⟨50117252537903097652625803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66823003383870796870167737 50117252537903097652625803)
  ·
    refine ⟨75175878806854646478938705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50117252537903097652625803 75175878806854646478938705)
    ·
      refine ⟨56381909105140984859204029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75175878806854646478938705 56381909105140984859204029)
      ·
        refine ⟨21143215914427869322201511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56381909105140984859204029 21143215914427869322201511)
        ·
          refine ⟨31714823871641803983302267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21143215914427869322201511 31714823871641803983302267)
          ·
            refine ⟨47572235807462705974953401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31714823871641803983302267 47572235807462705974953401)
            ·
              refine ⟨35679176855597029481215051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47572235807462705974953401 35679176855597029481215051)
              ·
                refine ⟨53518765283395544221822577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35679176855597029481215051 53518765283395544221822577)
                ·
                  refine ⟨40139073962546658166366933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53518765283395544221822577 40139073962546658166366933)
                  ·
                    refine ⟨940759545997187300774225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40139073962546658166366933 940759545997187300774225)
                    ·
                      rfl

theorem cell22_2748184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_2748184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748184 prefixEnd_2748184 := by exact prefixLift 2748184
  have htrace : WordTrace (prefixWord ++ tailWord_2748184) baseStart_2748184 baseEnd_2748184 := by
    simpa [prefixWord, tailWord_2748184, baseEnd_2748184] using wordTrace_append hprefix tailTrace_2748184
  have hstable : (prefixWord ++ tailWord_2748184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748184).length < 2 ^ (prefixWord ++ tailWord_2748184).sum := by decide
  have hdescent : baseEnd_2748184 < baseStart_2748184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748231 : List Nat := [1, 1, 4, 1, 2, 1, 4, 3, 5]
def baseStart_2748231 : Nat := 118140960795 + 2748231 * 2 ^ 59
def prefixEnd_2748231 : Nat := 4983230072969 + 3 ^ 40 * 2748231 * 2
def baseEnd_2748231 : Nat := 313591878352564948283027

theorem tailTrace_2748231 : CollatzResearch.WordTrace tailWord_2748231 prefixEnd_2748231 313591878352564948283027 := by
  unfold tailWord_2748231
  simp only [CollatzResearch.WordTrace]
  refine ⟨100236219306635922332212547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66824146204423948221475031 100236219306635922332212547)
  ·
    refine ⟨150354328959953883498318821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100236219306635922332212547 150354328959953883498318821)
    ·
      refine ⟨28191436679991353155934779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150354328959953883498318821 28191436679991353155934779)
      ·
        refine ⟨42287155019987029733902169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28191436679991353155934779 42287155019987029733902169)
        ·
          refine ⟨31715366264990272300426627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42287155019987029733902169 31715366264990272300426627)
          ·
            refine ⟨47573049397485408450639941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31715366264990272300426627 47573049397485408450639941)
            ·
              refine ⟨8919946762028514084494989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47573049397485408450639941 8919946762028514084494989)
              ·
                refine ⟨3344980035760692781685621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8919946762028514084494989 3344980035760692781685621)
                ·
                  refine ⟨313591878352564948283027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3344980035760692781685621 313591878352564948283027)
                  ·
                    rfl

theorem cell22_2748231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 5].length) (baseStart_2748231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748231 prefixEnd_2748231 := by exact prefixLift 2748231
  have htrace : WordTrace (prefixWord ++ tailWord_2748231) baseStart_2748231 baseEnd_2748231 := by
    simpa [prefixWord, tailWord_2748231, baseEnd_2748231] using wordTrace_append hprefix tailTrace_2748231
  have hstable : (prefixWord ++ tailWord_2748231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748231).length < 2 ^ (prefixWord ++ tailWord_2748231).sum := by decide
  have hdescent : baseEnd_2748231 < baseStart_2748231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748295 : List Nat := [1, 1, 4, 2, 4, 1, 2, 2, 1, 4]
def baseStart_2748295 : Nat := 118140960795 + 2748295 * 2 ^ 59
def prefixEnd_2748295 : Nat := 4983230072969 + 3 ^ 40 * 2748295 * 2
def baseEnd_2748295 : Nat := 940797543565620011248885

theorem tailTrace_2748295 : CollatzResearch.WordTrace tailWord_2748295 prefixEnd_2748295 940797543565620011248885 := by
  unfold tailWord_2748295
  simp only [CollatzResearch.WordTrace]
  refine ⟨100238553578404061262542339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66825702385602707508361559 100238553578404061262542339)
  ·
    refine ⟨150357830367606091893813509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100238553578404061262542339 150357830367606091893813509)
    ·
      refine ⟨28192093193926142230090033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150357830367606091893813509 28192093193926142230090033)
      ·
        refine ⟨21144069895444606672567525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28192093193926142230090033 21144069895444606672567525)
        ·
          refine ⟨3964513105395863751106411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21144069895444606672567525 3964513105395863751106411)
          ·
            refine ⟨5946769658093795626659617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3964513105395863751106411 5946769658093795626659617)
            ·
              refine ⟨4460077243570346719994713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5946769658093795626659617 4460077243570346719994713)
              ·
                refine ⟨3345057932677760039996035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4460077243570346719994713 3345057932677760039996035)
                ·
                  refine ⟨5017586899016640059994053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345057932677760039996035 5017586899016640059994053)
                  ·
                    refine ⟨940797543565620011248885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5017586899016640059994053 940797543565620011248885)
                    ·
                      rfl

theorem cell22_2748295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_2748295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748295 prefixEnd_2748295 := by exact prefixLift 2748295
  have htrace : WordTrace (prefixWord ++ tailWord_2748295) baseStart_2748295 baseEnd_2748295 := by
    simpa [prefixWord, tailWord_2748295, baseEnd_2748295] using wordTrace_append hprefix tailTrace_2748295
  have hstable : (prefixWord ++ tailWord_2748295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748295).length < 2 ^ (prefixWord ++ tailWord_2748295).sum := by decide
  have hdescent : baseEnd_2748295 < baseStart_2748295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748327 : List Nat := [1, 1, 6, 1, 2, 2, 3, 2, 4]
def baseStart_2748327 : Nat := 118140960795 + 2748327 * 2 ^ 59
def prefixEnd_2748327 : Nat := 4983230072969 + 3 ^ 40 * 2748327 * 2
def baseEnd_2748327 : Nat := 313602832606527531482929

theorem tailTrace_2748327 : CollatzResearch.WordTrace tailWord_2748327 prefixEnd_2748327 313602832606527531482929 := by
  unfold tailWord_2748327
  simp only [CollatzResearch.WordTrace]
  refine ⟨100239720714288130727707235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66826480476192087151804823 100239720714288130727707235)
  ·
    refine ⟨150359581071432196091560853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100239720714288130727707235 150359581071432196091560853)
    ·
      refine ⟨7048105362723384191791915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 150359581071432196091560853 7048105362723384191791915)
      ·
        refine ⟨10572158044085076287687873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7048105362723384191791915 10572158044085076287687873)
        ·
          refine ⟨7929118533063807215765905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10572158044085076287687873 7929118533063807215765905)
          ·
            refine ⟨5946838899797855411824429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7929118533063807215765905 5946838899797855411824429)
            ·
              refine ⟨2230064587424195779434161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5946838899797855411824429 2230064587424195779434161)
              ·
                refine ⟨1672548440568146834575621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2230064587424195779434161 1672548440568146834575621)
                ·
                  refine ⟨313602832606527531482929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1672548440568146834575621 313602832606527531482929)
                  ·
                    rfl

theorem cell22_2748327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 4].length) (baseStart_2748327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748327 prefixEnd_2748327 := by exact prefixLift 2748327
  have htrace : WordTrace (prefixWord ++ tailWord_2748327) baseStart_2748327 baseEnd_2748327 := by
    simpa [prefixWord, tailWord_2748327, baseEnd_2748327] using wordTrace_append hprefix tailTrace_2748327
  have hstable : (prefixWord ++ tailWord_2748327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748327).length < 2 ^ (prefixWord ++ tailWord_2748327).sum := by decide
  have hdescent : baseEnd_2748327 < baseStart_2748327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748383 : List Nat := [1, 1, 2, 3, 4, 1, 1, 4, 5]
def baseStart_2748383 : Nat := 118140960795 + 2748383 * 2 ^ 59
def prefixEnd_2748383 : Nat := 4983230072969 + 3 ^ 40 * 2748383 * 2
def baseEnd_2748383 : Nat := 313609222588005705016205

theorem tailTrace_2748383 : CollatzResearch.WordTrace tailWord_2748383 prefixEnd_2748383 313609222588005705016205 := by
  unfold tailWord_2748383
  simp only [CollatzResearch.WordTrace]
  refine ⟨100241763202085252291745803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66827842134723501527830535 100241763202085252291745803)
  ·
    refine ⟨150362644803127878437618705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100241763202085252291745803 150362644803127878437618705)
    ·
      refine ⟨112771983602345908828214029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150362644803127878437618705 112771983602345908828214029)
      ·
        refine ⟨42289493850879715810580261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112771983602345908828214029 42289493850879715810580261)
        ·
          refine ⟨7929280097039946714483799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42289493850879715810580261 7929280097039946714483799)
          ·
            refine ⟨11893920145559920071725699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7929280097039946714483799 11893920145559920071725699)
            ·
              refine ⟨17840880218339880107588549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11893920145559920071725699 17840880218339880107588549)
              ·
                refine ⟨3345165040938727520172853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17840880218339880107588549 3345165040938727520172853)
                ·
                  refine ⟨313609222588005705016205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3345165040938727520172853 313609222588005705016205)
                  ·
                    rfl

theorem cell22_2748383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 5].length) (baseStart_2748383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748383 prefixEnd_2748383 := by exact prefixLift 2748383
  have htrace : WordTrace (prefixWord ++ tailWord_2748383) baseStart_2748383 baseEnd_2748383 := by
    simpa [prefixWord, tailWord_2748383, baseEnd_2748383] using wordTrace_append hprefix tailTrace_2748383
  have hstable : (prefixWord ++ tailWord_2748383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748383).length < 2 ^ (prefixWord ++ tailWord_2748383).sum := by decide
  have hdescent : baseEnd_2748383 < baseStart_2748383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748387 : List Nat := [1, 1, 1, 6, 1, 3, 1, 4, 1, 3]
def baseStart_2748387 : Nat := 118140960795 + 2748387 * 2 ^ 59
def prefixEnd_2748387 : Nat := 4983230072969 + 3 ^ 40 * 2748387 * 2
def baseEnd_2748387 : Nat := 940829037045762437948603

theorem tailTrace_2748387 : CollatzResearch.WordTrace tailWord_2748387 prefixEnd_2748387 940829037045762437948603 := by
  unfold tailWord_2748387
  simp only [CollatzResearch.WordTrace]
  refine ⟨100241909094070760974891415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66827939396047173983260943 100241909094070760974891415)
  ·
    refine ⟨150362863641106141462337123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100241909094070760974891415 150362863641106141462337123)
    ·
      refine ⟨225544295461659212193505685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150362863641106141462337123 225544295461659212193505685)
      ·
        refine ⟨10572388849765275571570579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 225544295461659212193505685 10572388849765275571570579)
        ·
          refine ⟨15858583274647913357355869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10572388849765275571570579 15858583274647913357355869)
          ·
            refine ⟨5946968727992967509008451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15858583274647913357355869 5946968727992967509008451)
            ·
              refine ⟨8920453091989451263512677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5946968727992967509008451 8920453091989451263512677)
              ·
                refine ⟨1672584954748022111908627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8920453091989451263512677 1672584954748022111908627)
                ·
                  refine ⟨2508877432122033167862941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672584954748022111908627 2508877432122033167862941)
                  ·
                    refine ⟨940829037045762437948603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2508877432122033167862941 940829037045762437948603)
                    ·
                      rfl

theorem cell22_2748387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 1, 3].length) (baseStart_2748387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748387 prefixEnd_2748387 := by exact prefixLift 2748387
  have htrace : WordTrace (prefixWord ++ tailWord_2748387) baseStart_2748387 baseEnd_2748387 := by
    simpa [prefixWord, tailWord_2748387, baseEnd_2748387] using wordTrace_append hprefix tailTrace_2748387
  have hstable : (prefixWord ++ tailWord_2748387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748387).length < 2 ^ (prefixWord ++ tailWord_2748387).sum := by decide
  have hdescent : baseEnd_2748387 < baseStart_2748387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748398 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_2748398 : Nat := 118140960795 + 2748398 * 2 ^ 59
def prefixEnd_2748398 : Nat := 4983230072969 + 3 ^ 40 * 2748398 * 2
def baseEnd_2748398 : Nat := 940832802570562075923569

theorem tailTrace_2748398 : CollatzResearch.WordTrace tailWord_2748398 prefixEnd_2748398 940832802570562075923569 := by
  unfold tailWord_2748398
  simp only [CollatzResearch.WordTrace]
  refine ⟨12530288787128863731692731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66828206864687273235694565 12530288787128863731692731)
  ·
    refine ⟨18795433180693295597539097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12530288787128863731692731 18795433180693295597539097)
    ·
      refine ⟨14096574885519971698154323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18795433180693295597539097 14096574885519971698154323)
      ·
        refine ⟨21144862328279957547231485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14096574885519971698154323 21144862328279957547231485)
        ·
          refine ⟨7929323373104984080211807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21144862328279957547231485 7929323373104984080211807)
          ·
            refine ⟨11893985059657476120317711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7929323373104984080211807 11893985059657476120317711)
            ·
              refine ⟨17840977589486214180476567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11893985059657476120317711 17840977589486214180476567)
              ·
                refine ⟨26761466384229321270714851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17840977589486214180476567 26761466384229321270714851)
                ·
                  refine ⟨40142199576343981906072277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26761466384229321270714851 40142199576343981906072277)
                  ·
                    refine ⟨940832802570562075923569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40142199576343981906072277 940832802570562075923569)
                    ·
                      rfl

theorem cell22_2748398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_2748398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748398 prefixEnd_2748398 := by exact prefixLift 2748398
  have htrace : WordTrace (prefixWord ++ tailWord_2748398) baseStart_2748398 baseEnd_2748398 := by
    simpa [prefixWord, tailWord_2748398, baseEnd_2748398] using wordTrace_append hprefix tailTrace_2748398
  have hstable : (prefixWord ++ tailWord_2748398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748398).length < 2 ^ (prefixWord ++ tailWord_2748398).sum := by decide
  have hdescent : baseEnd_2748398 < baseStart_2748398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748411 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 8]
def baseStart_2748411 : Nat := 118140960795 + 2748411 * 2 ^ 59
def prefixEnd_2748411 : Nat := 4983230072969 + 3 ^ 40 * 2748411 * 2
def baseEnd_2748411 : Nat := 313612417578744791782843

theorem tailTrace_2748411 : CollatzResearch.WordTrace tailWord_2748411 prefixEnd_2748411 313612417578744791782843 := by
  unfold tailWord_2748411
  simp only [CollatzResearch.WordTrace]
  refine ⟨100242784445983813073765087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66828522963989208715843391 100242784445983813073765087)
  ·
    refine ⟨150364176668975719610647631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100242784445983813073765087 150364176668975719610647631)
    ·
      refine ⟨225546265003463579415971447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150364176668975719610647631 225546265003463579415971447)
      ·
        refine ⟨338319397505195369123957171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225546265003463579415971447 338319397505195369123957171)
        ·
          refine ⟨507479096257793053685935757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338319397505195369123957171 507479096257793053685935757)
          ·
            refine ⟨190304661096672395132225909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 507479096257793053685935757 190304661096672395132225909)
            ·
              refine ⟨17841061977813037043646179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 190304661096672395132225909 17841061977813037043646179)
              ·
                refine ⟨26761592966719555565469269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17841061977813037043646179 26761592966719555565469269)
                ·
                  refine ⟨313612417578744791782843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26761592966719555565469269 313612417578744791782843)
                  ·
                    rfl

theorem cell22_2748411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 8].length) (baseStart_2748411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748411 prefixEnd_2748411 := by exact prefixLift 2748411
  have htrace : WordTrace (prefixWord ++ tailWord_2748411) baseStart_2748411 baseEnd_2748411 := by
    simpa [prefixWord, tailWord_2748411, baseEnd_2748411] using wordTrace_append hprefix tailTrace_2748411
  have hstable : (prefixWord ++ tailWord_2748411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748411).length < 2 ^ (prefixWord ++ tailWord_2748411).sum := by decide
  have hdescent : baseEnd_2748411 < baseStart_2748411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748413 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_2748413 : Nat := 118140960795 + 2748413 * 2 ^ 59
def prefixEnd_2748413 : Nat := 4983230072969 + 3 ^ 40 * 2748413 * 2
def baseEnd_2748413 : Nat := 940837937377107036798523

theorem tailTrace_2748413 : CollatzResearch.WordTrace tailWord_2748413 prefixEnd_2748413 940837937377107036798523 := by
  unfold tailWord_2748413
  simp only [CollatzResearch.WordTrace]
  refine ⟨100242857391976567415337893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66828571594651044943558595 100242857391976567415337893)
  ·
    refine ⟨18795535760995606390375855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100242857391976567415337893 18795535760995606390375855)
    ·
      refine ⟨28193303641493409585563783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18795535760995606390375855 28193303641493409585563783)
      ·
        refine ⟨42289955462240114378345675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28193303641493409585563783 42289955462240114378345675)
        ·
          refine ⟨63434933193360171567518513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42289955462240114378345675 63434933193360171567518513)
          ·
            refine ⟨47576199895020128675638885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63434933193360171567518513 47576199895020128675638885)
            ·
              refine ⟨8920537480316274126682291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47576199895020128675638885 8920537480316274126682291)
              ·
                refine ⟨13380806220474411190023437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8920537480316274126682291 13380806220474411190023437)
                ·
                  refine ⟨5017802332677904196258789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13380806220474411190023437 5017802332677904196258789)
                  ·
                    refine ⟨940837937377107036798523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5017802332677904196258789 940837937377107036798523)
                    ·
                      rfl

theorem cell22_2748413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_2748413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748413 prefixEnd_2748413 := by exact prefixLift 2748413
  have htrace : WordTrace (prefixWord ++ tailWord_2748413) baseStart_2748413 baseEnd_2748413 := by
    simpa [prefixWord, tailWord_2748413, baseEnd_2748413] using wordTrace_append hprefix tailTrace_2748413
  have hstable : (prefixWord ++ tailWord_2748413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748413).length < 2 ^ (prefixWord ++ tailWord_2748413).sum := by decide
  have hdescent : baseEnd_2748413 < baseStart_2748413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748430 : List Nat := [4, 1, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_2748430 : Nat := 118140960795 + 2748430 * 2 ^ 59
def prefixEnd_2748430 : Nat := 4983230072969 + 3 ^ 40 * 2748430 * 2
def baseEnd_2748430 : Nat := 940843756824524659123471

theorem tailTrace_2748430 : CollatzResearch.WordTrace tailWord_2748430 prefixEnd_2748430 940843756824524659123471 := by
  unfold tailWord_2748430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12530434679114372414838343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66828984955276652879137829 12530434679114372414838343)
  ·
    refine ⟨18795652018671558622257515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12530434679114372414838343 18795652018671558622257515)
    ·
      refine ⟨28193478028007337933386273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18795652018671558622257515 28193478028007337933386273)
      ·
        refine ⟨21145108521005503450039705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28193478028007337933386273 21145108521005503450039705)
        ·
          refine ⟨15858831390754127587529779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21145108521005503450039705 15858831390754127587529779)
          ·
            refine ⟨23788247086131191381294669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15858831390754127587529779 23788247086131191381294669)
            ·
              refine ⟨8920592657299196767985501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23788247086131191381294669 8920592657299196767985501)
              ·
                refine ⟨3345222246487198787994563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8920592657299196767985501 3345222246487198787994563)
                ·
                  refine ⟨5017833369730798181991845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345222246487198787994563 5017833369730798181991845)
                  ·
                    refine ⟨940843756824524659123471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5017833369730798181991845 940843756824524659123471)
                    ·
                      rfl

theorem cell22_2748430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_2748430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748430 prefixEnd_2748430 := by exact prefixLift 2748430
  have htrace : WordTrace (prefixWord ++ tailWord_2748430) baseStart_2748430 baseEnd_2748430 := by
    simpa [prefixWord, tailWord_2748430, baseEnd_2748430] using wordTrace_append hprefix tailTrace_2748430
  have hstable : (prefixWord ++ tailWord_2748430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748430).length < 2 ^ (prefixWord ++ tailWord_2748430).sum := by decide
  have hdescent : baseEnd_2748430 < baseStart_2748430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748445 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 6]
def baseStart_2748445 : Nat := 118140960795 + 2748445 * 2 ^ 59
def prefixEnd_2748445 : Nat := 4983230072969 + 3 ^ 40 * 2748445 * 2
def baseEnd_2748445 : Nat := 313616297210356539999475

theorem tailTrace_2748445 : CollatzResearch.WordTrace tailWord_2748445 prefixEnd_2748445 313616297210356539999475 := by
  unfold tailWord_2748445
  simp only [CollatzResearch.WordTrace]
  refine ⟨100244024527860636880502789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66829349685240424587001859 100244024527860636880502789)
  ·
    refine ⟨18795754598973869415094273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100244024527860636880502789 18795754598973869415094273)
    ·
      refine ⟨14096815949230402061320705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18795754598973869415094273 14096815949230402061320705)
      ·
        refine ⟨10572611961922801545990529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14096815949230402061320705 10572611961922801545990529)
        ·
          refine ⟨7929458971442101159492897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10572611961922801545990529 7929458971442101159492897)
          ·
            refine ⟨5947094228581575869619673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7929458971442101159492897 5947094228581575869619673)
            ·
              refine ⟨4460320671436181902214755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5947094228581575869619673 4460320671436181902214755)
              ·
                refine ⟨6690481007154272853322133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4460320671436181902214755 6690481007154272853322133)
                ·
                  refine ⟨313616297210356539999475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6690481007154272853322133 313616297210356539999475)
                  ·
                    rfl

theorem cell22_2748445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_2748445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748445 prefixEnd_2748445 := by exact prefixLift 2748445
  have htrace : WordTrace (prefixWord ++ tailWord_2748445) baseStart_2748445 baseEnd_2748445 := by
    simpa [prefixWord, tailWord_2748445, baseEnd_2748445] using wordTrace_append hprefix tailTrace_2748445
  have hstable : (prefixWord ++ tailWord_2748445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748445).length < 2 ^ (prefixWord ++ tailWord_2748445).sum := by decide
  have hdescent : baseEnd_2748445 < baseStart_2748445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748552 : List Nat := [2, 1, 3, 4, 1, 2, 2, 2, 5]
def baseStart_2748552 : Nat := 118140960795 + 2748552 * 2 ^ 59
def prefixEnd_2748552 : Nat := 4983230072969 + 3 ^ 40 * 2748552 * 2
def baseEnd_2748552 : Nat := 313628506639252335857699

theorem tailTrace_2748552 : CollatzResearch.WordTrace tailWord_2748552 prefixEnd_2748552 313628506639252335857699 := by
  unfold tailWord_2748552
  simp only [CollatzResearch.WordTrace]
  refine ⟨50123963569236497077323955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66831951425648662769765273 50123963569236497077323955)
  ·
    refine ⟨75185945353854745615985933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50123963569236497077323955 75185945353854745615985933)
    ·
      refine ⟨28194729507695529605994725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75185945353854745615985933 28194729507695529605994725)
      ·
        refine ⟨5286511782692911801124011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28194729507695529605994725 5286511782692911801124011)
        ·
          refine ⟨7929767674039367701686017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5286511782692911801124011 7929767674039367701686017)
          ·
            refine ⟨5947325755529525776264513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7929767674039367701686017 5947325755529525776264513)
            ·
              refine ⟨4460494316647144332198385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5947325755529525776264513 4460494316647144332198385)
              ·
                refine ⟨3345370737485358249148789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4460494316647144332198385 3345370737485358249148789)
                ·
                  refine ⟨313628506639252335857699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3345370737485358249148789 313628506639252335857699)
                  ·
                    rfl

theorem cell22_2748552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 5].length) (baseStart_2748552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748552 prefixEnd_2748552 := by exact prefixLift 2748552
  have htrace : WordTrace (prefixWord ++ tailWord_2748552) baseStart_2748552 baseEnd_2748552 := by
    simpa [prefixWord, tailWord_2748552, baseEnd_2748552] using wordTrace_append hprefix tailTrace_2748552
  have hstable : (prefixWord ++ tailWord_2748552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748552).length < 2 ^ (prefixWord ++ tailWord_2748552).sum := by decide
  have hdescent : baseEnd_2748552 < baseStart_2748552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748563 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 6]
def baseStart_2748563 : Nat := 118140960795 + 2748563 * 2 ^ 59
def prefixEnd_2748563 : Nat := 4983230072969 + 3 ^ 40 * 2748563 * 2
def baseEnd_2748563 : Nat := 313629761814185548516021

theorem tailTrace_2748563 : CollatzResearch.WordTrace tailWord_2748563 prefixEnd_2748563 313629761814185548516021 := by
  unfold tailWord_2748563
  simp only [CollatzResearch.WordTrace]
  refine ⟨100248328341433143033298343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66832218894288762022198895 100248328341433143033298343)
  ·
    refine ⟨150372492512149714549947515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100248328341433143033298343 150372492512149714549947515)
    ·
      refine ⟨225558738768224571824921273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150372492512149714549947515 225558738768224571824921273)
      ·
        refine ⟨169169054076168428868690955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225558738768224571824921273 169169054076168428868690955)
        ·
          refine ⟨253753581114252643303036433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169169054076168428868690955 253753581114252643303036433)
          ·
            refine ⟨190315185835689482477277325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253753581114252643303036433 190315185835689482477277325)
            ·
              refine ⟨71368194688383555928978997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190315185835689482477277325 71368194688383555928978997)
              ·
                refine ⟨6690768252035958368341781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71368194688383555928978997 6690768252035958368341781)
                ·
                  refine ⟨313629761814185548516021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6690768252035958368341781 313629761814185548516021)
                  ·
                    rfl

theorem cell22_2748563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 6].length) (baseStart_2748563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748563 prefixEnd_2748563 := by exact prefixLift 2748563
  have htrace : WordTrace (prefixWord ++ tailWord_2748563) baseStart_2748563 baseEnd_2748563 := by
    simpa [prefixWord, tailWord_2748563, baseEnd_2748563] using wordTrace_append hprefix tailTrace_2748563
  have hstable : (prefixWord ++ tailWord_2748563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748563).length < 2 ^ (prefixWord ++ tailWord_2748563).sum := by decide
  have hdescent : baseEnd_2748563 < baseStart_2748563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748595 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 4, 3]
def baseStart_2748595 : Nat := 118140960795 + 2748595 * 2 ^ 59
def prefixEnd_2748595 : Nat := 4983230072969 + 3 ^ 40 * 2748595 * 2
def baseEnd_2748595 : Nat := 940900239696519228747965

theorem tailTrace_2748595 : CollatzResearch.WordTrace tailWord_2748595 prefixEnd_2748595 940900239696519228747965 := by
  unfold tailWord_2748595
  simp only [CollatzResearch.WordTrace]
  refine ⟨100249495477317212498463239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66832996984878141665642159 100249495477317212498463239)
  ·
    refine ⟨150374243215975818747694859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100249495477317212498463239 150374243215975818747694859)
    ·
      refine ⟨225561364823963728121542289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150374243215975818747694859 225561364823963728121542289)
      ·
        refine ⟨169171023617972796091156717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225561364823963728121542289 169171023617972796091156717)
        ·
          refine ⟨63439133856739798534183769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169171023617972796091156717 63439133856739798534183769)
          ·
            refine ⟨47579350392554848900637827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63439133856739798534183769 47579350392554848900637827)
            ·
              refine ⟨71369025588832273350956741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47579350392554848900637827 71369025588832273350956741)
              ·
                refine ⟨13381692297906051253304389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71369025588832273350956741 13381692297906051253304389)
                ·
                  refine ⟨2509067305857384609994573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13381692297906051253304389 2509067305857384609994573)
                  ·
                    refine ⟨940900239696519228747965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2509067305857384609994573 940900239696519228747965)
                    ·
                      rfl

theorem cell22_2748595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 3].length) (baseStart_2748595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748595 prefixEnd_2748595 := by exact prefixLift 2748595
  have htrace : WordTrace (prefixWord ++ tailWord_2748595) baseStart_2748595 baseEnd_2748595 := by
    simpa [prefixWord, tailWord_2748595, baseEnd_2748595] using wordTrace_append hprefix tailTrace_2748595
  have hstable : (prefixWord ++ tailWord_2748595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748595).length < 2 ^ (prefixWord ++ tailWord_2748595).sum := by decide
  have hdescent : baseEnd_2748595 < baseStart_2748595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748599 : List Nat := [1, 1, 3, 1, 4, 4, 2, 1, 1, 4]
def baseStart_2748599 : Nat := 118140960795 + 2748599 * 2 ^ 59
def prefixEnd_2748599 : Nat := 4983230072969 + 3 ^ 40 * 2748599 * 2
def baseEnd_2748599 : Nat := 940901608978264551647953

theorem tailTrace_2748599 : CollatzResearch.WordTrace tailWord_2748599 prefixEnd_2748599 940901608978264551647953 := by
  unfold tailWord_2748599
  simp only [CollatzResearch.WordTrace]
  refine ⟨100249641369302721181608851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66833094246201814121072567 100249641369302721181608851)
  ·
    refine ⟨150374462053954081772413277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100249641369302721181608851 150374462053954081772413277)
    ·
      refine ⟨56390423270232780664654979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150374462053954081772413277 56390423270232780664654979)
      ·
        refine ⟨84585634905349170996982469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56390423270232780664654979 84585634905349170996982469)
        ·
          refine ⟨15859806544752969561934213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84585634905349170996982469 15859806544752969561934213)
          ·
            refine ⟨2973713727141181792862665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15859806544752969561934213 2973713727141181792862665)
            ·
              refine ⟨2230285295355886344646999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2973713727141181792862665 2230285295355886344646999)
              ·
                refine ⟨3345427943033829516970499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230285295355886344646999 3345427943033829516970499)
                ·
                  refine ⟨5018141914550744275455749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345427943033829516970499 5018141914550744275455749)
                  ·
                    refine ⟨940901608978264551647953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5018141914550744275455749 940901608978264551647953)
                    ·
                      rfl

theorem cell22_2748599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_2748599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748599 prefixEnd_2748599 := by exact prefixLift 2748599
  have htrace : WordTrace (prefixWord ++ tailWord_2748599) baseStart_2748599 baseEnd_2748599 := by
    simpa [prefixWord, tailWord_2748599, baseEnd_2748599] using wordTrace_append hprefix tailTrace_2748599
  have hstable : (prefixWord ++ tailWord_2748599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748599).length < 2 ^ (prefixWord ++ tailWord_2748599).sum := by decide
  have hdescent : baseEnd_2748599 < baseStart_2748599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748629 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 1, 5]
def baseStart_2748629 : Nat := 118140960795 + 2748629 * 2 ^ 59
def prefixEnd_2748629 : Nat := 4983230072969 + 3 ^ 40 * 2748629 * 2
def baseEnd_2748629 : Nat := 940911878591354473397861

theorem tailTrace_2748629 : CollatzResearch.WordTrace tailWord_2748629 prefixEnd_2748629 940911878591354473397861 := by
  unfold tailWord_2748629
  simp only [CollatzResearch.WordTrace]
  refine ⟨100250735559194036305200941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66833823706129357536800627 100250735559194036305200941)
  ·
    refine ⟨37594025834697763614450353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100250735559194036305200941 37594025834697763614450353)
    ·
      refine ⟨28195519376023322710837765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37594025834697763614450353 28195519376023322710837765)
      ·
        refine ⟨5286659883004373008282081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28195519376023322710837765 5286659883004373008282081)
        ·
          refine ⟨3964994912253279756211561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5286659883004373008282081 3964994912253279756211561)
          ·
            refine ⟨2973746184189959817158671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3964994912253279756211561 2973746184189959817158671)
            ·
              refine ⟨4460619276284939725738007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2973746184189959817158671 4460619276284939725738007)
              ·
                refine ⟨6690928914427409588607011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4460619276284939725738007 6690928914427409588607011)
                ·
                  refine ⟨10036393371641114382910517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6690928914427409588607011 10036393371641114382910517)
                  ·
                    refine ⟨940911878591354473397861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10036393371641114382910517 940911878591354473397861)
                    ·
                      rfl

theorem cell22_2748629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_2748629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748629 prefixEnd_2748629 := by exact prefixLift 2748629
  have htrace : WordTrace (prefixWord ++ tailWord_2748629) baseStart_2748629 baseEnd_2748629 := by
    simpa [prefixWord, tailWord_2748629, baseEnd_2748629] using wordTrace_append hprefix tailTrace_2748629
  have hstable : (prefixWord ++ tailWord_2748629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748629).length < 2 ^ (prefixWord ++ tailWord_2748629).sum := by decide
  have hdescent : baseEnd_2748629 < baseStart_2748629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748745 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 1, 6]
def baseStart_2748745 : Nat := 118140960795 + 2748745 * 2 ^ 59
def prefixEnd_2748745 : Nat := 4983230072969 + 3 ^ 40 * 2748745 * 2
def baseEnd_2748745 : Nat := 940951587761968837497505

theorem tailTrace_2748745 : CollatzResearch.WordTrace tailWord_2748745 prefixEnd_2748745 940951587761968837497505 := by
  unfold tailWord_2748745
  simp only [CollatzResearch.WordTrace]
  refine ⟨100254966426773788116423689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66836644284515858744282459 100254966426773788116423689)
  ·
    refine ⟨75191224820080341087317767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100254966426773788116423689 75191224820080341087317767)
    ·
      refine ⟨112786837230120511630976651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75191224820080341087317767 112786837230120511630976651)
      ·
        refine ⟨169180255845180767446464977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112786837230120511630976651 169180255845180767446464977)
        ·
          refine ⟨126885191883885575584848733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169180255845180767446464977 126885191883885575584848733)
          ·
            refine ⟨47581946956457090844318275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126885191883885575584848733 47581946956457090844318275)
            ·
              refine ⟨71372920434685636266477413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47581946956457090844318275 71372920434685636266477413)
              ·
                refine ⟨13382422581503556799964515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71372920434685636266477413 13382422581503556799964515)
                ·
                  refine ⟨20073633872255335199946773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13382422581503556799964515 20073633872255335199946773)
                  ·
                    refine ⟨940951587761968837497505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20073633872255335199946773 940951587761968837497505)
                    ·
                      rfl

theorem cell22_2748745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_2748745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748745 prefixEnd_2748745 := by exact prefixLift 2748745
  have htrace : WordTrace (prefixWord ++ tailWord_2748745) baseStart_2748745 baseEnd_2748745 := by
    simpa [prefixWord, tailWord_2748745, baseEnd_2748745] using wordTrace_append hprefix tailTrace_2748745
  have hstable : (prefixWord ++ tailWord_2748745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748745).length < 2 ^ (prefixWord ++ tailWord_2748745).sum := by decide
  have hdescent : baseEnd_2748745 < baseStart_2748745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748768 : List Nat := [2, 1, 1, 3, 6, 1, 2, 1, 1, 4]
def baseStart_2748768 : Nat := 118140960795 + 2748768 * 2 ^ 59
def prefixEnd_2748768 : Nat := 4983230072969 + 3 ^ 40 * 2748768 * 2
def baseEnd_2748768 : Nat := 940959461132004444172435

theorem tailTrace_2748768 : CollatzResearch.WordTrace tailWord_2748768 prefixEnd_2748768 940959461132004444172435 := by
  unfold tailWord_2748768
  simp only [CollatzResearch.WordTrace]
  refine ⟨50127902652845231522255479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66837203537126975363007305 50127902652845231522255479)
  ·
    refine ⟨75191853979267847283383219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50127902652845231522255479 75191853979267847283383219)
    ·
      refine ⟨112787780968901770925074829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75191853979267847283383219 112787780968901770925074829)
      ·
        refine ⟨42295417863338164096903061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112787780968901770925074829 42295417863338164096903061)
        ·
          refine ⟨1982597712343976442042331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42295417863338164096903061 1982597712343976442042331)
          ·
            refine ⟨2973896568515964663063497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982597712343976442042331 2973896568515964663063497)
            ·
              refine ⟨2230422426386973497297623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2973896568515964663063497 2230422426386973497297623)
              ·
                refine ⟨3345633639580460245946435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230422426386973497297623 3345633639580460245946435)
                ·
                  refine ⟨5018450459370690368919653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345633639580460245946435 5018450459370690368919653)
                  ·
                    refine ⟨940959461132004444172435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5018450459370690368919653 940959461132004444172435)
                    ·
                      rfl

theorem cell22_2748768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 1, 4].length) (baseStart_2748768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748768 prefixEnd_2748768 := by exact prefixLift 2748768
  have htrace : WordTrace (prefixWord ++ tailWord_2748768) baseStart_2748768 baseEnd_2748768 := by
    simpa [prefixWord, tailWord_2748768, baseEnd_2748768] using wordTrace_append hprefix tailTrace_2748768
  have hstable : (prefixWord ++ tailWord_2748768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748768).length < 2 ^ (prefixWord ++ tailWord_2748768).sum := by decide
  have hdescent : baseEnd_2748768 < baseStart_2748768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748809 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 3, 3]
def baseStart_2748809 : Nat := 118140960795 + 2748809 * 2 ^ 59
def prefixEnd_2748809 : Nat := 4983230072969 + 3 ^ 40 * 2748809 * 2
def baseEnd_2748809 : Nat := 940973496269894003897309

theorem tailTrace_2748809 : CollatzResearch.WordTrace tailWord_2748809 prefixEnd_2748809 940973496269894003897309 := by
  unfold tailWord_2748809
  simp only [CollatzResearch.WordTrace]
  refine ⟨100257300698541927046753481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66838200465694618031168987 100257300698541927046753481)
  ·
    refine ⟨75192975523906445285065111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100257300698541927046753481 75192975523906445285065111)
    ·
      refine ⟨112789463285859667927597667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75192975523906445285065111 112789463285859667927597667)
      ·
        refine ⟨169184194928789501891396501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112789463285859667927597667 169184194928789501891396501)
        ·
          refine ⟨7930509137287007901159211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 169184194928789501891396501 7930509137287007901159211)
          ·
            refine ⟨11895763705930511851738817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7930509137287007901159211 11895763705930511851738817)
            ·
              refine ⟨8921822779447883888804113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11895763705930511851738817 8921822779447883888804113)
              ·
                refine ⟨6691367084585912916603085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8921822779447883888804113 6691367084585912916603085)
                ·
                  refine ⟨2509262656719717343726157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6691367084585912916603085 2509262656719717343726157)
                  ·
                    refine ⟨940973496269894003897309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2509262656719717343726157 940973496269894003897309)
                    ·
                      rfl

theorem cell22_2748809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 3].length) (baseStart_2748809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748809 prefixEnd_2748809 := by exact prefixLift 2748809
  have htrace : WordTrace (prefixWord ++ tailWord_2748809) baseStart_2748809 baseEnd_2748809 := by
    simpa [prefixWord, tailWord_2748809, baseEnd_2748809] using wordTrace_append hprefix tailTrace_2748809
  have hstable : (prefixWord ++ tailWord_2748809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748809).length < 2 ^ (prefixWord ++ tailWord_2748809).sum := by decide
  have hdescent : baseEnd_2748809 < baseStart_2748809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748961 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 3, 3]
def baseStart_2748961 : Nat := 118140960795 + 2748961 * 2 ^ 59
def prefixEnd_2748961 : Nat := 4983230072969 + 3 ^ 40 * 2748961 * 2
def baseEnd_2748961 : Nat := 941025528976216274096843

theorem tailTrace_2748961 : CollatzResearch.WordTrace tailWord_2748961 prefixEnd_2748961 941025528976216274096843 := by
  unfold tailWord_2748961
  simp only [CollatzResearch.WordTrace]
  refine ⟨100262844593991257006286737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66841896395994171337524491 100262844593991257006286737)
  ·
    refine ⟨75197133445493442754715053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100262844593991257006286737 75197133445493442754715053)
    ·
      refine ⟨28198925042060041033018145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75197133445493442754715053 28198925042060041033018145)
      ·
        refine ⟨21149193781545030774763609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28198925042060041033018145 21149193781545030774763609)
        ·
          refine ⟨15861895336158773081072707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21149193781545030774763609 15861895336158773081072707)
          ·
            refine ⟨23792843004238159621609061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15861895336158773081072707 23792843004238159621609061)
            ·
              refine ⟨4461158063294654929051699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23792843004238159621609061 4461158063294654929051699)
              ·
                refine ⟨6691737094941982393577549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4461158063294654929051699 6691737094941982393577549)
                ·
                  refine ⟨2509401410603243397591581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6691737094941982393577549 2509401410603243397591581)
                  ·
                    refine ⟨941025528976216274096843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2509401410603243397591581 941025528976216274096843)
                    ·
                      rfl

theorem cell22_2748961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_2748961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748961 prefixEnd_2748961 := by exact prefixLift 2748961
  have htrace : WordTrace (prefixWord ++ tailWord_2748961) baseStart_2748961 baseEnd_2748961 := by
    simpa [prefixWord, tailWord_2748961, baseEnd_2748961] using wordTrace_append hprefix tailTrace_2748961
  have hstable : (prefixWord ++ tailWord_2748961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748961).length < 2 ^ (prefixWord ++ tailWord_2748961).sum := by decide
  have hdescent : baseEnd_2748961 < baseStart_2748961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748967 : List Nat := [1, 1, 7, 2, 1, 1, 3, 1, 2, 3]
def baseStart_2748967 : Nat := 118140960795 + 2748967 * 2 ^ 59
def prefixEnd_2748967 : Nat := 4983230072969 + 3 ^ 40 * 2748967 * 2
def baseEnd_2748967 : Nat := 941027582898834258446825

theorem tailTrace_2748967 : CollatzResearch.WordTrace tailWord_2748967 prefixEnd_2748967 941027582898834258446825 := by
  unfold tailWord_2748967
  simp only [CollatzResearch.WordTrace]
  refine ⟨100263063431969520031005155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66842042287979680020670103 100263063431969520031005155)
  ·
    refine ⟨150394595147954280046507733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100263063431969520031005155 150394595147954280046507733)
    ·
      refine ⟨3524873323780178438590025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 150394595147954280046507733 3524873323780178438590025)
      ·
        refine ⟨2643654992835133828942519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3524873323780178438590025 2643654992835133828942519)
        ·
          refine ⟨3965482489252700743413779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2643654992835133828942519 3965482489252700743413779)
          ·
            refine ⟨5948223733879051115120669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3965482489252700743413779 5948223733879051115120669)
            ·
              refine ⟨2230583900204644168170251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5948223733879051115120669 2230583900204644168170251)
              ·
                refine ⟨3345875850306966252255377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230583900204644168170251 3345875850306966252255377)
                ·
                  refine ⟨2509406887730224689191533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3345875850306966252255377 2509406887730224689191533)
                  ·
                    refine ⟨941027582898834258446825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2509406887730224689191533 941027582898834258446825)
                    ·
                      rfl

theorem cell22_2748967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_2748967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748967 prefixEnd_2748967 := by exact prefixLift 2748967
  have htrace : WordTrace (prefixWord ++ tailWord_2748967) baseStart_2748967 baseEnd_2748967 := by
    simpa [prefixWord, tailWord_2748967, baseEnd_2748967] using wordTrace_append hprefix tailTrace_2748967
  have hstable : (prefixWord ++ tailWord_2748967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748967).length < 2 ^ (prefixWord ++ tailWord_2748967).sum := by decide
  have hdescent : baseEnd_2748967 < baseStart_2748967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2748980 : List Nat := [2, 5, 1, 3, 1, 2, 2, 6]
def baseStart_2748980 : Nat := 118140960795 + 2748980 * 2 ^ 59
def prefixEnd_2748980 : Nat := 4983230072969 + 3 ^ 40 * 2748980 * 2
def baseEnd_2748980 : Nat := 104559114784945173096865

theorem tailTrace_2748980 : CollatzResearch.WordTrace tailWord_2748980 prefixEnd_2748980 104559114784945173096865 := by
  unfold tailWord_2748980
  simp only [CollatzResearch.WordTrace]
  refine ⟨50131768790461211625614197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66842358387281615500818929 50131768790461211625614197)
  ·
    refine ⟨4699853324105738589901331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50131768790461211625614197 4699853324105738589901331)
    ·
      refine ⟨7049779986158607884851997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4699853324105738589901331 7049779986158607884851997)
      ·
        refine ⟨2643667494809477956819499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7049779986158607884851997 2643667494809477956819499)
        ·
          refine ⟨3965501242214216935229249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2643667494809477956819499 3965501242214216935229249)
          ·
            refine ⟨2974125931660662701421937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3965501242214216935229249 2974125931660662701421937)
            ·
              refine ⟨2230594448745497026066453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2974125931660662701421937 2230594448745497026066453)
              ·
                refine ⟨104559114784945173096865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2230594448745497026066453 104559114784945173096865)
                ·
                  rfl

theorem cell22_2748980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 6].length) (baseStart_2748980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2748980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2748980 prefixEnd_2748980 := by exact prefixLift 2748980
  have htrace : WordTrace (prefixWord ++ tailWord_2748980) baseStart_2748980 baseEnd_2748980 := by
    simpa [prefixWord, tailWord_2748980, baseEnd_2748980] using wordTrace_append hprefix tailTrace_2748980
  have hstable : (prefixWord ++ tailWord_2748980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2748980).length < 2 ^ (prefixWord ++ tailWord_2748980).sum := by decide
  have hdescent : baseEnd_2748980 < baseStart_2748980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2748980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749038 : List Nat := [4, 1, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_2749038 : Nat := 118140960795 + 2749038 * 2 ^ 59
def prefixEnd_2749038 : Nat := 4983230072969 + 3 ^ 40 * 2749038 * 2
def baseEnd_2749038 : Nat := 941051887649813739921607

theorem tailTrace_2749038 : CollatzResearch.WordTrace tailWord_2749038 prefixEnd_2749038 941051887649813739921607 := by
  unfold tailWord_2749038
  simp only [CollatzResearch.WordTrace]
  refine ⟨12533206626839037394604971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66843768676474866104559845 12533206626839037394604971)
  ·
    refine ⟨18799809940258556091907457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12533206626839037394604971 18799809940258556091907457)
    ·
      refine ⟨14099857455193917068930593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18799809940258556091907457 14099857455193917068930593)
      ·
        refine ⟨10574893091395437801697945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14099857455193917068930593 10574893091395437801697945)
        ·
          refine ⟨7931169818546578351273459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10574893091395437801697945 7931169818546578351273459)
          ·
            refine ⟨11896754727819867526910189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7931169818546578351273459 11896754727819867526910189)
            ·
              refine ⟨4461283022932450322591321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11896754727819867526910189 4461283022932450322591321)
              ·
                refine ⟨3345962267199337741943491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4461283022932450322591321 3345962267199337741943491)
                ·
                  refine ⟨5018943400799006612915237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345962267199337741943491 5018943400799006612915237)
                  ·
                    refine ⟨941051887649813739921607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5018943400799006612915237 941051887649813739921607)
                    ·
                      rfl

theorem cell22_2749038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_2749038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749038 prefixEnd_2749038 := by exact prefixLift 2749038
  have htrace : WordTrace (prefixWord ++ tailWord_2749038) baseStart_2749038 baseEnd_2749038 := by
    simpa [prefixWord, tailWord_2749038, baseEnd_2749038] using wordTrace_append hprefix tailTrace_2749038
  have hstable : (prefixWord ++ tailWord_2749038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749038).length < 2 ^ (prefixWord ++ tailWord_2749038).sum := by decide
  have hdescent : baseEnd_2749038 < baseStart_2749038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749130 : List Nat := [3, 1, 2, 1, 4, 1, 2, 4, 1, 3]
def baseStart_2749130 : Nat := 118140960795 + 2749130 * 2 ^ 59
def prefixEnd_2749130 : Nat := 4983230072969 + 3 ^ 40 * 2749130 * 2
def baseEnd_2749130 : Nat := 941083381129956166621325

theorem tailTrace_2749130 : CollatzResearch.WordTrace tailWord_2749130 prefixEnd_2749130 941083381129956166621325 := by
  unfold tailWord_2749130
  simp only [CollatzResearch.WordTrace]
  refine ⟨25067252132594749717297211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66846005686919332579459229 25067252132594749717297211)
  ·
    refine ⟨37600878198892124575945817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25067252132594749717297211 37600878198892124575945817)
    ·
      refine ⟨28200658649169093431959363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37600878198892124575945817 28200658649169093431959363)
      ·
        refine ⟨42300987973753640147939045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28200658649169093431959363 42300987973753640147939045)
        ·
          refine ⟨7931435245078807527738571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42300987973753640147939045 7931435245078807527738571)
          ·
            refine ⟨11897152867618211291607857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7931435245078807527738571 11897152867618211291607857)
            ·
              refine ⟨8922864650713658468705893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11897152867618211291607857 8922864650713658468705893)
              ·
                refine ⟨1673037122008810962882355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8922864650713658468705893 1673037122008810962882355)
                ·
                  refine ⟨2509555683013216444323533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673037122008810962882355 2509555683013216444323533)
                  ·
                    refine ⟨941083381129956166621325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2509555683013216444323533 941083381129956166621325)
                    ·
                      rfl

theorem cell22_2749130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_2749130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749130 prefixEnd_2749130 := by exact prefixLift 2749130
  have htrace : WordTrace (prefixWord ++ tailWord_2749130) baseStart_2749130 baseEnd_2749130 := by
    simpa [prefixWord, tailWord_2749130, baseEnd_2749130] using wordTrace_append hprefix tailTrace_2749130
  have hstable : (prefixWord ++ tailWord_2749130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749130).length < 2 ^ (prefixWord ++ tailWord_2749130).sum := by decide
  have hdescent : baseEnd_2749130 < baseStart_2749130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749143 : List Nat := [1, 1, 3, 2, 1, 5, 3, 1, 5]
def baseStart_2749143 : Nat := 118140960795 + 2749143 * 2 ^ 59
def prefixEnd_2749143 : Nat := 4983230072969 + 3 ^ 40 * 2749143 * 2
def baseEnd_2749143 : Nat := 313695943765209488682095

theorem tailTrace_2749143 : CollatzResearch.WordTrace tailWord_2749143 prefixEnd_2749143 313695943765209488682095 := by
  unfold tailWord_2749143
  simp only [CollatzResearch.WordTrace]
  refine ⟨100269482679331902089412083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66846321786221268059608055 100269482679331902089412083)
  ·
    refine ⟨150404224018997853134118125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100269482679331902089412083 150404224018997853134118125)
    ·
      refine ⟨56401584007124194925294297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150404224018997853134118125 56401584007124194925294297)
      ·
        refine ⟨42301188005343146193970723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56401584007124194925294297 42301188005343146193970723)
        ·
          refine ⟨63451782008014719290956085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42301188005343146193970723 63451782008014719290956085)
          ·
            refine ⟨5948604563251379933527133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63451782008014719290956085 5948604563251379933527133)
            ·
              refine ⟨2230726711219267475072675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5948604563251379933527133 2230726711219267475072675)
              ·
                refine ⟨3346090066828901212609013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230726711219267475072675 3346090066828901212609013)
                ·
                  refine ⟨313695943765209488682095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3346090066828901212609013 313695943765209488682095)
                  ·
                    rfl

theorem cell22_2749143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 5].length) (baseStart_2749143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749143 prefixEnd_2749143 := by exact prefixLift 2749143
  have htrace : WordTrace (prefixWord ++ tailWord_2749143) baseStart_2749143 baseEnd_2749143 := by
    simpa [prefixWord, tailWord_2749143, baseEnd_2749143] using wordTrace_append hprefix tailTrace_2749143
  have hstable : (prefixWord ++ tailWord_2749143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749143).length < 2 ^ (prefixWord ++ tailWord_2749143).sum := by decide
  have hdescent : baseEnd_2749143 < baseStart_2749143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749203 : List Nat := [1, 1, 1, 2, 1, 3, 5, 3, 2, 3]
def baseStart_2749203 : Nat := 118140960795 + 2749203 * 2 ^ 59
def prefixEnd_2749203 : Nat := 4983230072969 + 3 ^ 40 * 2749203 * 2
def baseEnd_2749203 : Nat := 941108370521808309546101

theorem tailTrace_2749203 : CollatzResearch.WordTrace tailWord_2749203 prefixEnd_2749203 941108370521808309546101 := by
  unfold tailWord_2749203
  simp only [CollatzResearch.WordTrace]
  refine ⟨100271671059114532336596263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66847780706076354891064175 100271671059114532336596263)
  ·
    refine ⟨150407506588671798504894395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100271671059114532336596263 150407506588671798504894395)
    ·
      refine ⟨225611259883007697757341593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150407506588671798504894395 225611259883007697757341593)
      ·
        refine ⟨169208444912255773318006195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225611259883007697757341593 169208444912255773318006195)
        ·
          refine ⟨253812667368383659977009293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169208444912255773318006195 253812667368383659977009293)
          ·
            refine ⟨95179750263143872491378485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253812667368383659977009293 95179750263143872491378485)
            ·
              refine ⟨8923101587169738046066733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95179750263143872491378485 8923101587169738046066733)
              ·
                refine ⟨3346163095188651767275025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8923101587169738046066733 3346163095188651767275025)
                ·
                  refine ⟨2509622321391488825456269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3346163095188651767275025 2509622321391488825456269)
                  ·
                    refine ⟨941108370521808309546101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2509622321391488825456269 941108370521808309546101)
                    ·
                      rfl

theorem cell22_2749203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 3].length) (baseStart_2749203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749203 prefixEnd_2749203 := by exact prefixLift 2749203
  have htrace : WordTrace (prefixWord ++ tailWord_2749203) baseStart_2749203 baseEnd_2749203 := by
    simpa [prefixWord, tailWord_2749203, baseEnd_2749203] using wordTrace_append hprefix tailTrace_2749203
  have hstable : (prefixWord ++ tailWord_2749203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749203).length < 2 ^ (prefixWord ++ tailWord_2749203).sum := by decide
  have hdescent : baseEnd_2749203 < baseStart_2749203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749207 : List Nat := [1, 1, 3, 4, 4, 1, 1, 2, 1, 4]
def baseStart_2749207 : Nat := 118140960795 + 2749207 * 2 ^ 59
def prefixEnd_2749207 : Nat := 4983230072969 + 3 ^ 40 * 2749207 * 2
def baseEnd_2749207 : Nat := 941109739803553632446089

theorem tailTrace_2749207 : CollatzResearch.WordTrace tailWord_2749207 prefixEnd_2749207 941109739803553632446089 := by
  unfold tailWord_2749207
  simp only [CollatzResearch.WordTrace]
  refine ⟨100271816951100041019741875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66847877967400027346494583 100271816951100041019741875)
  ·
    refine ⟨150407725426650061529612813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100271816951100041019741875 150407725426650061529612813)
    ·
      refine ⟨56402897034993773073604805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150407725426650061529612813 56402897034993773073604805)
      ·
        refine ⟨10575543194061332451300901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56402897034993773073604805 10575543194061332451300901)
        ·
          refine ⟨1982914348886499834618919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10575543194061332451300901 1982914348886499834618919)
          ·
            refine ⟨2974371523329749751928379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982914348886499834618919 2974371523329749751928379)
            ·
              refine ⟨4461557284994624627892569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2974371523329749751928379 4461557284994624627892569)
              ·
                refine ⟨3346167963745968470919427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4461557284994624627892569 3346167963745968470919427)
                ·
                  refine ⟨5019251945618952706379141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3346167963745968470919427 5019251945618952706379141)
                  ·
                    refine ⟨941109739803553632446089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5019251945618952706379141 941109739803553632446089)
                    ·
                      rfl

theorem cell22_2749207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_2749207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749207 prefixEnd_2749207 := by exact prefixLift 2749207
  have htrace : WordTrace (prefixWord ++ tailWord_2749207) baseStart_2749207 baseEnd_2749207 := by
    simpa [prefixWord, tailWord_2749207, baseEnd_2749207] using wordTrace_append hprefix tailTrace_2749207
  have hstable : (prefixWord ++ tailWord_2749207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749207).length < 2 ^ (prefixWord ++ tailWord_2749207).sum := by decide
  have hdescent : baseEnd_2749207 < baseStart_2749207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749216 : List Nat := [2, 1, 1, 5, 1, 2, 2, 8]
def baseStart_2749216 : Nat := 118140960795 + 2749216 * 2 ^ 59
def prefixEnd_2749216 : Nat := 4983230072969 + 3 ^ 40 * 2749216 * 2
def baseEnd_2749216 : Nat := 104568091187497845441229

theorem tailTrace_2749216 : CollatzResearch.WordTrace tailWord_2749216 prefixEnd_2749216 104568091187497845441229 := by
  unfold tailWord_2749216
  simp only [CollatzResearch.WordTrace]
  refine ⟨50136072604033717778409751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66848096805378290371213001 50136072604033717778409751)
  ·
    refine ⟨75204108906050576667614627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50136072604033717778409751 75204108906050576667614627)
    ·
      refine ⟨112806163359075865001421941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75204108906050576667614627 112806163359075865001421941)
      ·
        refine ⟨10575577814913362343883307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112806163359075865001421941 10575577814913362343883307)
        ·
          refine ⟨15863366722370043515824961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10575577814913362343883307 15863366722370043515824961)
          ·
            refine ⟨11897525041777532636868721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15863366722370043515824961 11897525041777532636868721)
            ·
              refine ⟨8923143781333149477651541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11897525041777532636868721 8923143781333149477651541)
              ·
                refine ⟨104568091187497845441229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8923143781333149477651541 104568091187497845441229)
                ·
                  rfl

theorem cell22_2749216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 8].length) (baseStart_2749216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749216 prefixEnd_2749216 := by exact prefixLift 2749216
  have htrace : WordTrace (prefixWord ++ tailWord_2749216) baseStart_2749216 baseEnd_2749216 := by
    simpa [prefixWord, tailWord_2749216, baseEnd_2749216] using wordTrace_append hprefix tailTrace_2749216
  have hstable : (prefixWord ++ tailWord_2749216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749216).length < 2 ^ (prefixWord ++ tailWord_2749216).sum := by decide
  have hdescent : baseEnd_2749216 < baseStart_2749216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749218 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_2749218 : Nat := 118140960795 + 2749218 * 2 ^ 59
def prefixEnd_2749218 : Nat := 4983230072969 + 3 ^ 40 * 2749218 * 2
def baseEnd_2749218 : Nat := 941113505328353270421055

theorem tailTrace_2749218 : CollatzResearch.WordTrace tailWord_2749218 prefixEnd_2749218 941113505328353270421055 := by
  unfold tailWord_2749218
  simp only [CollatzResearch.WordTrace]
  refine ⟨25068054538515047474598077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66848145436040126598928205 25068054538515047474598077)
  ·
    refine ⟨9400520451943142802974279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25068054538515047474598077 9400520451943142802974279)
    ·
      refine ⟨14100780677914714204461419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9400520451943142802974279 14100780677914714204461419)
      ·
        refine ⟨21151171016872071306692129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14100780677914714204461419 21151171016872071306692129)
        ·
          refine ⟨15863378262654053480019097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21151171016872071306692129 15863378262654053480019097)
          ·
            refine ⟨11897533696990540110014323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15863378262654053480019097 11897533696990540110014323)
            ·
              refine ⟨17846300545485810165021485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11897533696990540110014323 17846300545485810165021485)
              ·
                refine ⟨6692362704557178811883057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17846300545485810165021485 6692362704557178811883057)
                ·
                  refine ⟨5019272028417884108912293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6692362704557178811883057 5019272028417884108912293)
                  ·
                    refine ⟨941113505328353270421055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5019272028417884108912293 941113505328353270421055)
                    ·
                      rfl

theorem cell22_2749218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_2749218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749218 prefixEnd_2749218 := by exact prefixLift 2749218
  have htrace : WordTrace (prefixWord ++ tailWord_2749218) baseStart_2749218 baseEnd_2749218 := by
    simpa [prefixWord, tailWord_2749218, baseEnd_2749218] using wordTrace_append hprefix tailTrace_2749218
  have hstable : (prefixWord ++ tailWord_2749218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749218).length < 2 ^ (prefixWord ++ tailWord_2749218).sum := by decide
  have hdescent : baseEnd_2749218 < baseStart_2749218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749265 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 3, 3]
def baseStart_2749265 : Nat := 118140960795 + 2749265 * 2 ^ 59
def prefixEnd_2749265 : Nat := 4983230072969 + 3 ^ 40 * 2749265 * 2
def baseEnd_2749265 : Nat := 941129594388860814495911

theorem tailTrace_2749265 : CollatzResearch.WordTrace tailWord_2749265 prefixEnd_2749265 941129594388860814495911 := by
  unfold tailWord_2749265
  simp only [CollatzResearch.WordTrace]
  refine ⟨100273932384889916925353249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66849288256593277950235499 100273932384889916925353249)
  ·
    refine ⟨75205449288667437694014937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100273932384889916925353249 75205449288667437694014937)
    ·
      refine ⟨56404086966500578270511203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75205449288667437694014937 56404086966500578270511203)
      ·
        refine ⟨84606130449750867405766805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56404086966500578270511203 84606130449750867405766805)
        ·
          refine ⟨3965912364832071909645319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84606130449750867405766805 3965912364832071909645319)
          ·
            refine ⟨5948868547248107864467979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3965912364832071909645319 5948868547248107864467979)
            ·
              refine ⟨8923302820872161796701969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5948868547248107864467979 8923302820872161796701969)
              ·
                refine ⟨6692477115654121347526477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8923302820872161796701969 6692477115654121347526477)
                ·
                  refine ⟨2509678918370295505322429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6692477115654121347526477 2509678918370295505322429)
                  ·
                    refine ⟨941129594388860814495911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2509678918370295505322429 941129594388860814495911)
                    ·
                      rfl

theorem cell22_2749265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_2749265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749265 prefixEnd_2749265 := by exact prefixLift 2749265
  have htrace : WordTrace (prefixWord ++ tailWord_2749265) baseStart_2749265 baseEnd_2749265 := by
    simpa [prefixWord, tailWord_2749265, baseEnd_2749265] using wordTrace_append hprefix tailTrace_2749265
  have hstable : (prefixWord ++ tailWord_2749265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749265).length < 2 ^ (prefixWord ++ tailWord_2749265).sum := by decide
  have hdescent : baseEnd_2749265 < baseStart_2749265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749353 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 2, 4]
def baseStart_2749353 : Nat := 118140960795 + 2749353 * 2 ^ 59
def prefixEnd_2749353 : Nat := 4983230072969 + 3 ^ 40 * 2749353 * 2
def baseEnd_2749353 : Nat := 941159718587257918295641

theorem tailTrace_2749353 : CollatzResearch.WordTrace tailWord_2749353 prefixEnd_2749353 941159718587257918295641 := by
  unfold tailWord_2749353
  simp only [CollatzResearch.WordTrace]
  refine ⟨100277142008571107954556713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66851428005714071969704475 100277142008571107954556713)
  ·
    refine ⟨75207856506428330965917535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100277142008571107954556713 75207856506428330965917535)
    ·
      refine ⟨112811784759642496448876303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75207856506428330965917535 112811784759642496448876303)
      ·
        refine ⟨169217677139463744673314455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112811784759642496448876303 169217677139463744673314455)
        ·
          refine ⟨253826515709195617009971683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169217677139463744673314455 253826515709195617009971683)
          ·
            refine ⟨380739773563793425514957525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253826515709195617009971683 380739773563793425514957525)
            ·
              refine ⟨8923588442901408410506817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 380739773563793425514957525 8923588442901408410506817)
              ·
                refine ⟨6692691332176056307880113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8923588442901408410506817 6692691332176056307880113)
                ·
                  refine ⟨5019518499132042230910085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6692691332176056307880113 5019518499132042230910085)
                  ·
                    refine ⟨941159718587257918295641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5019518499132042230910085 941159718587257918295641)
                    ·
                      rfl

theorem cell22_2749353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_2749353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749353 prefixEnd_2749353 := by exact prefixLift 2749353
  have htrace : WordTrace (prefixWord ++ tailWord_2749353) baseStart_2749353 baseEnd_2749353 := by
    simpa [prefixWord, tailWord_2749353, baseEnd_2749353] using wordTrace_append hprefix tailTrace_2749353
  have hstable : (prefixWord ++ tailWord_2749353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749353).length < 2 ^ (prefixWord ++ tailWord_2749353).sum := by decide
  have hdescent : baseEnd_2749353 < baseStart_2749353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749368 : List Nat := [2, 1, 2, 1, 2, 5, 2, 7]
def baseStart_2749368 : Nat := 118140960795 + 2749368 * 2 ^ 59
def prefixEnd_2749368 : Nat := 4983230072969 + 3 ^ 40 * 2749368 * 2
def baseEnd_2749368 : Nat := 104573872599311431018955

theorem tailTrace_2749368 : CollatzResearch.WordTrace tailWord_2749368 prefixEnd_2749368 104573872599311431018955 := by
  unfold tailWord_2749368
  simp only [CollatzResearch.WordTrace]
  refine ⟨50138844551758382758176379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66851792735677843677568505 50138844551758382758176379)
  ·
    refine ⟨75208266827637574137264569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50138844551758382758176379 75208266827637574137264569)
    ·
      refine ⟨56406200120728180602948427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75208266827637574137264569 56406200120728180602948427)
      ·
        refine ⟨84609300181092270904422641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56406200120728180602948427 84609300181092270904422641)
        ·
          refine ⟨63456975135819203178316981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84609300181092270904422641 63456975135819203178316981)
          ·
            refine ⟨5949091418983050297967217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63456975135819203178316981 5949091418983050297967217)
            ·
              refine ⟨4461818564237287723475413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5949091418983050297967217 4461818564237287723475413)
              ·
                refine ⟨104573872599311431018955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4461818564237287723475413 104573872599311431018955)
                ·
                  rfl

theorem cell22_2749368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 7].length) (baseStart_2749368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749368 prefixEnd_2749368 := by exact prefixLift 2749368
  have htrace : WordTrace (prefixWord ++ tailWord_2749368) baseStart_2749368 baseEnd_2749368 := by
    simpa [prefixWord, tailWord_2749368, baseEnd_2749368] using wordTrace_append hprefix tailTrace_2749368
  have hstable : (prefixWord ++ tailWord_2749368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749368).length < 2 ^ (prefixWord ++ tailWord_2749368).sum := by decide
  have hdescent : baseEnd_2749368 < baseStart_2749368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749475 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 6]
def baseStart_2749475 : Nat := 118140960795 + 2749475 * 2 ^ 59
def prefixEnd_2749475 : Nat := 4983230072969 + 3 ^ 40 * 2749475 * 2
def baseEnd_2749475 : Nat := 313733827226830088915089

theorem tailTrace_2749475 : CollatzResearch.WordTrace tailWord_2749475 prefixEnd_2749475 313733827226830088915089 := by
  unfold tailWord_2749475
  simp only [CollatzResearch.WordTrace]
  refine ⟨100281591714129122790497879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66854394476086081860331919 100281591714129122790497879)
  ·
    refine ⟨150422387571193684185746819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100281591714129122790497879 150422387571193684185746819)
    ·
      refine ⟨225633581356790526278620229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150422387571193684185746819 225633581356790526278620229)
      ·
        refine ⟨42306296504398223677241293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225633581356790526278620229 42306296504398223677241293)
        ·
          refine ⟨15864861189149333878965485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42306296504398223677241293 15864861189149333878965485)
          ·
            refine ⟨5949322945931000204612057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15864861189149333878965485 5949322945931000204612057)
            ·
              refine ⟨4461992209448250153459043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5949322945931000204612057 4461992209448250153459043)
              ·
                refine ⟨6692988314172375230188565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4461992209448250153459043 6692988314172375230188565)
                ·
                  refine ⟨313733827226830088915089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6692988314172375230188565 313733827226830088915089)
                  ·
                    rfl

theorem cell22_2749475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 6].length) (baseStart_2749475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749475 prefixEnd_2749475 := by exact prefixLift 2749475
  have htrace : WordTrace (prefixWord ++ tailWord_2749475) baseStart_2749475 baseEnd_2749475 := by
    simpa [prefixWord, tailWord_2749475, baseEnd_2749475] using wordTrace_append hprefix tailTrace_2749475
  have hstable : (prefixWord ++ tailWord_2749475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749475).length < 2 ^ (prefixWord ++ tailWord_2749475).sum := by decide
  have hdescent : baseEnd_2749475 < baseStart_2749475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749488 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 3, 6]
def baseStart_2749488 : Nat := 118140960795 + 2749488 * 2 ^ 59
def prefixEnd_2749488 : Nat := 4983230072969 + 3 ^ 40 * 2749488 * 2
def baseEnd_2749488 : Nat := 941205931846162566170227

theorem tailTrace_2749488 : CollatzResearch.WordTrace tailWord_2749488 prefixEnd_2749488 941205931846162566170227 := by
  unfold tailWord_2749488
  simp only [CollatzResearch.WordTrace]
  refine ⟨50141032931541013005360559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66854710575388017340480745 50141032931541013005360559)
  ·
    refine ⟨75211549397311519508040839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50141032931541013005360559 75211549397311519508040839)
    ·
      refine ⟨112817324095967279262061259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75211549397311519508040839 112817324095967279262061259)
      ·
        refine ⟨169225986143950918893091889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112817324095967279262061259 169225986143950918893091889)
        ·
          refine ⟨126919489607963189169818917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169225986143950918893091889 126919489607963189169818917)
          ·
            refine ⟨23797404301493097969341047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126919489607963189169818917 23797404301493097969341047)
            ·
              refine ⟨35696106452239646954011571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23797404301493097969341047 35696106452239646954011571)
              ·
                refine ⟨53544159678359470431017357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35696106452239646954011571 53544159678359470431017357)
                ·
                  refine ⟨20079059879384801411631509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53544159678359470431017357 20079059879384801411631509)
                  ·
                    refine ⟨941205931846162566170227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20079059879384801411631509 941205931846162566170227)
                    ·
                      rfl

theorem cell22_2749488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_2749488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749488 prefixEnd_2749488 := by exact prefixLift 2749488
  have htrace : WordTrace (prefixWord ++ tailWord_2749488) baseStart_2749488 baseEnd_2749488 := by
    simpa [prefixWord, tailWord_2749488, baseEnd_2749488] using wordTrace_append hprefix tailTrace_2749488
  have hstable : (prefixWord ++ tailWord_2749488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749488).length < 2 ^ (prefixWord ++ tailWord_2749488).sum := by decide
  have hdescent : baseEnd_2749488 < baseStart_2749488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749492 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 6]
def baseStart_2749492 : Nat := 118140960795 + 2749492 * 2 ^ 59
def prefixEnd_2749492 : Nat := 4983230072969 + 3 ^ 40 * 2749492 * 2
def baseEnd_2749492 : Nat := 313735767042635963023405

theorem tailTrace_2749492 : CollatzResearch.WordTrace tailWord_2749492 prefixEnd_2749492 313735767042635963023405 := by
  unfold tailWord_2749492
  simp only [CollatzResearch.WordTrace]
  refine ⟨50141105877533767346933365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66854807836711689795911153 50141105877533767346933365)
  ·
    refine ⟨4700728676018790688775003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50141105877533767346933365 4700728676018790688775003)
    ·
      refine ⟨7051093014028186033162505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4700728676018790688775003 7051093014028186033162505)
      ·
        refine ⟨5288319760521139524871879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7051093014028186033162505 5288319760521139524871879)
        ·
          refine ⟨7932479640781709287307819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5288319760521139524871879 7932479640781709287307819)
          ·
            refine ⟨11898719461172563930961729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7932479640781709287307819 11898719461172563930961729)
            ·
              refine ⟨8924039595879422948221297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11898719461172563930961729 8924039595879422948221297)
              ·
                refine ⟨6693029696909567211165973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8924039595879422948221297 6693029696909567211165973)
                ·
                  refine ⟨313735767042635963023405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6693029696909567211165973 313735767042635963023405)
                  ·
                    rfl

theorem cell22_2749492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_2749492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749492 prefixEnd_2749492 := by exact prefixLift 2749492
  have htrace : WordTrace (prefixWord ++ tailWord_2749492) baseStart_2749492 baseEnd_2749492 := by
    simpa [prefixWord, tailWord_2749492, baseEnd_2749492] using wordTrace_append hprefix tailTrace_2749492
  have hstable : (prefixWord ++ tailWord_2749492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749492).length < 2 ^ (prefixWord ++ tailWord_2749492).sum := by decide
  have hdescent : baseEnd_2749492 < baseStart_2749492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749494 : List Nat := [5, 1, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_2749494 : Nat := 118140960795 + 2749494 * 2 ^ 59
def prefixEnd_2749494 : Nat := 4983230072969 + 3 ^ 40 * 2749494 * 2
def baseEnd_2749494 : Nat := 941207985768780550520209

theorem tailTrace_2749494 : CollatzResearch.WordTrace tailWord_2749494 prefixEnd_2749494 941207985768780550520209 := by
  unfold tailWord_2749494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6267642793816268064714971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66854856467373526023626357 6267642793816268064714971)
  ·
    refine ⟨9401464190724402097072457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6267642793816268064714971 9401464190724402097072457)
    ·
      refine ⟨7051098143043301572804343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9401464190724402097072457 7051098143043301572804343)
      ·
        refine ⟨10576647214564952359206515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7051098143043301572804343 10576647214564952359206515)
        ·
          refine ⟨15864970821847428538809773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10576647214564952359206515 15864970821847428538809773)
          ·
            refine ⟨5949364058192785702053665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15864970821847428538809773 5949364058192785702053665)
            ·
              refine ⟨4462023043644589276540249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5949364058192785702053665 4462023043644589276540249)
              ·
                refine ⟨3346517282733441957405187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4462023043644589276540249 3346517282733441957405187)
                ·
                  refine ⟨5019775924100162936107781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3346517282733441957405187 5019775924100162936107781)
                  ·
                    refine ⟨941207985768780550520209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5019775924100162936107781 941207985768780550520209)
                    ·
                      rfl

theorem cell22_2749494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_2749494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749494 prefixEnd_2749494 := by exact prefixLift 2749494
  have htrace : WordTrace (prefixWord ++ tailWord_2749494) baseStart_2749494 baseEnd_2749494 := by
    simpa [prefixWord, tailWord_2749494, baseEnd_2749494] using wordTrace_append hprefix tailTrace_2749494
  have hstable : (prefixWord ++ tailWord_2749494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749494).length < 2 ^ (prefixWord ++ tailWord_2749494).sum := by decide
  have hdescent : baseEnd_2749494 < baseStart_2749494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749522 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_2749522 : Nat := 118140960795 + 2749522 * 2 ^ 59
def prefixEnd_2749522 : Nat := 4983230072969 + 3 ^ 40 * 2749522 * 2
def baseEnd_2749522 : Nat := 941217570740997810820123

theorem tailTrace_2749522 : CollatzResearch.WordTrace tailWord_2749522 prefixEnd_2749522 941217570740997810820123 := by
  unfold tailWord_2749522
  simp only [CollatzResearch.WordTrace]
  refine ⟨25070826486239712454364705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66855537296639233211639213 25070826486239712454364705)
  ·
    refine ⟨18803119864679784340773529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25070826486239712454364705 18803119864679784340773529)
    ·
      refine ⟨14102339898509838255580147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18803119864679784340773529 14102339898509838255580147)
      ·
        refine ⟨21153509847764757383370221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14102339898509838255580147 21153509847764757383370221)
        ·
          refine ⟨7932566192911784018763833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21153509847764757383370221 7932566192911784018763833)
          ·
            refine ⟨5949424644683838014072875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7932566192911784018763833 5949424644683838014072875)
            ·
              refine ⟨8924136967025757021109313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5949424644683838014072875 8924136967025757021109313)
              ·
                refine ⟨6693102725269317765831985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8924136967025757021109313 6693102725269317765831985)
                ·
                  refine ⟨5019827043951988324373989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6693102725269317765831985 5019827043951988324373989)
                  ·
                    refine ⟨941217570740997810820123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5019827043951988324373989 941217570740997810820123)
                    ·
                      rfl

theorem cell22_2749522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_2749522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749522 prefixEnd_2749522 := by exact prefixLift 2749522
  have htrace : WordTrace (prefixWord ++ tailWord_2749522) baseStart_2749522 baseEnd_2749522 := by
    simpa [prefixWord, tailWord_2749522, baseEnd_2749522] using wordTrace_append hprefix tailTrace_2749522
  have hstable : (prefixWord ++ tailWord_2749522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749522).length < 2 ^ (prefixWord ++ tailWord_2749522).sum := by decide
  have hdescent : baseEnd_2749522 < baseStart_2749522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749526 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_2749526 : Nat := 118140960795 + 2749526 * 2 ^ 59
def prefixEnd_2749526 : Nat := 4983230072969 + 3 ^ 40 * 2749526 * 2
def baseEnd_2749526 : Nat := 313739646674247711240037

theorem tailTrace_2749526 : CollatzResearch.WordTrace tailWord_2749526 prefixEnd_2749526 313739646674247711240037 := by
  unfold tailWord_2749526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6267715739809022406287777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66855634557962905667069621 6267715739809022406287777)
  ·
    refine ⟨4700786804856766804715833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6267715739809022406287777 4700786804856766804715833)
    ·
      refine ⟨3525590103642575103536875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4700786804856766804715833 3525590103642575103536875)
      ·
        refine ⟨5288385155463862655305313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3525590103642575103536875 5288385155463862655305313)
        ·
          refine ⟨3966288866597896991478985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5288385155463862655305313 3966288866597896991478985)
          ·
            refine ⟨2974716649948422743609239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3966288866597896991478985 2974716649948422743609239)
            ·
              refine ⟨4462074974922634115413859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2974716649948422743609239 4462074974922634115413859)
              ·
                refine ⟨6693112462383951173120789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462074974922634115413859 6693112462383951173120789)
                ·
                  refine ⟨313739646674247711240037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6693112462383951173120789 313739646674247711240037)
                  ·
                    rfl

theorem cell22_2749526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_2749526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749526 prefixEnd_2749526 := by exact prefixLift 2749526
  have htrace : WordTrace (prefixWord ++ tailWord_2749526) baseStart_2749526 baseEnd_2749526 := by
    simpa [prefixWord, tailWord_2749526, baseEnd_2749526] using wordTrace_append hprefix tailTrace_2749526
  have hstable : (prefixWord ++ tailWord_2749526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749526).length < 2 ^ (prefixWord ++ tailWord_2749526).sum := by decide
  have hdescent : baseEnd_2749526 < baseStart_2749526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749582 : List Nat := [4, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_2749582 : Nat := 118140960795 + 2749582 * 2 ^ 59
def prefixEnd_2749582 : Nat := 4983230072969 + 3 ^ 40 * 2749582 * 2
def baseEnd_2749582 : Nat := 313746036655725884773313

theorem tailTrace_2749582 : CollatzResearch.WordTrace tailWord_2749582 prefixEnd_2749582 313746036655725884773313 := by
  unfold tailWord_2749582
  simp only [CollatzResearch.WordTrace]
  refine ⟨12535686790592685008080375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66856996216494320043095333 12535686790592685008080375)
  ·
    refine ⟨18803530185889027512120563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12535686790592685008080375 18803530185889027512120563)
    ·
      refine ⟨28205295278833541268180845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18803530185889027512120563 28205295278833541268180845)
      ·
        refine ⟨10576985729562577975567817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28205295278833541268180845 10576985729562577975567817)
        ·
          refine ⟨7932739297171933481675863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10576985729562577975567817 7932739297171933481675863)
          ·
            refine ⟨11899108945757900222513795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7932739297171933481675863 11899108945757900222513795)
            ·
              refine ⟨17848663418636850333770693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11899108945757900222513795 17848663418636850333770693)
              ·
                refine ⟨3346624390994409437582005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17848663418636850333770693 3346624390994409437582005)
                ·
                  refine ⟨313746036655725884773313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3346624390994409437582005 313746036655725884773313)
                  ·
                    rfl

theorem cell22_2749582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_2749582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749582 prefixEnd_2749582 := by exact prefixLift 2749582
  have htrace : WordTrace (prefixWord ++ tailWord_2749582) baseStart_2749582 baseEnd_2749582 := by
    simpa [prefixWord, tailWord_2749582, baseEnd_2749582] using wordTrace_append hprefix tailTrace_2749582
  have hstable : (prefixWord ++ tailWord_2749582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749582).length < 2 ^ (prefixWord ++ tailWord_2749582).sum := by decide
  have hdescent : baseEnd_2749582 < baseStart_2749582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749586 : List Nat := [3, 2, 3, 1, 1, 3, 1, 4, 1, 3]
def baseStart_2749586 : Nat := 118140960795 + 2749586 * 2 ^ 59
def prefixEnd_2749586 : Nat := 4983230072969 + 3 ^ 40 * 2749586 * 2
def baseEnd_2749586 : Nat := 941239479248922977219927

theorem tailTrace_2749586 : CollatzResearch.WordTrace tailWord_2749586 prefixEnd_2749586 941239479248922977219927 := by
  unfold tailWord_2749586
  simp only [CollatzResearch.WordTrace]
  refine ⟨25071410054181747186947153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66857093477817992498525741 25071410054181747186947153)
  ·
    refine ⟨18803557540636310390210365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25071410054181747186947153 18803557540636310390210365)
    ·
      refine ⟨7051334077738616396328887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18803557540636310390210365 7051334077738616396328887)
      ·
        refine ⟨10577001116607924594493331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7051334077738616396328887 10577001116607924594493331)
        ·
          refine ⟨15865501674911886891739997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10577001116607924594493331 15865501674911886891739997)
          ·
            refine ⟨5949563128091957584402499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15865501674911886891739997 5949563128091957584402499)
            ·
              refine ⟨8924344692137936376603749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5949563128091957584402499 8924344692137936376603749)
              ·
                refine ⟨1673314629775863070613203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8924344692137936376603749 1673314629775863070613203)
                ·
                  refine ⟨2509971944663794605919805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673314629775863070613203 2509971944663794605919805)
                  ·
                    refine ⟨941239479248922977219927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2509971944663794605919805 941239479248922977219927)
                    ·
                      rfl

theorem cell22_2749586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_2749586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749586 prefixEnd_2749586 := by exact prefixLift 2749586
  have htrace : WordTrace (prefixWord ++ tailWord_2749586) baseStart_2749586 baseEnd_2749586 := by
    simpa [prefixWord, tailWord_2749586, baseEnd_2749586] using wordTrace_append hprefix tailTrace_2749586
  have hstable : (prefixWord ++ tailWord_2749586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749586).length < 2 ^ (prefixWord ++ tailWord_2749586).sum := by decide
  have hdescent : baseEnd_2749586 < baseStart_2749586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749629 : List Nat := [1, 4, 1, 2, 1, 1, 6, 1, 1, 4]
def baseStart_2749629 : Nat := 118140960795 + 2749629 * 2 ^ 59
def prefixEnd_2749629 : Nat := 4983230072969 + 3 ^ 40 * 2749629 * 2
def baseEnd_2749629 : Nat := 941254199027685198394795

theorem tailTrace_2749629 : CollatzResearch.WordTrace tailWord_2749629 prefixEnd_2749629 941254199027685198394795 := by
  unfold tailWord_2749629
  simp only [CollatzResearch.WordTrace]
  refine ⟨100287208555571207091603941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66858139037047471394402627 100287208555571207091603941)
  ·
    refine ⟨18803851604169601329675739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100287208555571207091603941 18803851604169601329675739)
    ·
      refine ⟨28205777406254401994513609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18803851604169601329675739 28205777406254401994513609)
      ·
        refine ⟨21154333054690801495885207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28205777406254401994513609 21154333054690801495885207)
        ·
          refine ⟨31731499582036202243827811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21154333054690801495885207 31731499582036202243827811)
          ·
            refine ⟨47597249373054303365741717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31731499582036202243827811 47597249373054303365741717)
            ·
              refine ⟨2231121064361920470269143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47597249373054303365741717 2231121064361920470269143)
              ·
                refine ⟨3346681596542880705403715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2231121064361920470269143 3346681596542880705403715)
                ·
                  refine ⟨5020022394814321058105573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3346681596542880705403715 5020022394814321058105573)
                  ·
                    refine ⟨941254199027685198394795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5020022394814321058105573 941254199027685198394795)
                    ·
                      rfl

theorem cell22_2749629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_2749629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749629 prefixEnd_2749629 := by exact prefixLift 2749629
  have htrace : WordTrace (prefixWord ++ tailWord_2749629) baseStart_2749629 baseEnd_2749629 := by
    simpa [prefixWord, tailWord_2749629, baseEnd_2749629] using wordTrace_append hprefix tailTrace_2749629
  have hstable : (prefixWord ++ tailWord_2749629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749629).length < 2 ^ (prefixWord ++ tailWord_2749629).sum := by decide
  have hdescent : baseEnd_2749629 < baseStart_2749629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749794 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2749794 : Nat := 118140960795 + 2749794 * 2 ^ 59
def prefixEnd_2749794 : Nat := 4983230072969 + 3 ^ 40 * 2749794 * 2
def baseEnd_2749794 : Nat := 941310681899679768019289

theorem tailTrace_2749794 : CollatzResearch.WordTrace tailWord_2749794 prefixEnd_2749794 941310681899679768019289 := by
  unfold tailWord_2749794
  simp only [CollatzResearch.WordTrace]
  refine ⟨25073306649993360067840109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66862151066648960180906957 25073306649993360067840109)
  ·
    refine ⟨9402489993747510025440041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25073306649993360067840109 9402489993747510025440041)
    ·
      refine ⟨7051867495310632519080031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9402489993747510025440041 7051867495310632519080031)
      ·
        refine ⟨10577801242965948778620047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7051867495310632519080031 10577801242965948778620047)
        ·
          refine ⟨15866701864448923167930071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10577801242965948778620047 15866701864448923167930071)
          ·
            refine ⟨23800052796673384751895107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15866701864448923167930071 23800052796673384751895107)
            ·
              refine ⟨35700079195010077127842661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23800052796673384751895107 35700079195010077127842661)
              ·
                refine ⟨6693764849064389461470499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35700079195010077127842661 6693764849064389461470499)
                ·
                  refine ⟨10040647273596584192205749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6693764849064389461470499 10040647273596584192205749)
                  ·
                    refine ⟨941310681899679768019289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10040647273596584192205749 941310681899679768019289)
                    ·
                      rfl

theorem cell22_2749794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2749794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749794 prefixEnd_2749794 := by exact prefixLift 2749794
  have htrace : WordTrace (prefixWord ++ tailWord_2749794) baseStart_2749794 baseEnd_2749794 := by
    simpa [prefixWord, tailWord_2749794, baseEnd_2749794] using wordTrace_append hprefix tailTrace_2749794
  have hstable : (prefixWord ++ tailWord_2749794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749794).length < 2 ^ (prefixWord ++ tailWord_2749794).sum := by decide
  have hdescent : baseEnd_2749794 < baseStart_2749794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749796 : List Nat := [2, 3, 1, 1, 3, 3, 2, 3, 4]
def baseStart_2749796 : Nat := 118140960795 + 2749796 * 2 ^ 59
def prefixEnd_2749796 : Nat := 4983230072969 + 3 ^ 40 * 2749796 * 2
def baseEnd_2749796 : Nat := 313770455513517476489761

theorem tailTrace_2749796 : CollatzResearch.WordTrace tailWord_2749796 prefixEnd_2749796 313770455513517476489761 := by
  unfold tailWord_2749796
  simp only [CollatzResearch.WordTrace]
  refine ⟨50146649772983097306466621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66862199697310796408622161 50146649772983097306466621)
  ·
    refine ⟨18804993664868661489924983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50146649772983097306466621 18804993664868661489924983)
    ·
      refine ⟨28207490497302992234887475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18804993664868661489924983 28207490497302992234887475)
      ·
        refine ⟨42311235745954488352331213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28207490497302992234887475 42311235745954488352331213)
        ·
          refine ⟨15866713404732933132124205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42311235745954488352331213 15866713404732933132124205)
          ·
            refine ⟨5950017526774849924546577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15866713404732933132124205 5950017526774849924546577)
            ·
              refine ⟨4462513145081137443409933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5950017526774849924546577 4462513145081137443409933)
              ·
                refine ⟨1673442429405426541278725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4462513145081137443409933 1673442429405426541278725)
                ·
                  refine ⟨313770455513517476489761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1673442429405426541278725 313770455513517476489761)
                  ·
                    rfl

theorem cell22_2749796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_2749796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749796 prefixEnd_2749796 := by exact prefixLift 2749796
  have htrace : WordTrace (prefixWord ++ tailWord_2749796) baseStart_2749796 baseEnd_2749796 := by
    simpa [prefixWord, tailWord_2749796, baseEnd_2749796] using wordTrace_append hprefix tailTrace_2749796
  have hstable : (prefixWord ++ tailWord_2749796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749796).length < 2 ^ (prefixWord ++ tailWord_2749796).sum := by decide
  have hdescent : baseEnd_2749796 < baseStart_2749796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749826 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2749826 : Nat := 118140960795 + 2749826 * 2 ^ 59
def prefixEnd_2749826 : Nat := 4983230072969 + 3 ^ 40 * 2749826 * 2
def baseEnd_2749826 : Nat := 941321636153642351219191

theorem tailTrace_2749826 : CollatzResearch.WordTrace tailWord_2749826 prefixEnd_2749826 941321636153642351219191 := by
  unfold tailWord_2749826
  simp only [CollatzResearch.WordTrace]
  refine ⟨25073598433964377434131333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66862929157238339824350221 25073598433964377434131333)
  ·
    refine ⟨4701299706368320768899625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25073598433964377434131333 4701299706368320768899625)
    ·
      refine ⟨3525974779776240576674719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4701299706368320768899625 3525974779776240576674719)
      ·
        refine ⟨5288962169664360865012079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3525974779776240576674719 5288962169664360865012079)
        ·
          refine ⟨7933443254496541297518119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5288962169664360865012079 7933443254496541297518119)
          ·
            refine ⟨11900164881744811946277179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7933443254496541297518119 11900164881744811946277179)
            ·
              refine ⟨17850247322617217919415769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11900164881744811946277179 17850247322617217919415769)
              ·
                refine ⟨13387685491962913439561827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17850247322617217919415769 13387685491962913439561827)
                ·
                  refine ⟨20081528237944370159342741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13387685491962913439561827 20081528237944370159342741)
                  ·
                    refine ⟨941321636153642351219191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20081528237944370159342741 941321636153642351219191)
                    ·
                      rfl

theorem cell22_2749826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2749826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749826 prefixEnd_2749826 := by exact prefixLift 2749826
  have htrace : WordTrace (prefixWord ++ tailWord_2749826) baseStart_2749826 baseEnd_2749826 := by
    simpa [prefixWord, tailWord_2749826, baseEnd_2749826] using wordTrace_append hprefix tailTrace_2749826
  have hstable : (prefixWord ++ tailWord_2749826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749826).length < 2 ^ (prefixWord ++ tailWord_2749826).sum := by decide
  have hdescent : baseEnd_2749826 < baseStart_2749826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749828 : List Nat := [2, 3, 2, 1, 1, 4, 3, 1, 2, 3]
def baseStart_2749828 : Nat := 118140960795 + 2749828 * 2 ^ 59
def prefixEnd_2749828 : Nat := 4983230072969 + 3 ^ 40 * 2749828 * 2
def baseEnd_2749828 : Nat := 941322320794515012669185

theorem tailTrace_2749828 : CollatzResearch.WordTrace tailWord_2749828 prefixEnd_2749828 941322320794515012669185 := by
  unfold tailWord_2749828
  simp only [CollatzResearch.WordTrace]
  refine ⟨50147233340925132039049069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66862977787900176052065425 50147233340925132039049069)
  ·
    refine ⟨18805212502846924514643401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50147233340925132039049069 18805212502846924514643401)
    ·
      refine ⟨14103909377135193385982551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18805212502846924514643401 14103909377135193385982551)
      ·
        refine ⟨21155864065702790078973827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14103909377135193385982551 21155864065702790078973827)
        ·
          refine ⟨31733796098554185118460741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21155864065702790078973827 31733796098554185118460741)
          ·
            refine ⟨5950086768478909709711389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31733796098554185118460741 5950086768478909709711389)
            ·
              refine ⟨2231282538179591141141771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5950086768478909709711389 2231282538179591141141771)
              ·
                refine ⟨3346923807269386711712657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2231282538179591141141771 3346923807269386711712657)
                ·
                  refine ⟨2510192855452040033784493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3346923807269386711712657 2510192855452040033784493)
                  ·
                    refine ⟨941322320794515012669185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2510192855452040033784493 941322320794515012669185)
                    ·
                      rfl

theorem cell22_2749828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_2749828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749828 prefixEnd_2749828 := by exact prefixLift 2749828
  have htrace : WordTrace (prefixWord ++ tailWord_2749828) baseStart_2749828 baseEnd_2749828 := by
    simpa [prefixWord, tailWord_2749828, baseEnd_2749828] using wordTrace_append hprefix tailTrace_2749828
  have hstable : (prefixWord ++ tailWord_2749828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749828).length < 2 ^ (prefixWord ++ tailWord_2749828).sum := by decide
  have hdescent : baseEnd_2749828 < baseStart_2749828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749882 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_2749882 : Nat := 118140960795 + 2749882 * 2 ^ 59
def prefixEnd_2749882 : Nat := 4983230072969 + 3 ^ 40 * 2749882 * 2
def baseEnd_2749882 : Nat := 941340806098076871819019

theorem tailTrace_2749882 : CollatzResearch.WordTrace tailWord_2749882 prefixEnd_2749882 941340806098076871819019 := by
  unfold tailWord_2749882
  simp only [CollatzResearch.WordTrace]
  refine ⟨25074109055913657825140975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66864290815769754200375933 25074109055913657825140975)
  ·
    refine ⟨37611163583870486737711463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25074109055913657825140975 37611163583870486737711463)
    ·
      refine ⟨56416745375805730106567195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37611163583870486737711463 56416745375805730106567195)
      ·
        refine ⟨84625118063708595159850793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56416745375805730106567195 84625118063708595159850793)
        ·
          refine ⟨63468838547781446369888095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84625118063708595159850793 63468838547781446369888095)
          ·
            refine ⟨95203257821672169554832143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63468838547781446369888095 95203257821672169554832143)
            ·
              refine ⟨142804886732508254332248215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95203257821672169554832143 142804886732508254332248215)
              ·
                refine ⟨214207330098762381498372323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142804886732508254332248215 214207330098762381498372323)
                ·
                  refine ⟨321310995148143572247558485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214207330098762381498372323 321310995148143572247558485)
                  ·
                    refine ⟨941340806098076871819019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 321310995148143572247558485 941340806098076871819019)
                    ·
                      rfl

theorem cell22_2749882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_2749882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749882 prefixEnd_2749882 := by exact prefixLift 2749882
  have htrace : WordTrace (prefixWord ++ tailWord_2749882) baseStart_2749882 baseEnd_2749882 := by
    simpa [prefixWord, tailWord_2749882, baseEnd_2749882] using wordTrace_append hprefix tailTrace_2749882
  have hstable : (prefixWord ++ tailWord_2749882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749882).length < 2 ^ (prefixWord ++ tailWord_2749882).sum := by decide
  have hdescent : baseEnd_2749882 < baseStart_2749882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749897 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 8]
def baseStart_2749897 : Nat := 118140960795 + 2749897 * 2 ^ 59
def prefixEnd_2749897 : Nat := 4983230072969 + 3 ^ 40 * 2749897 * 2
def baseEnd_2749897 : Nat := 313781980301540610897991

theorem tailTrace_2749897 : CollatzResearch.WordTrace tailWord_2749897 prefixEnd_2749897 313781980301540610897991 := by
  unfold tailWord_2749897
  simp only [CollatzResearch.WordTrace]
  refine ⟨100296983318600288862359945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66864655545733525908239963 100296983318600288862359945)
  ·
    refine ⟨75222737488950216646769959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100296983318600288862359945 75222737488950216646769959)
    ·
      refine ⟨112834106233425324970154939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75222737488950216646769959 112834106233425324970154939)
      ·
        refine ⟨169251159350137987455232409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112834106233425324970154939 169251159350137987455232409)
        ·
          refine ⟨126938369512603490591424307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169251159350137987455232409 126938369512603490591424307)
          ·
            refine ⟨190407554268905235887136461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126938369512603490591424307 190407554268905235887136461)
            ·
              refine ⟨71402832850839463457676173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190407554268905235887136461 71402832850839463457676173)
              ·
                refine ⟨26776062319064798796628565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71402832850839463457676173 26776062319064798796628565)
                ·
                  refine ⟨313781980301540610897991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26776062319064798796628565 313781980301540610897991)
                  ·
                    rfl

theorem cell22_2749897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 8].length) (baseStart_2749897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749897 prefixEnd_2749897 := by exact prefixLift 2749897
  have htrace : WordTrace (prefixWord ++ tailWord_2749897) baseStart_2749897 baseEnd_2749897 := by
    simpa [prefixWord, tailWord_2749897, baseEnd_2749897] using wordTrace_append hprefix tailTrace_2749897
  have hstable : (prefixWord ++ tailWord_2749897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749897).length < 2 ^ (prefixWord ++ tailWord_2749897).sum := by decide
  have hdescent : baseEnd_2749897 < baseStart_2749897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749929 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 8, 3]
def baseStart_2749929 : Nat := 118140960795 + 2749929 * 2 ^ 59
def prefixEnd_2749929 : Nat := 4983230072969 + 3 ^ 40 * 2749929 * 2
def baseEnd_2749929 : Nat := 941356895158584415893875

theorem tailTrace_2749929 : CollatzResearch.WordTrace tailWord_2749929 prefixEnd_2749929 941356895158584415893875 := by
  unfold tailWord_2749929
  simp only [CollatzResearch.WordTrace]
  refine ⟨100298150454484358327524841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66865433636322905551683227 100298150454484358327524841)
  ·
    refine ⟨75223612840863268745643631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100298150454484358327524841 75223612840863268745643631)
    ·
      refine ⟨112835419261294903118465447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75223612840863268745643631 112835419261294903118465447)
      ·
        refine ⟨169253128891942354677698171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112835419261294903118465447 169253128891942354677698171)
        ·
          refine ⟨253879693337913532016547257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169253128891942354677698171 253879693337913532016547257)
          ·
            refine ⟨190409770003435149012410443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253879693337913532016547257 190409770003435149012410443)
            ·
              refine ⟨285614655005152723518615665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190409770003435149012410443 285614655005152723518615665)
              ·
                refine ⟨214210991253864542638961749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285614655005152723518615665 214210991253864542638961749)
                ·
                  refine ⟨2510285053756225109050333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 214210991253864542638961749 2510285053756225109050333)
                  ·
                    refine ⟨941356895158584415893875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2510285053756225109050333 941356895158584415893875)
                    ·
                      rfl

theorem cell22_2749929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 3].length) (baseStart_2749929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749929 prefixEnd_2749929 := by exact prefixLift 2749929
  have htrace : WordTrace (prefixWord ++ tailWord_2749929) baseStart_2749929 baseEnd_2749929 := by
    simpa [prefixWord, tailWord_2749929, baseEnd_2749929] using wordTrace_append hprefix tailTrace_2749929
  have hstable : (prefixWord ++ tailWord_2749929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749929).length < 2 ^ (prefixWord ++ tailWord_2749929).sum := by decide
  have hdescent : baseEnd_2749929 < baseStart_2749929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749946 : List Nat := [3, 1, 1, 1, 1, 2, 3, 5, 2, 3]
def baseStart_2749946 : Nat := 118140960795 + 2749946 * 2 ^ 59
def prefixEnd_2749946 : Nat := 4983230072969 + 3 ^ 40 * 2749946 * 2
def baseEnd_2749946 : Nat := 941362714606002038218823

theorem tailTrace_2749946 : CollatzResearch.WordTrace tailWord_2749946 prefixEnd_2749946 941362714606002038218823 := by
  unfold tailWord_2749946
  simp only [CollatzResearch.WordTrace]
  refine ⟨25074692623855692557723423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66865846996948513487262461 25074692623855692557723423)
  ·
    refine ⟨37612038935783538836585135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25074692623855692557723423 37612038935783538836585135)
    ·
      refine ⟨56418058403675308254877703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37612038935783538836585135 56418058403675308254877703)
      ·
        refine ⟨84627087605512962382316555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56418058403675308254877703 84627087605512962382316555)
        ·
          refine ⟨126940631408269443573474833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84627087605512962382316555 126940631408269443573474833)
          ·
            refine ⟨95205473556202082680106125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126940631408269443573474833 95205473556202082680106125)
            ·
              refine ⟨35702052583575781005039797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95205473556202082680106125 35702052583575781005039797)
              ·
                refine ⟨3347067429710229469222481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35702052583575781005039797 3347067429710229469222481)
                ·
                  refine ⟨2510300572282672101916861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3347067429710229469222481 2510300572282672101916861)
                  ·
                    refine ⟨941362714606002038218823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2510300572282672101916861 941362714606002038218823)
                    ·
                      rfl

theorem cell22_2749946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_2749946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749946 prefixEnd_2749946 := by exact prefixLift 2749946
  have htrace : WordTrace (prefixWord ++ tailWord_2749946) baseStart_2749946 baseEnd_2749946 := by
    simpa [prefixWord, tailWord_2749946, baseEnd_2749946] using wordTrace_append hprefix tailTrace_2749946
  have hstable : (prefixWord ++ tailWord_2749946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749946).length < 2 ^ (prefixWord ++ tailWord_2749946).sum := by decide
  have hdescent : baseEnd_2749946 < baseStart_2749946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2749982 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 6]
def baseStart_2749982 : Nat := 118140960795 + 2749982 * 2 ^ 59
def prefixEnd_2749982 : Nat := 4983230072969 + 3 ^ 40 * 2749982 * 2
def baseEnd_2749982 : Nat := 313791679380569981439571

theorem tailTrace_2749982 : CollatzResearch.WordTrace tailWord_2749982 prefixEnd_2749982 313791679380569981439571 := by
  unfold tailWord_2749982
  simp only [CollatzResearch.WordTrace]
  refine ⟨12537510440411543547400525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66866722348861565586136133 12537510440411543547400525)
  ·
    refine ⟨4701566415154328830275197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12537510440411543547400525 4701566415154328830275197)
    ·
      refine ⟨1763087405682873311353199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4701566415154328830275197 1763087405682873311353199)
      ·
        refine ⟨2644631108524309967029799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1763087405682873311353199 2644631108524309967029799)
        ·
          refine ⟨3966946662786464950544699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2644631108524309967029799 3966946662786464950544699)
          ·
            refine ⟨5950419994179697425817049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3966946662786464950544699 5950419994179697425817049)
            ·
              refine ⟨4462814995634773069362787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5950419994179697425817049 4462814995634773069362787)
              ·
                refine ⟨6694222493452159604044181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462814995634773069362787 6694222493452159604044181)
                ·
                  refine ⟨313791679380569981439571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6694222493452159604044181 313791679380569981439571)
                  ·
                    rfl

theorem cell22_2749982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_2749982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2749982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2749982 prefixEnd_2749982 := by exact prefixLift 2749982
  have htrace : WordTrace (prefixWord ++ tailWord_2749982) baseStart_2749982 baseEnd_2749982 := by
    simpa [prefixWord, tailWord_2749982, baseEnd_2749982] using wordTrace_append hprefix tailTrace_2749982
  have hstable : (prefixWord ++ tailWord_2749982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2749982).length < 2 ^ (prefixWord ++ tailWord_2749982).sum := by decide
  have hdescent : baseEnd_2749982 < baseStart_2749982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2749982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750079 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 5, 6]
def baseStart_2750079 : Nat := 118140960795 + 2750079 * 2 ^ 59
def prefixEnd_2750079 : Nat := 4983230072969 + 3 ^ 40 * 2750079 * 2
def baseEnd_2750079 : Nat := 941408243224034024643415

theorem tailTrace_2750079 : CollatzResearch.WordTrace tailWord_2750079 prefixEnd_2750079 941408243224034024643415 := by
  unfold tailWord_2750079
  simp only [CollatzResearch.WordTrace]
  refine ⟨100303621403940933945485291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66869080935960622630323527 100303621403940933945485291)
  ·
    refine ⟨150455432105911400918227937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100303621403940933945485291 150455432105911400918227937)
    ·
      refine ⟨112841574079433550688670953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150455432105911400918227937 112841574079433550688670953)
      ·
        refine ⟨84631180559575163016503215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112841574079433550688670953 84631180559575163016503215)
        ·
          refine ⟨126946770839362744524754823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84631180559575163016503215 126946770839362744524754823)
          ·
            refine ⟨190420156259044116787132235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126946770839362744524754823 190420156259044116787132235)
            ·
              refine ⟨285630234388566175180698353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190420156259044116787132235 285630234388566175180698353)
              ·
                refine ⟨214222675791424631385523765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285630234388566175180698353 214222675791424631385523765)
                ·
                  refine ⟨20083375855446059192392853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 214222675791424631385523765 20083375855446059192392853)
                  ·
                    refine ⟨941408243224034024643415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20083375855446059192392853 941408243224034024643415)
                    ·
                      rfl

theorem cell22_2750079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_2750079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750079 prefixEnd_2750079 := by exact prefixLift 2750079
  have htrace : WordTrace (prefixWord ++ tailWord_2750079) baseStart_2750079 baseEnd_2750079 := by
    simpa [prefixWord, tailWord_2750079, baseEnd_2750079] using wordTrace_append hprefix tailTrace_2750079
  have hstable : (prefixWord ++ tailWord_2750079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750079).length < 2 ^ (prefixWord ++ tailWord_2750079).sum := by decide
  have hdescent : baseEnd_2750079 < baseStart_2750079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750081 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2750081 : Nat := 118140960795 + 2750081 * 2 ^ 59
def prefixEnd_2750081 : Nat := 4983230072969 + 3 ^ 40 * 2750081 * 2
def baseEnd_2750081 : Nat := 941408927864906686093409

theorem tailTrace_2750081 : CollatzResearch.WordTrace tailWord_2750081 prefixEnd_2750081 941408927864906686093409 := by
  unfold tailWord_2750081
  simp only [CollatzResearch.WordTrace]
  refine ⟨100303694349933688287058097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66869129566622458858038731 100303694349933688287058097)
  ·
    refine ⟨75227770762450266215293573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100303694349933688287058097 75227770762450266215293573)
    ·
      refine ⟨14105207017959424915367545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75227770762450266215293573 14105207017959424915367545)
      ·
        refine ⟨10578905263469568686525659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14105207017959424915367545 10578905263469568686525659)
        ·
          refine ⟨15868357895204353029788489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10578905263469568686525659 15868357895204353029788489)
          ·
            refine ⟨11901268421403264772341367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15868357895204353029788489 11901268421403264772341367)
            ·
              refine ⟨17851902632104897158512051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11901268421403264772341367 17851902632104897158512051)
              ·
                refine ⟨26777853948157345737768077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17851902632104897158512051 26777853948157345737768077)
                ·
                  refine ⟨10041695230559004651663029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26777853948157345737768077 10041695230559004651663029)
                  ·
                    refine ⟨941408927864906686093409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10041695230559004651663029 941408927864906686093409)
                    ·
                      rfl

theorem cell22_2750081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2750081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750081 prefixEnd_2750081 := by exact prefixLift 2750081
  have htrace : WordTrace (prefixWord ++ tailWord_2750081) baseStart_2750081 baseEnd_2750081 := by
    simpa [prefixWord, tailWord_2750081, baseEnd_2750081] using wordTrace_append hprefix tailTrace_2750081
  have hstable : (prefixWord ++ tailWord_2750081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750081).length < 2 ^ (prefixWord ++ tailWord_2750081).sum := by decide
  have hdescent : baseEnd_2750081 < baseStart_2750081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750166 : List Nat := [5, 2, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_2750166 : Nat := 118140960795 + 2750166 * 2 ^ 59
def prefixEnd_2750166 : Nat := 4983230072969 + 3 ^ 40 * 2750166 * 2
def baseEnd_2750166 : Nat := 941438025101994797718149

theorem tailTrace_2750166 : CollatzResearch.WordTrace tailWord_2750166 prefixEnd_2750166 941438025101994797718149 := by
  unfold tailWord_2750166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6269174659664109237743897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66871196369750498535934901 6269174659664109237743897)
  ·
    refine ⟨4701880994748081928307923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6269174659664109237743897 4701880994748081928307923)
    ·
      refine ⟨7052821492122122892461885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4701880994748081928307923 7052821492122122892461885)
      ·
        refine ⟨2644808059545796084673207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7052821492122122892461885 2644808059545796084673207)
        ·
          refine ⟨3967212089318694127009811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2644808059545796084673207 3967212089318694127009811)
          ·
            refine ⟨5950818133978041190514717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3967212089318694127009811 5950818133978041190514717)
            ·
              refine ⟨2231556800241765446443019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5950818133978041190514717 2231556800241765446443019)
              ·
                refine ⟨3347335200362648169664529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2231556800241765446443019 3347335200362648169664529)
                ·
                  refine ⟨2510501400271986127248397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3347335200362648169664529 2510501400271986127248397)
                  ·
                    refine ⟨941438025101994797718149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2510501400271986127248397 941438025101994797718149)
                    ·
                      rfl

theorem cell22_2750166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_2750166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750166 prefixEnd_2750166 := by exact prefixLift 2750166
  have htrace : WordTrace (prefixWord ++ tailWord_2750166) baseStart_2750166 baseEnd_2750166 := by
    simpa [prefixWord, tailWord_2750166, baseEnd_2750166] using wordTrace_append hprefix tailTrace_2750166
  have hstable : (prefixWord ++ tailWord_2750166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750166).length < 2 ^ (prefixWord ++ tailWord_2750166).sum := by decide
  have hdescent : baseEnd_2750166 < baseStart_2750166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750218 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 6]
def baseStart_2750218 : Nat := 118140960795 + 2750218 * 2 ^ 59
def prefixEnd_2750218 : Nat := 4983230072969 + 3 ^ 40 * 2750218 * 2
def baseEnd_2750218 : Nat := 313818608588227998472663

theorem tailTrace_2750218 : CollatzResearch.WordTrace tailWord_2750218 prefixEnd_2750218 313818608588227998472663 := by
  unfold tailWord_2750218
  simp only [CollatzResearch.WordTrace]
  refine ⟨25077172787609340171198827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66872460766958240456530205 25077172787609340171198827)
  ·
    refine ⟨37615759181414010256798241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25077172787609340171198827 37615759181414010256798241)
    ·
      refine ⟨28211819386060507692598681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37615759181414010256798241 28211819386060507692598681)
      ·
        refine ⟨21158864539545380769449011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28211819386060507692598681 21158864539545380769449011)
        ·
          refine ⟨31738296809318071154173517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21158864539545380769449011 31738296809318071154173517)
          ·
            refine ⟨11901861303494276682815069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31738296809318071154173517 11901861303494276682815069)
            ·
              refine ⟨4463197988810353756055651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11901861303494276682815069 4463197988810353756055651)
              ·
                refine ⟨6694796983215530634083477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4463197988810353756055651 6694796983215530634083477)
                ·
                  refine ⟨313818608588227998472663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6694796983215530634083477 313818608588227998472663)
                  ·
                    rfl

theorem cell22_2750218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_2750218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750218 prefixEnd_2750218 := by exact prefixLift 2750218
  have htrace : WordTrace (prefixWord ++ tailWord_2750218) baseStart_2750218 baseEnd_2750218 := by
    simpa [prefixWord, tailWord_2750218, baseEnd_2750218] using wordTrace_append hprefix tailTrace_2750218
  have hstable : (prefixWord ++ tailWord_2750218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750218).length < 2 ^ (prefixWord ++ tailWord_2750218).sum := by decide
  have hdescent : baseEnd_2750218 < baseStart_2750218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750254 : List Nat := [4, 1, 3, 2, 2, 1, 3, 1, 1, 4]
def baseStart_2750254 : Nat := 118140960795 + 2750254 * 2 ^ 59
def prefixEnd_2750254 : Nat := 4983230072969 + 3 ^ 40 * 2750254 * 2
def baseEnd_2750254 : Nat := 941468149300391901517879

theorem tailTrace_2750254 : CollatzResearch.WordTrace tailWord_2750254 prefixEnd_2750254 941468149300391901517879 := by
  unfold tailWord_2750254
  simp only [CollatzResearch.WordTrace]
  refine ⟨12538750522288367354138227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66873336118871292555403877 12538750522288367354138227)
  ·
    refine ⟨18808125783432551031207341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12538750522288367354138227 18808125783432551031207341)
    ·
      refine ⟨7053047168787206636702753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18808125783432551031207341 7053047168787206636702753)
      ·
        refine ⟨5289785376590404977527065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7053047168787206636702753 5289785376590404977527065)
        ·
          refine ⟨3967339032442803733145299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5289785376590404977527065 3967339032442803733145299)
          ·
            refine ⟨5951008548664205599717949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3967339032442803733145299 5951008548664205599717949)
            ·
              refine ⟨2231628205749077099894231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5951008548664205599717949 2231628205749077099894231)
              ·
                refine ⟨3347442308623615649841347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2231628205749077099894231 3347442308623615649841347)
                ·
                  refine ⟨5021163462935423474762021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3347442308623615649841347 5021163462935423474762021)
                  ·
                    refine ⟨941468149300391901517879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5021163462935423474762021 941468149300391901517879)
                    ·
                      rfl

theorem cell22_2750254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_2750254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750254 prefixEnd_2750254 := by exact prefixLift 2750254
  have htrace : WordTrace (prefixWord ++ tailWord_2750254) baseStart_2750254 baseEnd_2750254 := by
    simpa [prefixWord, tailWord_2750254, baseEnd_2750254] using wordTrace_append hprefix tailTrace_2750254
  have hstable : (prefixWord ++ tailWord_2750254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750254).length < 2 ^ (prefixWord ++ tailWord_2750254).sum := by decide
  have hdescent : baseEnd_2750254 < baseStart_2750254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750269 : List Nat := [1, 4, 1, 4, 1, 3, 2, 2, 4]
def baseStart_2750269 : Nat := 118140960795 + 2750269 * 2 ^ 59
def prefixEnd_2750269 : Nat := 4983230072969 + 3 ^ 40 * 2750269 * 2
def baseEnd_2750269 : Nat := 313824428035645620797611

theorem tailTrace_2750269 : CollatzResearch.WordTrace tailWord_2750269 prefixEnd_2750269 313824428035645620797611 := by
  unfold tailWord_2750269
  simp only [CollatzResearch.WordTrace]
  refine ⟨100310551273252596394901861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66873700848835064263267907 100310551273252596394901861)
  ·
    refine ⟨18808228363734861824044099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100310551273252596394901861 18808228363734861824044099)
    ·
      refine ⟨28212342545602292736066149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18808228363734861824044099 28212342545602292736066149)
      ·
        refine ⟨5289814227300429888012403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28212342545602292736066149 5289814227300429888012403)
        ·
          refine ⟨7934721340950644832018605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5289814227300429888012403 7934721340950644832018605)
          ·
            refine ⟨2975520502856491812006977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7934721340950644832018605 2975520502856491812006977)
            ·
              refine ⟨2231640377142368859005233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2975520502856491812006977 2231640377142368859005233)
              ·
                refine ⟨1673730282856776644253925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2231640377142368859005233 1673730282856776644253925)
                ·
                  refine ⟨313824428035645620797611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1673730282856776644253925 313824428035645620797611)
                  ·
                    rfl

theorem cell22_2750269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_2750269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750269 prefixEnd_2750269 := by exact prefixLift 2750269
  have htrace : WordTrace (prefixWord ++ tailWord_2750269) baseStart_2750269 baseEnd_2750269 := by
    simpa [prefixWord, tailWord_2750269, baseEnd_2750269] using wordTrace_append hprefix tailTrace_2750269
  have hstable : (prefixWord ++ tailWord_2750269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750269).length < 2 ^ (prefixWord ++ tailWord_2750269).sum := by decide
  have hdescent : baseEnd_2750269 < baseStart_2750269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750291 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 11]
def baseStart_2750291 : Nat := 118140960795 + 2750291 * 2 ^ 59
def prefixEnd_2750291 : Nat := 4983230072969 + 3 ^ 40 * 2750291 * 2
def baseEnd_2750291 : Nat := 313826938385512046114255

theorem tailTrace_2750291 : CollatzResearch.WordTrace tailWord_2750291 prefixEnd_2750291 313826938385512046114255 := by
  unfold tailWord_2750291
  simp only [CollatzResearch.WordTrace]
  refine ⟨100311353679172894152202727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66874235786115262768135151 100311353679172894152202727)
  ·
    refine ⟨150467030518759341228304091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100311353679172894152202727 150467030518759341228304091)
    ·
      refine ⟨225700545778139011842456137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150467030518759341228304091 225700545778139011842456137)
      ·
        refine ⟨169275409333604258881842103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225700545778139011842456137 169275409333604258881842103)
        ·
          refine ⟨253913114000406388322763155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169275409333604258881842103 253913114000406388322763155)
          ·
            refine ⟨380869671000609582484144733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253913114000406388322763155 380869671000609582484144733)
            ·
              refine ⟨142826126625228593431554275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380869671000609582484144733 142826126625228593431554275)
              ·
                refine ⟨214239189937842890147331413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142826126625228593431554275 214239189937842890147331413)
                ·
                  refine ⟨313826938385512046114255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 214239189937842890147331413 313826938385512046114255)
                  ·
                    rfl

theorem cell22_2750291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 11].length) (baseStart_2750291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750291 prefixEnd_2750291 := by exact prefixLift 2750291
  have htrace : WordTrace (prefixWord ++ tailWord_2750291) baseStart_2750291 baseEnd_2750291 := by
    simpa [prefixWord, tailWord_2750291, baseEnd_2750291] using wordTrace_append hprefix tailTrace_2750291
  have hstable : (prefixWord ++ tailWord_2750291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750291).length < 2 ^ (prefixWord ++ tailWord_2750291).sum := by decide
  have hdescent : baseEnd_2750291 < baseStart_2750291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750353 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 6]
def baseStart_2750353 : Nat := 118140960795 + 2750353 * 2 ^ 59
def prefixEnd_2750353 : Nat := 4983230072969 + 3 ^ 40 * 2750353 * 2
def baseEnd_2750353 : Nat := 313834013007862881097525

theorem tailTrace_2750353 : CollatzResearch.WordTrace tailWord_2750353 prefixEnd_2750353 313834013007862881097525 := by
  unfold tailWord_2750353
  simp only [CollatzResearch.WordTrace]
  refine ⟨100313615004948278740959713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66875743336632185827306475 100313615004948278740959713)
  ·
    refine ⟨75235211253711209055719785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100313615004948278740959713 75235211253711209055719785)
    ·
      refine ⟨56426408440283406791789839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75235211253711209055719785 56426408440283406791789839)
      ·
        refine ⟨84639612660425110187684759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56426408440283406791789839 84639612660425110187684759)
        ·
          refine ⟨126959418990637665281527139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84639612660425110187684759 126959418990637665281527139)
          ·
            refine ⟨190439128485956497922290709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126959418990637665281527139 190439128485956497922290709)
            ·
              refine ⟨8926834147779210840107377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 190439128485956497922290709 8926834147779210840107377)
              ·
                refine ⟨6695125610834408130080533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8926834147779210840107377 6695125610834408130080533)
                ·
                  refine ⟨313834013007862881097525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6695125610834408130080533 313834013007862881097525)
                  ·
                    rfl

theorem cell22_2750353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 6].length) (baseStart_2750353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750353 prefixEnd_2750353 := by exact prefixLift 2750353
  have htrace : WordTrace (prefixWord ++ tailWord_2750353) baseStart_2750353 baseEnd_2750353 := by
    simpa [prefixWord, tailWord_2750353, baseEnd_2750353] using wordTrace_append hprefix tailTrace_2750353
  have hstable : (prefixWord ++ tailWord_2750353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750353).length < 2 ^ (prefixWord ++ tailWord_2750353).sum := by decide
  have hdescent : baseEnd_2750353 < baseStart_2750353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750368 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 3, 5]
def baseStart_2750368 : Nat := 118140960795 + 2750368 * 2 ^ 59
def prefixEnd_2750368 : Nat := 4983230072969 + 3 ^ 40 * 2750368 * 2
def baseEnd_2750368 : Nat := 941507173830133604167529

theorem tailTrace_2750368 : CollatzResearch.WordTrace tailWord_2750368 prefixEnd_2750368 941507173830133604167529 := by
  unfold tailWord_2750368
  simp only [CollatzResearch.WordTrace]
  refine ⟨50157081049946968151377879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66876108066595957535170505 50157081049946968151377879)
  ·
    refine ⟨75235621574920452227066819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50157081049946968151377879 75235621574920452227066819)
    ·
      refine ⟨112853432362380678340600229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75235621574920452227066819 112853432362380678340600229)
      ·
        refine ⟨21160018567946377188862543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112853432362380678340600229 21160018567946377188862543)
        ·
          refine ⟨31740027851919565783293815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21160018567946377188862543 31740027851919565783293815)
          ·
            refine ⟨47610041777879348674940723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31740027851919565783293815 47610041777879348674940723)
            ·
              refine ⟨71415062666819023012411085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47610041777879348674940723 71415062666819023012411085)
              ·
                refine ⟨26780648500057133629654157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71415062666819023012411085 26780648500057133629654157)
                ·
                  refine ⟨10042743187521425111120309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26780648500057133629654157 10042743187521425111120309)
                  ·
                    refine ⟨941507173830133604167529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10042743187521425111120309 941507173830133604167529)
                    ·
                      rfl

theorem cell22_2750368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_2750368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750368 prefixEnd_2750368 := by exact prefixLift 2750368
  have htrace : WordTrace (prefixWord ++ tailWord_2750368) baseStart_2750368 baseEnd_2750368 := by
    simpa [prefixWord, tailWord_2750368, baseEnd_2750368] using wordTrace_append hprefix tailTrace_2750368
  have hstable : (prefixWord ++ tailWord_2750368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750368).length < 2 ^ (prefixWord ++ tailWord_2750368).sum := by decide
  have hdescent : baseEnd_2750368 < baseStart_2750368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750387 : List Nat := [1, 1, 1, 2, 3, 1, 7, 2, 4]
def baseStart_2750387 : Nat := 118140960795 + 2750387 * 2 ^ 59
def prefixEnd_2750387 : Nat := 4983230072969 + 3 ^ 40 * 2750387 * 2
def baseEnd_2750387 : Nat := 313837892639474629314157

theorem tailTrace_2750387 : CollatzResearch.WordTrace tailWord_2750387 prefixEnd_2750387 313837892639474629314157 := by
  unfold tailWord_2750387
  simp only [CollatzResearch.WordTrace]
  refine ⟨100314855086825102547697415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66876570057883401698464943 100314855086825102547697415)
  ·
    refine ⟨150472282630237653821546123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100314855086825102547697415 150472282630237653821546123)
    ·
      refine ⟨225708423945356480732319185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150472282630237653821546123 225708423945356480732319185)
      ·
        refine ⟨169281317959017360549239389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225708423945356480732319185 169281317959017360549239389)
        ·
          refine ⟨63480494234631510205964771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169281317959017360549239389 63480494234631510205964771)
          ·
            refine ⟨95220741351947265308947157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63480494234631510205964771 95220741351947265308947157)
            ·
              refine ⟨2231736125436264030678449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 95220741351947265308947157 2231736125436264030678449)
              ·
                refine ⟨1673802094077198023008837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2231736125436264030678449 1673802094077198023008837)
                ·
                  refine ⟨313837892639474629314157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1673802094077198023008837 313837892639474629314157)
                  ·
                    rfl

theorem cell22_2750387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 4].length) (baseStart_2750387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750387 prefixEnd_2750387 := by exact prefixLift 2750387
  have htrace : WordTrace (prefixWord ++ tailWord_2750387) baseStart_2750387 baseEnd_2750387 := by
    simpa [prefixWord, tailWord_2750387, baseEnd_2750387] using wordTrace_append hprefix tailTrace_2750387
  have hstable : (prefixWord ++ tailWord_2750387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750387).length < 2 ^ (prefixWord ++ tailWord_2750387).sum := by decide
  have hdescent : baseEnd_2750387 < baseStart_2750387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750443 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 7]
def baseStart_2750443 : Nat := 118140960795 + 2750443 * 2 ^ 59
def prefixEnd_2750443 : Nat := 4983230072969 + 3 ^ 40 * 2750443 * 2
def baseEnd_2750443 : Nat := 313844282620952802847433

theorem tailTrace_2750443 : CollatzResearch.WordTrace tailWord_2750443 prefixEnd_2750443 313844282620952802847433 := by
  unfold tailWord_2750443
  simp only [CollatzResearch.WordTrace]
  refine ⟨100316897574622224111735983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66877931716414816074490655 100316897574622224111735983)
  ·
    refine ⟨150475346361933336167603975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100316897574622224111735983 150475346361933336167603975)
    ·
      refine ⟨225713019542900004251405963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150475346361933336167603975 225713019542900004251405963)
      ·
        refine ⟨338569529314350006377108945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225713019542900004251405963 338569529314350006377108945)
        ·
          refine ⟨253927146985762504782831709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338569529314350006377108945 253927146985762504782831709)
          ·
            refine ⟨95222680119660939293561891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253927146985762504782831709 95222680119660939293561891)
            ·
              refine ⟨142834020179491408940342837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95222680119660939293561891 142834020179491408940342837)
              ·
                refine ⟨13390689391827319588157141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142834020179491408940342837 13390689391827319588157141)
                ·
                  refine ⟨313844282620952802847433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13390689391827319588157141 313844282620952802847433)
                  ·
                    rfl

theorem cell22_2750443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 7].length) (baseStart_2750443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750443 prefixEnd_2750443 := by exact prefixLift 2750443
  have htrace : WordTrace (prefixWord ++ tailWord_2750443) baseStart_2750443 baseEnd_2750443 := by
    simpa [prefixWord, tailWord_2750443, baseEnd_2750443] using wordTrace_append hprefix tailTrace_2750443
  have hstable : (prefixWord ++ tailWord_2750443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750443).length < 2 ^ (prefixWord ++ tailWord_2750443).sum := by decide
  have hdescent : baseEnd_2750443 < baseStart_2750443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750460 : List Nat := [2, 2, 2, 1, 2, 2, 1, 5, 5]
def baseStart_2750460 : Nat := 118140960795 + 2750460 * 2 ^ 59
def prefixEnd_2750460 : Nat := 4983230072969 + 3 ^ 40 * 2750460 * 2
def baseEnd_2750460 : Nat := 313846222436758676955749

theorem tailTrace_2750460 : CollatzResearch.WordTrace tailWord_2750460 prefixEnd_2750460 313846222436758676955749 := by
  unfold tailWord_2750460
  simp only [CollatzResearch.WordTrace]
  refine ⟨50158758807780318007552417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66878345077040424010069889 50158758807780318007552417)
  ·
    refine ⟨37619069105835238505664313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50158758807780318007552417 37619069105835238505664313)
    ·
      refine ⟨28214301829376428879248235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37619069105835238505664313 28214301829376428879248235)
      ·
        refine ⟨42321452744064643318872353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28214301829376428879248235 42321452744064643318872353)
        ·
          refine ⟨31741089558048482489154265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42321452744064643318872353 31741089558048482489154265)
          ·
            refine ⟨23805817168536361866865699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31741089558048482489154265 23805817168536361866865699)
            ·
              refine ⟨35708725752804542800298549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23805817168536361866865699 35708725752804542800298549)
              ·
                refine ⟨3347693039325425887527989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35708725752804542800298549 3347693039325425887527989)
                ·
                  refine ⟨313846222436758676955749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3347693039325425887527989 313846222436758676955749)
                  ·
                    rfl

theorem cell22_2750460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_2750460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750460 prefixEnd_2750460 := by exact prefixLift 2750460
  have htrace : WordTrace (prefixWord ++ tailWord_2750460) baseStart_2750460 baseEnd_2750460 := by
    simpa [prefixWord, tailWord_2750460, baseEnd_2750460] using wordTrace_append hprefix tailTrace_2750460
  have hstable : (prefixWord ++ tailWord_2750460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750460).length < 2 ^ (prefixWord ++ tailWord_2750460).sum := by decide
  have hdescent : baseEnd_2750460 < baseStart_2750460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750535 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 1, 6]
def baseStart_2750535 : Nat := 118140960795 + 2750535 * 2 ^ 59
def prefixEnd_2750535 : Nat := 4983230072969 + 3 ^ 40 * 2750535 * 2
def baseEnd_2750535 : Nat := 941564341343000835242017

theorem tailTrace_2750535 : CollatzResearch.WordTrace tailWord_2750535 prefixEnd_2750535 941564341343000835242017 := by
  unfold tailWord_2750535
  simp only [CollatzResearch.WordTrace]
  refine ⟨100320253090288923824085059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66880168726859282549390039 100320253090288923824085059)
  ·
    refine ⟨150480379635433385736127589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100320253090288923824085059 150480379635433385736127589)
    ·
      refine ⟨28215071181643759825523923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150480379635433385736127589 28215071181643759825523923)
      ·
        refine ⟨42322606772465639738285885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28215071181643759825523923 42322606772465639738285885)
        ·
          refine ⟨15870977539674614901857207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42322606772465639738285885 15870977539674614901857207)
          ·
            refine ⟨23806466309511922352785811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15870977539674614901857207 23806466309511922352785811)
            ·
              refine ⟨35709699464267883529178717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23806466309511922352785811 35709699464267883529178717)
              ·
                refine ⟨13391137299100456323442019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35709699464267883529178717 13391137299100456323442019)
                ·
                  refine ⟨20086705948650684485163029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13391137299100456323442019 20086705948650684485163029)
                  ·
                    refine ⟨941564341343000835242017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20086705948650684485163029 941564341343000835242017)
                    ·
                      rfl

theorem cell22_2750535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_2750535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750535 prefixEnd_2750535 := by exact prefixLift 2750535
  have htrace : WordTrace (prefixWord ++ tailWord_2750535) baseStart_2750535 baseEnd_2750535 := by
    simpa [prefixWord, tailWord_2750535, baseEnd_2750535] using wordTrace_append hprefix tailTrace_2750535
  have hstable : (prefixWord ++ tailWord_2750535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750535).length < 2 ^ (prefixWord ++ tailWord_2750535).sum := by decide
  have hdescent : baseEnd_2750535 < baseStart_2750535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750552 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 2, 4]
def baseStart_2750552 : Nat := 118140960795 + 2750552 * 2 ^ 59
def prefixEnd_2750552 : Nat := 4983230072969 + 3 ^ 40 * 2750552 * 2
def baseEnd_2750552 : Nat := 941570160790418457566965

theorem tailTrace_2750552 : CollatzResearch.WordTrace tailWord_2750552 prefixEnd_2750552 941570160790418457566965 := by
  unfold tailWord_2750552
  simp only [CollatzResearch.WordTrace]
  refine ⟨50160436565613667863726955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66880582087484890484969273 50160436565613667863726955)
  ·
    refine ⟨75240654848420501795590433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50160436565613667863726955 75240654848420501795590433)
    ·
      refine ⟨56430491136315376346692825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75240654848420501795590433 56430491136315376346692825)
      ·
        refine ⟨42322868352236532260019619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56430491136315376346692825 42322868352236532260019619)
        ·
          refine ⟨63484302528354798390029429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42322868352236532260019619 63484302528354798390029429)
          ·
            refine ⟨5951653362033262349065259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63484302528354798390029429 5951653362033262349065259)
            ·
              refine ⟨8927480043049893523597889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5951653362033262349065259 8927480043049893523597889)
              ·
                refine ⟨6695610032287420142698417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8927480043049893523597889 6695610032287420142698417)
                ·
                  refine ⟨5021707524215565107023813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6695610032287420142698417 5021707524215565107023813)
                  ·
                    refine ⟨941570160790418457566965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5021707524215565107023813 941570160790418457566965)
                    ·
                      rfl

theorem cell22_2750552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_2750552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750552 prefixEnd_2750552 := by exact prefixLift 2750552
  have htrace : WordTrace (prefixWord ++ tailWord_2750552) baseStart_2750552 baseEnd_2750552 := by
    simpa [prefixWord, tailWord_2750552, baseEnd_2750552] using wordTrace_append hprefix tailTrace_2750552
  have hstable : (prefixWord ++ tailWord_2750552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750552).length < 2 ^ (prefixWord ++ tailWord_2750552).sum := by decide
  have hdescent : baseEnd_2750552 < baseStart_2750552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750556 : List Nat := [2, 2, 4, 1, 1, 3, 3, 2, 4]
def baseStart_2750556 : Nat := 118140960795 + 2750556 * 2 ^ 59
def prefixEnd_2750556 : Nat := 4983230072969 + 3 ^ 40 * 2750556 * 2
def baseEnd_2750556 : Nat := 313857176690721260155651

theorem tailTrace_2750556 : CollatzResearch.WordTrace tailWord_2750556 prefixEnd_2750556 313857176690721260155651 := by
  unfold tailWord_2750556
  simp only [CollatzResearch.WordTrace]
  refine ⟨50160509511606422205299761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66880679348808562940399681 50160509511606422205299761)
  ·
    refine ⟨37620382133704816653974821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50160509511606422205299761 37620382133704816653974821)
    ·
      refine ⟨7053821650069653122620279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37620382133704816653974821 7053821650069653122620279)
      ·
        refine ⟨10580732475104479683930419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7053821650069653122620279 10580732475104479683930419)
        ·
          refine ⟨15871098712656719525895629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10580732475104479683930419 15871098712656719525895629)
          ·
            refine ⟨5951662017246269822210861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15871098712656719525895629 5951662017246269822210861)
            ·
              refine ⟨2231873256467351183329073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5951662017246269822210861 2231873256467351183329073)
              ·
                refine ⟨1673904942350513387496805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2231873256467351183329073 1673904942350513387496805)
                ·
                  refine ⟨313857176690721260155651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1673904942350513387496805 313857176690721260155651)
                  ·
                    rfl

theorem cell22_2750556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_2750556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750556 prefixEnd_2750556 := by exact prefixLift 2750556
  have htrace : WordTrace (prefixWord ++ tailWord_2750556) baseStart_2750556 baseEnd_2750556 := by
    simpa [prefixWord, tailWord_2750556, baseEnd_2750556] using wordTrace_append hprefix tailTrace_2750556
  have hstable : (prefixWord ++ tailWord_2750556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750556).length < 2 ^ (prefixWord ++ tailWord_2750556).sum := by decide
  have hdescent : baseEnd_2750556 < baseStart_2750556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750642 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_2750642 : Nat := 118140960795 + 2750642 * 2 ^ 59
def prefixEnd_2750642 : Nat := 4983230072969 + 3 ^ 40 * 2750642 * 2
def baseEnd_2750642 : Nat := 941600969629688222816689

theorem tailTrace_2750642 : CollatzResearch.WordTrace tailWord_2750642 prefixEnd_2750642 941600969629688222816689 := by
  unfold tailWord_2750642
  simp only [CollatzResearch.WordTrace]
  refine ⟨25081038925225320274557545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66882770467267520732153453 25081038925225320274557545)
  ·
    refine ⟨18810779193918990205918159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25081038925225320274557545 18810779193918990205918159)
    ·
      refine ⟨28216168790878485308877239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18810779193918990205918159 28216168790878485308877239)
      ·
        refine ⟨42324253186317727963315859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28216168790878485308877239 42324253186317727963315859)
        ·
          refine ⟨63486379779476591944973789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42324253186317727963315859 63486379779476591944973789)
          ·
            refine ⟨23807392417303721979365171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63486379779476591944973789 23807392417303721979365171)
            ·
              refine ⟨35711088625955582969047757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23807392417303721979365171 35711088625955582969047757)
              ·
                refine ⟨13391658234733343613392909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35711088625955582969047757 13391658234733343613392909)
                ·
                  refine ⟨5021871838025003855022341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13391658234733343613392909 5021871838025003855022341)
                  ·
                    refine ⟨941600969629688222816689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5021871838025003855022341 941600969629688222816689)
                    ·
                      rfl

theorem cell22_2750642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_2750642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750642 prefixEnd_2750642 := by exact prefixLift 2750642
  have htrace : WordTrace (prefixWord ++ tailWord_2750642) baseStart_2750642 baseEnd_2750642 := by
    simpa [prefixWord, tailWord_2750642, baseEnd_2750642] using wordTrace_append hprefix tailTrace_2750642
  have hstable : (prefixWord ++ tailWord_2750642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750642).length < 2 ^ (prefixWord ++ tailWord_2750642).sum := by decide
  have hdescent : baseEnd_2750642 < baseStart_2750642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750674 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 6]
def baseStart_2750674 : Nat := 118140960795 + 2750674 * 2 ^ 59
def prefixEnd_2750674 : Nat := 4983230072969 + 3 ^ 40 * 2750674 * 2
def baseEnd_2750674 : Nat := 313870641294550268672197

theorem tailTrace_2750674 : CollatzResearch.WordTrace tailWord_2750674 prefixEnd_2750674 313870641294550268672197 := by
  unfold tailWord_2750674
  simp only [CollatzResearch.WordTrace]
  refine ⟨25081330709196337640848769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66883548557856900375596717 25081330709196337640848769)
  ·
    refine ⟨18810998031897253230636577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25081330709196337640848769 18810998031897253230636577)
    ·
      refine ⟨14108248523922939922977433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18810998031897253230636577 14108248523922939922977433)
      ·
        refine ⟨10581186392942204942233075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14108248523922939922977433 10581186392942204942233075)
        ·
          refine ⟨15871779589413307413349613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10581186392942204942233075 15871779589413307413349613)
          ·
            refine ⟨5951917346029990280006105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15871779589413307413349613 5951917346029990280006105)
            ·
              refine ⟨4463938009522492710004579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5951917346029990280006105 4463938009522492710004579)
              ·
                refine ⟨6695907014283739065006869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4463938009522492710004579 6695907014283739065006869)
                ·
                  refine ⟨313870641294550268672197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6695907014283739065006869 313870641294550268672197)
                  ·
                    rfl

theorem cell22_2750674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_2750674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750674 prefixEnd_2750674 := by exact prefixLift 2750674
  have htrace : WordTrace (prefixWord ++ tailWord_2750674) baseStart_2750674 baseEnd_2750674 := by
    simpa [prefixWord, tailWord_2750674, baseEnd_2750674] using wordTrace_append hprefix tailTrace_2750674
  have hstable : (prefixWord ++ tailWord_2750674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750674).length < 2 ^ (prefixWord ++ tailWord_2750674).sum := by decide
  have hdescent : baseEnd_2750674 < baseStart_2750674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750732 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_2750732 : Nat := 118140960795 + 2750732 * 2 ^ 59
def prefixEnd_2750732 : Nat := 4983230072969 + 3 ^ 40 * 2750732 * 2
def baseEnd_2750732 : Nat := 941631778468957988066413

theorem tailTrace_2750732 : CollatzResearch.WordTrace tailWord_2750732 prefixEnd_2750732 941631778468957988066413 := by
  unfold tailWord_2750732
  simp only [CollatzResearch.WordTrace]
  refine ⟨50163719135287613234503225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66884958847050150979337633 50163719135287613234503225)
  ·
    refine ⟨37622789351465709925877419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50163719135287613234503225 37622789351465709925877419)
    ·
      refine ⟨56434184027198564888816129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37622789351465709925877419 56434184027198564888816129)
      ·
        refine ⟨42325638020398923666612097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56434184027198564888816129 42325638020398923666612097)
        ·
          refine ⟨31744228515299192749959073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42325638020398923666612097 31744228515299192749959073)
          ·
            refine ⟨23808171386474394562469305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31744228515299192749959073 23808171386474394562469305)
            ·
              refine ⟨17856128539855795921851979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23808171386474394562469305 17856128539855795921851979)
              ·
                refine ⟨26784192809783693882777969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17856128539855795921851979 26784192809783693882777969)
                ·
                  refine ⟨20088144607337770412083477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26784192809783693882777969 20088144607337770412083477)
                  ·
                    refine ⟨941631778468957988066413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20088144607337770412083477 941631778468957988066413)
                    ·
                      rfl

theorem cell22_2750732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_2750732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750732 prefixEnd_2750732 := by exact prefixLift 2750732
  have htrace : WordTrace (prefixWord ++ tailWord_2750732) baseStart_2750732 baseEnd_2750732 := by
    simpa [prefixWord, tailWord_2750732, baseEnd_2750732] using wordTrace_append hprefix tailTrace_2750732
  have hstable : (prefixWord ++ tailWord_2750732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750732).length < 2 ^ (prefixWord ++ tailWord_2750732).sum := by decide
  have hdescent : baseEnd_2750732 < baseStart_2750732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750785 : List Nat := [1, 2, 5, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2750785 : Nat := 118140960795 + 2750785 * 2 ^ 59
def prefixEnd_2750785 : Nat := 4983230072969 + 3 ^ 40 * 2750785 * 2
def baseEnd_2750785 : Nat := 941649921452083516491251

theorem tailTrace_2750785 : CollatzResearch.WordTrace tailWord_2750785 prefixEnd_2750785 941649921452083516491251 := by
  unfold tailWord_2750785
  simp only [CollatzResearch.WordTrace]
  refine ⟨100329371339383216520685809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66886247559588811013790539 100329371339383216520685809)
  ·
    refine ⟨75247028504537412390514357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100329371339383216520685809 75247028504537412390514357)
    ·
      refine ⟨7054408922300382411610721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75247028504537412390514357 7054408922300382411610721)
      ·
        refine ⟨5290806691725286808708041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7054408922300382411610721 5290806691725286808708041)
        ·
          refine ⟨3968105018793965106531031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5290806691725286808708041 3968105018793965106531031)
          ·
            refine ⟨5952157528190947659796547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3968105018793965106531031 5952157528190947659796547)
            ·
              refine ⟨8928236292286421489694821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5952157528190947659796547 8928236292286421489694821)
              ·
                refine ⟨1674044304803704029317779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8928236292286421489694821 1674044304803704029317779)
                ·
                  refine ⟨2511066457205556043976669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674044304803704029317779 2511066457205556043976669)
                  ·
                    refine ⟨941649921452083516491251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2511066457205556043976669 941649921452083516491251)
                    ·
                      rfl

theorem cell22_2750785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2750785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750785 prefixEnd_2750785 := by exact prefixLift 2750785
  have htrace : WordTrace (prefixWord ++ tailWord_2750785) baseStart_2750785 baseEnd_2750785 := by
    simpa [prefixWord, tailWord_2750785, baseEnd_2750785] using wordTrace_append hprefix tailTrace_2750785
  have hstable : (prefixWord ++ tailWord_2750785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750785).length < 2 ^ (prefixWord ++ tailWord_2750785).sum := by decide
  have hdescent : baseEnd_2750785 < baseStart_2750785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750903 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 3, 3]
def baseStart_2750903 : Nat := 118140960795 + 2750903 * 2 ^ 59
def prefixEnd_2750903 : Nat := 4983230072969 + 3 ^ 40 * 2750903 * 2
def baseEnd_2750903 : Nat := 941690315263570542040889

theorem tailTrace_2750903 : CollatzResearch.WordTrace tailWord_2750903 prefixEnd_2750903 941690315263570542040889 := by
  unfold tailWord_2750903
  simp only [CollatzResearch.WordTrace]
  refine ⟨100333675152955722673481363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66889116768637148448987575 100333675152955722673481363)
  ·
    refine ⟨150500512729433584010222045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100333675152955722673481363 150500512729433584010222045)
    ·
      refine ⟨56437692273537594003833267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150500512729433584010222045 56437692273537594003833267)
      ·
        refine ⟨84656538410306391005749901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56437692273537594003833267 84656538410306391005749901)
        ·
          refine ⟨31746201903864896627156213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84656538410306391005749901 31746201903864896627156213)
          ·
            refine ⟨2976206428487334058795895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31746201903864896627156213 2976206428487334058795895)
            ·
              refine ⟨4464309642731001088193843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976206428487334058795895 4464309642731001088193843)
              ·
                refine ⟨6696464464096501632290765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4464309642731001088193843 6696464464096501632290765)
                ·
                  refine ⟨2511174174036188112109037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6696464464096501632290765 2511174174036188112109037)
                  ·
                    refine ⟨941690315263570542040889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2511174174036188112109037 941690315263570542040889)
                    ·
                      rfl

theorem cell22_2750903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_2750903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750903 prefixEnd_2750903 := by exact prefixLift 2750903
  have htrace : WordTrace (prefixWord ++ tailWord_2750903) baseStart_2750903 baseEnd_2750903 := by
    simpa [prefixWord, tailWord_2750903, baseEnd_2750903] using wordTrace_append hprefix tailTrace_2750903
  have hstable : (prefixWord ++ tailWord_2750903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750903).length < 2 ^ (prefixWord ++ tailWord_2750903).sum := by decide
  have hdescent : baseEnd_2750903 < baseStart_2750903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2750959 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 5, 5]
def baseStart_2750959 : Nat := 118140960795 + 2750959 * 2 ^ 59
def prefixEnd_2750959 : Nat := 4983230072969 + 3 ^ 40 * 2750959 * 2
def baseEnd_2750959 : Nat := 941709485208005062640717

theorem tailTrace_2750959 : CollatzResearch.WordTrace tailWord_2750959 prefixEnd_2750959 941709485208005062640717 := by
  unfold tailWord_2750959
  simp only [CollatzResearch.WordTrace]
  refine ⟨100335717640752844237519931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66890478427168562825013287 100335717640752844237519931)
  ·
    refine ⟨150503576461129266356279897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100335717640752844237519931 150503576461129266356279897)
    ·
      refine ⟨112877682345846949767209923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150503576461129266356279897 112877682345846949767209923)
      ·
        refine ⟨169316523518770424650814885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112877682345846949767209923 169316523518770424650814885)
        ·
          refine ⟨31746848159769454622027791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169316523518770424650814885 31746848159769454622027791)
          ·
            refine ⟨47620272239654181933041687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31746848159769454622027791 47620272239654181933041687)
            ·
              refine ⟨71430408359481272899562531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47620272239654181933041687 71430408359481272899562531)
              ·
                refine ⟨107145612539221909349343797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71430408359481272899562531 107145612539221909349343797)
                ·
                  refine ⟨10044901175552054001500981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107145612539221909349343797 10044901175552054001500981)
                  ·
                    refine ⟨941709485208005062640717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10044901175552054001500981 941709485208005062640717)
                    ·
                      rfl

theorem cell22_2750959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_2750959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2750959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2750959 prefixEnd_2750959 := by exact prefixLift 2750959
  have htrace : WordTrace (prefixWord ++ tailWord_2750959) baseStart_2750959 baseEnd_2750959 := by
    simpa [prefixWord, tailWord_2750959, baseEnd_2750959] using wordTrace_append hprefix tailTrace_2750959
  have hstable : (prefixWord ++ tailWord_2750959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2750959).length < 2 ^ (prefixWord ++ tailWord_2750959).sum := by decide
  have hdescent : baseEnd_2750959 < baseStart_2750959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2750959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751019 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 1, 8]
def baseStart_2751019 : Nat := 118140960795 + 2751019 * 2 ^ 59
def prefixEnd_2751019 : Nat := 4983230072969 + 3 ^ 40 * 2751019 * 2
def baseEnd_2751019 : Nat := 941730024434184906140533

theorem tailTrace_2751019 : CollatzResearch.WordTrace tailWord_2751019 prefixEnd_2751019 941730024434184906140533 := by
  unfold tailWord_2751019
  simp only [CollatzResearch.WordTrace]
  refine ⟨100337906020535474484704111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66891937347023649656469407 100337906020535474484704111)
  ·
    refine ⟨150506859030803211727056167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100337906020535474484704111 150506859030803211727056167)
    ·
      refine ⟨225760288546204817590584251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150506859030803211727056167 225760288546204817590584251)
      ·
        refine ⟨338640432819307226385876377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225760288546204817590584251 338640432819307226385876377)
        ·
          refine ⟨253980324614480419789407283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338640432819307226385876377 253980324614480419789407283)
          ·
            refine ⟨380970486921720629684110925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253980324614480419789407283 380970486921720629684110925)
            ·
              refine ⟨142863932595645236131541597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380970486921720629684110925 142863932595645236131541597)
              ·
                refine ⟨53573974723366963549328099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142863932595645236131541597 53573974723366963549328099)
                ·
                  refine ⟨80360962085050445323992149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53573974723366963549328099 80360962085050445323992149)
                  ·
                    refine ⟨941730024434184906140533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80360962085050445323992149 941730024434184906140533)
                    ·
                      rfl

theorem cell22_2751019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 8].length) (baseStart_2751019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751019 prefixEnd_2751019 := by exact prefixLift 2751019
  have htrace : WordTrace (prefixWord ++ tailWord_2751019) baseStart_2751019 baseEnd_2751019 := by
    simpa [prefixWord, tailWord_2751019, baseEnd_2751019] using wordTrace_append hprefix tailTrace_2751019
  have hstable : (prefixWord ++ tailWord_2751019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751019).length < 2 ^ (prefixWord ++ tailWord_2751019).sum := by decide
  have hdescent : baseEnd_2751019 < baseStart_2751019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751055 : List Nat := [1, 1, 2, 1, 1, 2, 7, 3, 1, 3]
def baseStart_2751055 : Nat := 118140960795 + 2751055 * 2 ^ 59
def prefixEnd_2751055 : Nat := 4983230072969 + 3 ^ 40 * 2751055 * 2
def baseEnd_2751055 : Nat := 941742347969892812240423

theorem tailTrace_2751055 : CollatzResearch.WordTrace tailWord_2751055 prefixEnd_2751055 941742347969892812240423 := by
  unfold tailWord_2751055
  simp only [CollatzResearch.WordTrace]
  refine ⟨100339219048405052633014619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66892812698936701755343079 100339219048405052633014619)
  ·
    refine ⟨150508828572607578949521929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100339219048405052633014619 150508828572607578949521929)
    ·
      refine ⟨112881621429455684212141447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150508828572607578949521929 112881621429455684212141447)
      ·
        refine ⟨169322432144183526318212171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112881621429455684212141447 169322432144183526318212171)
        ·
          refine ⟨253983648216275289477318257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169322432144183526318212171 253983648216275289477318257)
          ·
            refine ⟨190487736162206467107988693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253983648216275289477318257 190487736162206467107988693)
            ·
              refine ⟨4464556316301714072843485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 190487736162206467107988693 4464556316301714072843485)
              ·
                refine ⟨1674208618613142777316307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4464556316301714072843485 1674208618613142777316307)
                ·
                  refine ⟨2511312927919714165974461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674208618613142777316307 2511312927919714165974461)
                  ·
                    refine ⟨941742347969892812240423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2511312927919714165974461 941742347969892812240423)
                    ·
                      rfl

theorem cell22_2751055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 1, 3].length) (baseStart_2751055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751055 prefixEnd_2751055 := by exact prefixLift 2751055
  have htrace : WordTrace (prefixWord ++ tailWord_2751055) baseStart_2751055 baseEnd_2751055 := by
    simpa [prefixWord, tailWord_2751055, baseEnd_2751055] using wordTrace_append hprefix tailTrace_2751055
  have hstable : (prefixWord ++ tailWord_2751055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751055).length < 2 ^ (prefixWord ++ tailWord_2751055).sum := by decide
  have hdescent : baseEnd_2751055 < baseStart_2751055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751081 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 3, 4]
def baseStart_2751081 : Nat := 118140960795 + 2751081 * 2 ^ 59
def prefixEnd_2751081 : Nat := 4983230072969 + 3 ^ 40 * 2751081 * 2
def baseEnd_2751081 : Nat := 941751248301237411090343

theorem tailTrace_2751081 : CollatzResearch.WordTrace tailWord_2751081 prefixEnd_2751081 941751248301237411090343 := by
  unfold tailWord_2751081
  simp only [CollatzResearch.WordTrace]
  refine ⟨100340167346310859073461097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66893444897540572715640731 100340167346310859073461097)
  ·
    refine ⟨75255125509733144305095823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100340167346310859073461097 75255125509733144305095823)
    ·
      refine ⟨112882688264599716457643735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75255125509733144305095823 112882688264599716457643735)
      ·
        refine ⟨169324032396899574686465603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112882688264599716457643735 169324032396899574686465603)
        ·
          refine ⟨253986048595349362029698405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169324032396899574686465603 253986048595349362029698405)
          ·
            refine ⟨47622384111628005380568451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 253986048595349362029698405 47622384111628005380568451)
            ·
              refine ⟨71433576167442008070852677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47622384111628005380568451 71433576167442008070852677)
              ·
                refine ⟨13393795531395376513284877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71433576167442008070852677 13393795531395376513284877)
                ·
                  refine ⟨5022673324273266192481829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13393795531395376513284877 5022673324273266192481829)
                  ·
                    refine ⟨941751248301237411090343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5022673324273266192481829 941751248301237411090343)
                    ·
                      rfl

theorem cell22_2751081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_2751081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751081 prefixEnd_2751081 := by exact prefixLift 2751081
  have htrace : WordTrace (prefixWord ++ tailWord_2751081) baseStart_2751081 baseEnd_2751081 := by
    simpa [prefixWord, tailWord_2751081, baseEnd_2751081] using wordTrace_append hprefix tailTrace_2751081
  have hstable : (prefixWord ++ tailWord_2751081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751081).length < 2 ^ (prefixWord ++ tailWord_2751081).sum := by decide
  have hdescent : baseEnd_2751081 < baseStart_2751081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751085 : List Nat := [1, 5, 1, 1, 3, 1, 4, 1, 5]
def baseStart_2751085 : Nat := 118140960795 + 2751085 * 2 ^ 59
def prefixEnd_2751085 : Nat := 4983230072969 + 3 ^ 40 * 2751085 * 2
def baseEnd_2751085 : Nat := 313917539194327577996777

theorem tailTrace_2751085 : CollatzResearch.WordTrace tailWord_2751085 prefixEnd_2751085 313917539194327577996777 := by
  unfold tailWord_2751085
  simp only [CollatzResearch.WordTrace]
  refine ⟨100340313238296367756606709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66893542158864245171071139 100340313238296367756606709)
  ·
    refine ⟨9406904366090284477181879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100340313238296367756606709 9406904366090284477181879)
    ·
      refine ⟨14110356549135426715772819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9406904366090284477181879 14110356549135426715772819)
      ·
        refine ⟨21165534823703140073659229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14110356549135426715772819 21165534823703140073659229)
        ·
          refine ⟨7937075558888677527622211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21165534823703140073659229 7937075558888677527622211)
          ·
            refine ⟨11905613338333016291433317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7937075558888677527622211 11905613338333016291433317)
            ·
              refine ⟨2232302500937440554643747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11905613338333016291433317 2232302500937440554643747)
              ·
                refine ⟨3348453751406160831965621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2232302500937440554643747 3348453751406160831965621)
                ·
                  refine ⟨313917539194327577996777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3348453751406160831965621 313917539194327577996777)
                  ·
                    rfl

theorem cell22_2751085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_2751085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751085 prefixEnd_2751085 := by exact prefixLift 2751085
  have htrace : WordTrace (prefixWord ++ tailWord_2751085) baseStart_2751085 baseEnd_2751085 := by
    simpa [prefixWord, tailWord_2751085, baseEnd_2751085] using wordTrace_append hprefix tailTrace_2751085
  have hstable : (prefixWord ++ tailWord_2751085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751085).length < 2 ^ (prefixWord ++ tailWord_2751085).sum := by decide
  have hdescent : baseEnd_2751085 < baseStart_2751085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751113 : List Nat := [1, 2, 1, 1, 4, 1, 1, 7, 4]
def baseStart_2751113 : Nat := 118140960795 + 2751113 * 2 ^ 59
def prefixEnd_2751113 : Nat := 4983230072969 + 3 ^ 40 * 2751113 * 2
def baseEnd_2751113 : Nat := 313920734185066664763415

theorem tailTrace_2751113 : CollatzResearch.WordTrace tailWord_2751113 prefixEnd_2751113 313920734185066664763415 := by
  unfold tailWord_2751113
  simp only [CollatzResearch.WordTrace]
  refine ⟨100341334482194928538625993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66894222988129952359083995 100341334482194928538625993)
  ·
    refine ⟨75256000861646196403969495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100341334482194928538625993 75256000861646196403969495)
    ·
      refine ⟨112884001292469294605954243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75256000861646196403969495 112884001292469294605954243)
      ·
        refine ⟨169326001938703941908931365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112884001292469294605954243 169326001938703941908931365)
        ·
          refine ⟨31748625363506989107924631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169326001938703941908931365 31748625363506989107924631)
          ·
            refine ⟨47622938045260483661886947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31748625363506989107924631 47622938045260483661886947)
            ·
              refine ⟨71434407067890725492830421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47622938045260483661886947 71434407067890725492830421)
              ·
                refine ⟨1674243915653688878738213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 71434407067890725492830421 1674243915653688878738213)
                ·
                  refine ⟨313920734185066664763415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1674243915653688878738213 313920734185066664763415)
                  ·
                    rfl

theorem cell22_2751113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 4].length) (baseStart_2751113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751113 prefixEnd_2751113 := by exact prefixLift 2751113
  have htrace : WordTrace (prefixWord ++ tailWord_2751113) baseStart_2751113 baseEnd_2751113 := by
    simpa [prefixWord, tailWord_2751113, baseEnd_2751113] using wordTrace_append hprefix tailTrace_2751113
  have hstable : (prefixWord ++ tailWord_2751113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751113).length < 2 ^ (prefixWord ++ tailWord_2751113).sum := by decide
  have hdescent : baseEnd_2751113 < baseStart_2751113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751233 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 5, 4]
def baseStart_2751233 : Nat := 118140960795 + 2751233 * 2 ^ 59
def prefixEnd_2751233 : Nat := 4983230072969 + 3 ^ 40 * 2751233 * 2
def baseEnd_2751233 : Nat := 941803281007559681289877

theorem tailTrace_2751233 : CollatzResearch.WordTrace tailWord_2751233 prefixEnd_2751233 941803281007559681289877 := by
  unfold tailWord_2751233
  simp only [CollatzResearch.WordTrace]
  refine ⟨100345711241760189032994353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66897140827840126021996235 100345711241760189032994353)
  ·
    refine ⟨75259283431320141774745765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100345711241760189032994353 75259283431320141774745765)
    ·
      refine ⟨14111115643372526582764831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75259283431320141774745765 14111115643372526582764831)
      ·
        refine ⟨21166673465058789874147247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14111115643372526582764831 21166673465058789874147247)
        ·
          refine ⟨31750010197588184811220871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21166673465058789874147247 31750010197588184811220871)
          ·
            refine ⟨47625015296382277216831307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31750010197588184811220871 47625015296382277216831307)
            ·
              refine ⟨71437522944573415825246961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47625015296382277216831307 71437522944573415825246961)
              ·
                refine ⟨53578142208430061868935221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71437522944573415825246961 53578142208430061868935221)
                ·
                  refine ⟨5022950832040318300212677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53578142208430061868935221 5022950832040318300212677)
                  ·
                    refine ⟨941803281007559681289877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5022950832040318300212677 941803281007559681289877)
                    ·
                      rfl

theorem cell22_2751233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_2751233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751233 prefixEnd_2751233 := by exact prefixLift 2751233
  have htrace : WordTrace (prefixWord ++ tailWord_2751233) baseStart_2751233 baseEnd_2751233 := by
    simpa [prefixWord, tailWord_2751233, baseEnd_2751233] using wordTrace_append hprefix tailTrace_2751233
  have hstable : (prefixWord ++ tailWord_2751233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751233).length < 2 ^ (prefixWord ++ tailWord_2751233).sum := by decide
  have hdescent : baseEnd_2751233 < baseStart_2751233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751293 : List Nat := [1, 4, 1, 4, 12]
def baseStart_2751293 : Nat := 118140960795 + 2751293 * 2 ^ 59
def prefixEnd_2751293 : Nat := 4983230072969 + 3 ^ 40 * 2751293 * 2
def baseEnd_2751293 : Nat := 3875818190262302571151

theorem tailTrace_2751293 : CollatzResearch.WordTrace tailWord_2751293 prefixEnd_2751293 3875818190262302571151 := by
  unfold tailWord_2751293
  simp only [CollatzResearch.WordTrace]
  refine ⟨100347899621542819280178533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66898599747695212853452355 100347899621542819280178533)
  ·
    refine ⟨18815231179039278615033475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100347899621542819280178533 18815231179039278615033475)
    ·
      refine ⟨28222846768558917922550213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18815231179039278615033475 28222846768558917922550213)
      ·
        refine ⟨5291783769104797110478165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28222846768558917922550213 5291783769104797110478165)
        ·
          refine ⟨3875818190262302571151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5291783769104797110478165 3875818190262302571151)
          ·
            rfl

theorem cell22_2751293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 12].length) (baseStart_2751293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751293 prefixEnd_2751293 := by exact prefixLift 2751293
  have htrace : WordTrace (prefixWord ++ tailWord_2751293) baseStart_2751293 baseEnd_2751293 := by
    simpa [prefixWord, tailWord_2751293, baseEnd_2751293] using wordTrace_append hprefix tailTrace_2751293
  have hstable : (prefixWord ++ tailWord_2751293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751293).length < 2 ^ (prefixWord ++ tailWord_2751293).sum := by decide
  have hdescent : baseEnd_2751293 < baseStart_2751293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751295 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 2, 4]
def baseStart_2751295 : Nat := 118140960795 + 2751295 * 2 ^ 59
def prefixEnd_2751295 : Nat := 4983230072969 + 3 ^ 40 * 2751295 * 2
def baseEnd_2751295 : Nat := 941824504874612186239687

theorem tailTrace_2751295 : CollatzResearch.WordTrace tailWord_2751295 prefixEnd_2751295 941824504874612186239687 := by
  unfold tailWord_2751295
  simp only [CollatzResearch.WordTrace]
  refine ⟨100347972567535573621751339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66898648378357049081167559 100347972567535573621751339)
  ·
    refine ⟨150521958851303360432627009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100347972567535573621751339 150521958851303360432627009)
    ·
      refine ⟨112891469138477520324470257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150521958851303360432627009 112891469138477520324470257)
      ·
        refine ⟨84668601853858140243352693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112891469138477520324470257 84668601853858140243352693)
        ·
          refine ⟨7937681423799200647814315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84668601853858140243352693 7937681423799200647814315)
          ·
            refine ⟨11906522135698800971721473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7937681423799200647814315 11906522135698800971721473)
            ·
              refine ⟨8929891601774100728791105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11906522135698800971721473 8929891601774100728791105)
              ·
                refine ⟨6697418701330575546593329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8929891601774100728791105 6697418701330575546593329)
                ·
                  refine ⟨5023064025997931659944997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6697418701330575546593329 5023064025997931659944997)
                  ·
                    refine ⟨941824504874612186239687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5023064025997931659944997 941824504874612186239687)
                    ·
                      rfl

theorem cell22_2751295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_2751295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751295 prefixEnd_2751295 := by exact prefixLift 2751295
  have htrace : WordTrace (prefixWord ++ tailWord_2751295) baseStart_2751295 baseEnd_2751295 := by
    simpa [prefixWord, tailWord_2751295, baseEnd_2751295] using wordTrace_append hprefix tailTrace_2751295
  have hstable : (prefixWord ++ tailWord_2751295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751295).length < 2 ^ (prefixWord ++ tailWord_2751295).sum := by decide
  have hdescent : baseEnd_2751295 < baseStart_2751295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751355 : List Nat := [1, 1, 1, 1, 1, 5, 5, 2, 5]
def baseStart_2751355 : Nat := 118140960795 + 2751355 * 2 ^ 59
def prefixEnd_2751355 : Nat := 4983230072969 + 3 ^ 40 * 2751355 * 2
def baseEnd_2751355 : Nat := 313948348033597343246501

theorem tailTrace_2751355 : CollatzResearch.WordTrace tailWord_2751355 prefixEnd_2751355 313948348033597343246501 := by
  unfold tailWord_2751355
  simp only [CollatzResearch.WordTrace]
  refine ⟨100350160947318203868935519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66900107298212135912623679 100350160947318203868935519)
  ·
    refine ⟨150525241420977305803403279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100350160947318203868935519 150525241420977305803403279)
    ·
      refine ⟨225787862131465958705104919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150525241420977305803403279 225787862131465958705104919)
      ·
        refine ⟨338681793197198938057657379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225787862131465958705104919 338681793197198938057657379)
        ·
          refine ⟨508022689795798407086486069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338681793197198938057657379 508022689795798407086486069)
          ·
            refine ⟨47627127168356100664358069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 508022689795798407086486069 47627127168356100664358069)
            ·
              refine ⟨4465043172033384437283569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47627127168356100664358069 4465043172033384437283569)
              ·
                refine ⟨3348782379025038327962677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4465043172033384437283569 3348782379025038327962677)
                ·
                  refine ⟨313948348033597343246501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3348782379025038327962677 313948348033597343246501)
                  ·
                    rfl

theorem cell22_2751355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 5].length) (baseStart_2751355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751355 prefixEnd_2751355 := by exact prefixLift 2751355
  have htrace : WordTrace (prefixWord ++ tailWord_2751355) baseStart_2751355 baseEnd_2751355 := by
    simpa [prefixWord, tailWord_2751355, baseEnd_2751355] using wordTrace_append hprefix tailTrace_2751355
  have hstable : (prefixWord ++ tailWord_2751355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751355).length < 2 ^ (prefixWord ++ tailWord_2751355).sum := by decide
  have hdescent : baseEnd_2751355 < baseStart_2751355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751417 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 6]
def baseStart_2751417 : Nat := 118140960795 + 2751417 * 2 ^ 59
def prefixEnd_2751417 : Nat := 4983230072969 + 3 ^ 40 * 2751417 * 2
def baseEnd_2751417 : Nat := 313955422655948178229771

theorem tailTrace_2751417 : CollatzResearch.WordTrace tailWord_2751417 prefixEnd_2751417 313955422655948178229771 := by
  unfold tailWord_2751417
  simp only [CollatzResearch.WordTrace]
  refine ⟨100352422273093588457692505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66901614848729058971795003 100352422273093588457692505)
  ·
    refine ⟨75264316704820191343269379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100352422273093588457692505 75264316704820191343269379)
    ·
      refine ⟨112896475057230287014904069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75264316704820191343269379 112896475057230287014904069)
      ·
        refine ⟨21168089073230678815294513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112896475057230287014904069 21168089073230678815294513)
        ·
          refine ⟨15876066804923009111470885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21168089073230678815294513 15876066804923009111470885)
          ·
            refine ⟨2976762525923064208400791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15876066804923009111470885 2976762525923064208400791)
            ·
              refine ⟨4465143788884596312601187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976762525923064208400791 4465143788884596312601187)
              ·
                refine ⟨6697715683326894468901781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4465143788884596312601187 6697715683326894468901781)
                ·
                  refine ⟨313955422655948178229771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6697715683326894468901781 313955422655948178229771)
                  ·
                    rfl

theorem cell22_2751417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 6].length) (baseStart_2751417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751417 prefixEnd_2751417 := by exact prefixLift 2751417
  have htrace : WordTrace (prefixWord ++ tailWord_2751417) baseStart_2751417 baseEnd_2751417 := by
    simpa [prefixWord, tailWord_2751417, baseEnd_2751417] using wordTrace_append hprefix tailTrace_2751417
  have hstable : (prefixWord ++ tailWord_2751417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751417).length < 2 ^ (prefixWord ++ tailWord_2751417).sum := by decide
  have hdescent : baseEnd_2751417 < baseStart_2751417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751511 : List Nat := [1, 1, 3, 5, 1, 1, 1, 5, 1, 3]
def baseStart_2751511 : Nat := 118140960795 + 2751511 * 2 ^ 59
def prefixEnd_2751511 : Nat := 4983230072969 + 3 ^ 40 * 2751511 * 2
def baseEnd_2751511 : Nat := 941898446088859622839025

theorem tailTrace_2751511 : CollatzResearch.WordTrace tailWord_2751511 prefixEnd_2751511 941898446088859622839025 := by
  unfold tailWord_2751511
  simp only [CollatzResearch.WordTrace]
  refine ⟨100355850734753042511614387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66903900489835361674409591 100355850734753042511614387)
  ·
    refine ⟨150533776102129563767421581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100355850734753042511614387 150533776102129563767421581)
    ·
      refine ⟨56450166038298586412783093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150533776102129563767421581 56450166038298586412783093)
      ·
        refine ⟨5292203066090492476198415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56450166038298586412783093 5292203066090492476198415)
        ·
          refine ⟨7938304599135738714297623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5292203066090492476198415 7938304599135738714297623)
          ·
            refine ⟨11907456898703608071446435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7938304599135738714297623 11907456898703608071446435)
            ·
              refine ⟨17861185348055412107169653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11907456898703608071446435 17861185348055412107169653)
              ·
                refine ⟨1674486126380194885047155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17861185348055412107169653 1674486126380194885047155)
                ·
                  refine ⟨2511729189570292327570733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674486126380194885047155 2511729189570292327570733)
                  ·
                    refine ⟨941898446088859622839025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2511729189570292327570733 941898446088859622839025)
                    ·
                      rfl

theorem cell22_2751511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_2751511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751511 prefixEnd_2751511 := by exact prefixLift 2751511
  have htrace : WordTrace (prefixWord ++ tailWord_2751511) baseStart_2751511 baseEnd_2751511 := by
    simpa [prefixWord, tailWord_2751511, baseEnd_2751511] using wordTrace_append hprefix tailTrace_2751511
  have hstable : (prefixWord ++ tailWord_2751511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751511).length < 2 ^ (prefixWord ++ tailWord_2751511).sum := by decide
  have hdescent : baseEnd_2751511 < baseStart_2751511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751522 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_2751522 : Nat := 118140960795 + 2751522 * 2 ^ 59
def prefixEnd_2751522 : Nat := 4983230072969 + 3 ^ 40 * 2751522 * 2
def baseEnd_2751522 : Nat := 941902211613659260813991

theorem tailTrace_2751522 : CollatzResearch.WordTrace tailWord_2751522 prefixEnd_2751522 941902211613659260813991 := by
  unfold tailWord_2751522
  simp only [CollatzResearch.WordTrace]
  refine ⟨25089062984428297847566205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66904167958475460926843213 25089062984428297847566205)
  ·
    refine ⟨9408398619160611692837327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25089062984428297847566205 9408398619160611692837327)
    ·
      refine ⟨14112597928740917539255991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9408398619160611692837327 14112597928740917539255991)
      ·
        refine ⟨21168896893111376308883987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14112597928740917539255991 21168896893111376308883987)
        ·
          refine ⟨31753345339667064463325981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21168896893111376308883987 31753345339667064463325981)
          ·
            refine ⟨11907504502375149173747243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31753345339667064463325981 11907504502375149173747243)
            ·
              refine ⟨17861256753562723760620865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11907504502375149173747243 17861256753562723760620865)
              ·
                refine ⟨13395942565172042820465649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17861256753562723760620865 13395942565172042820465649)
                ·
                  refine ⟨10046956923879032115349237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13395942565172042820465649 10046956923879032115349237)
                  ·
                    refine ⟨941902211613659260813991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10046956923879032115349237 941902211613659260813991)
                    ·
                      rfl

theorem cell22_2751522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_2751522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751522 prefixEnd_2751522 := by exact prefixLift 2751522
  have htrace : WordTrace (prefixWord ++ tailWord_2751522) baseStart_2751522 baseEnd_2751522 := by
    simpa [prefixWord, tailWord_2751522, baseEnd_2751522] using wordTrace_append hprefix tailTrace_2751522
  have hstable : (prefixWord ++ tailWord_2751522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751522).length < 2 ^ (prefixWord ++ tailWord_2751522).sum := by decide
  have hdescent : baseEnd_2751522 < baseStart_2751522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751524 : List Nat := [2, 3, 1, 4, 1, 1, 3, 2, 5]
def baseStart_2751524 : Nat := 118140960795 + 2751524 * 2 ^ 59
def prefixEnd_2751524 : Nat := 4983230072969 + 3 ^ 40 * 2751524 * 2
def baseEnd_2751524 : Nat := 313967632084843974087995

theorem tailTrace_2751524 : CollatzResearch.WordTrace tailWord_2751524 prefixEnd_2751524 313967632084843974087995 := by
  unfold tailWord_2751524
  simp only [CollatzResearch.WordTrace]
  refine ⟨50178162441852972865918813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66904216589137297154558417 50178162441852972865918813)
  ·
    refine ⟨18816810915694864824719555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50178162441852972865918813 18816810915694864824719555)
    ·
      refine ⟨28225216373542297237079333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18816810915694864824719555 28225216373542297237079333)
      ·
        refine ⟨5292228070039180731952375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28225216373542297237079333 5292228070039180731952375)
        ·
          refine ⟨7938342105058771097928563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5292228070039180731952375 7938342105058771097928563)
          ·
            refine ⟨11907513157588156646892845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7938342105058771097928563 11907513157588156646892845)
            ·
              refine ⟨4465317434095558742584817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11907513157588156646892845 4465317434095558742584817)
              ·
                refine ⟨3348988075571669056938613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4465317434095558742584817 3348988075571669056938613)
                ·
                  refine ⟨313967632084843974087995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3348988075571669056938613 313967632084843974087995)
                  ·
                    rfl

theorem cell22_2751524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_2751524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751524 prefixEnd_2751524 := by exact prefixLift 2751524
  have htrace : WordTrace (prefixWord ++ tailWord_2751524) baseStart_2751524 baseEnd_2751524 := by
    simpa [prefixWord, tailWord_2751524, baseEnd_2751524] using wordTrace_append hprefix tailTrace_2751524
  have hstable : (prefixWord ++ tailWord_2751524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751524).length < 2 ^ (prefixWord ++ tailWord_2751524).sum := by decide
  have hdescent : baseEnd_2751524 < baseStart_2751524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751569 : List Nat := [1, 2, 2, 1, 3, 1, 5, 3, 4]
def baseStart_2751569 : Nat := 118140960795 + 2751569 * 2 ^ 59
def prefixEnd_2751569 : Nat := 4983230072969 + 3 ^ 40 * 2751569 * 2
def baseEnd_2751569 : Nat := 313972766891388934962949

theorem tailTrace_2751569 : CollatzResearch.WordTrace tailWord_2751569 prefixEnd_2751569 313972766891388934962949 := by
  unfold tailWord_2751569
  simp only [CollatzResearch.WordTrace]
  refine ⟨100357966168542918417225761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66905310779028612278150507 100357966168542918417225761)
  ·
    refine ⟨75268474626407188812919321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100357966168542918417225761 75268474626407188812919321)
    ·
      refine ⟨56451355969805391609689491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75268474626407188812919321 56451355969805391609689491)
      ·
        refine ⟨84677033954708087414534237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56451355969805391609689491 84677033954708087414534237)
        ·
          refine ⟨31753887733015532780450339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84677033954708087414534237 31753887733015532780450339)
          ·
            refine ⟨47630831599523299170675509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31753887733015532780450339 47630831599523299170675509)
            ·
              refine ⟨4465390462455309297250829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47630831599523299170675509 4465390462455309297250829)
              ·
                refine ⟨1674521423420740986469061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4465390462455309297250829 1674521423420740986469061)
                ·
                  refine ⟨313972766891388934962949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1674521423420740986469061 313972766891388934962949)
                  ·
                    rfl

theorem cell22_2751569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 4].length) (baseStart_2751569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751569 prefixEnd_2751569 := by exact prefixLift 2751569
  have htrace : WordTrace (prefixWord ++ tailWord_2751569) baseStart_2751569 baseEnd_2751569 := by
    simpa [prefixWord, tailWord_2751569, baseEnd_2751569] using wordTrace_append hprefix tailTrace_2751569
  have hstable : (prefixWord ++ tailWord_2751569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751569).length < 2 ^ (prefixWord ++ tailWord_2751569).sum := by decide
  have hdescent : baseEnd_2751569 < baseStart_2751569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751584 : List Nat := [2, 1, 1, 3, 2, 2, 2, 4, 2, 3]
def baseStart_2751584 : Nat := 118140960795 + 2751584 * 2 ^ 59
def prefixEnd_2751584 : Nat := 4983230072969 + 3 ^ 40 * 2751584 * 2
def baseEnd_2751584 : Nat := 941923435480711765763801

theorem tailTrace_2751584 : CollatzResearch.WordTrace tailWord_2751584 prefixEnd_2751584 941923435480711765763801 := by
  unfold tailWord_2751584
  simp only [CollatzResearch.WordTrace]
  refine ⟨50179256631744287989510903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66905675508992383986014537 50179256631744287989510903)
  ·
    refine ⟨75268884947616431984266355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50179256631744287989510903 75268884947616431984266355)
    ·
      refine ⟨112903327421424647976399533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75268884947616431984266355 112903327421424647976399533)
      ·
        refine ⟨42338747783034242991149825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112903327421424647976399533 42338747783034242991149825)
        ·
          refine ⟨31754060837275682243362369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42338747783034242991149825 31754060837275682243362369)
          ·
            refine ⟨23815545627956761682521777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31754060837275682243362369 23815545627956761682521777)
            ·
              refine ⟨17861659220967571261891333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23815545627956761682521777 17861659220967571261891333)
              ·
                refine ⟨3349061103931419611604625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17861659220967571261891333 3349061103931419611604625)
                ·
                  refine ⟨2511795827948564708703469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3349061103931419611604625 2511795827948564708703469)
                  ·
                    refine ⟨941923435480711765763801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2511795827948564708703469 941923435480711765763801)
                    ·
                      rfl

theorem cell22_2751584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 2, 3].length) (baseStart_2751584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751584 prefixEnd_2751584 := by exact prefixLift 2751584
  have htrace : WordTrace (prefixWord ++ tailWord_2751584) baseStart_2751584 baseEnd_2751584 := by
    simpa [prefixWord, tailWord_2751584, baseEnd_2751584] using wordTrace_append hprefix tailTrace_2751584
  have hstable : (prefixWord ++ tailWord_2751584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751584).length < 2 ^ (prefixWord ++ tailWord_2751584).sum := by decide
  have hdescent : baseEnd_2751584 < baseStart_2751584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751586 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 6]
def baseStart_2751586 : Nat := 118140960795 + 2751586 * 2 ^ 59
def prefixEnd_2751586 : Nat := 4983230072969 + 3 ^ 40 * 2751586 * 2
def baseEnd_2751586 : Nat := 313974706707194809071265

theorem tailTrace_2751586 : CollatzResearch.WordTrace tailWord_2751586 prefixEnd_2751586 313974706707194809071265 := by
  unfold tailWord_2751586
  simp only [CollatzResearch.WordTrace]
  refine ⟨25089646552370332580148653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66905724139654220213729741 25089646552370332580148653)
  ·
    refine ⟨9408617457138874717555745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25089646552370332580148653 9408617457138874717555745)
    ·
      refine ⟨7056463092854156038166809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9408617457138874717555745 7056463092854156038166809)
      ·
        refine ⟨5292347319640617028625107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7056463092854156038166809 5292347319640617028625107)
        ·
          refine ⟨7938520979460925542937661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5292347319640617028625107 7938520979460925542937661)
          ·
            refine ⟨2976945367297847078601623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7938520979460925542937661 2976945367297847078601623)
            ·
              refine ⟨4465418050946770617902435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976945367297847078601623 4465418050946770617902435)
              ·
                refine ⟨6698127076420155926853653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4465418050946770617902435 6698127076420155926853653)
                ·
                  refine ⟨313974706707194809071265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6698127076420155926853653 313974706707194809071265)
                  ·
                    rfl

theorem cell22_2751586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_2751586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751586 prefixEnd_2751586 := by exact prefixLift 2751586
  have htrace : WordTrace (prefixWord ++ tailWord_2751586) baseStart_2751586 baseEnd_2751586 := by
    simpa [prefixWord, tailWord_2751586, baseEnd_2751586] using wordTrace_append hprefix tailTrace_2751586
  have hstable : (prefixWord ++ tailWord_2751586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751586).length < 2 ^ (prefixWord ++ tailWord_2751586).sum := by decide
  have hdescent : baseEnd_2751586 < baseStart_2751586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751597 : List Nat := [1, 5, 1, 1, 2, 2, 1, 9]
def baseStart_2751597 : Nat := 118140960795 + 2751597 * 2 ^ 59
def prefixEnd_2751597 : Nat := 4983230072969 + 3 ^ 40 * 2751597 * 2
def baseEnd_2751597 : Nat := 104658653960709340576529

theorem tailTrace_2751597 : CollatzResearch.WordTrace tailWord_2751597 prefixEnd_2751597 104658653960709340576529 := by
  unfold tailWord_2751597
  simp only [CollatzResearch.WordTrace]
  refine ⟨100358987412441479199245045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66905991608294319466163363 100358987412441479199245045)
  ·
    refine ⟨9408655069916388674929223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100358987412441479199245045 9408655069916388674929223)
    ·
      refine ⟨14112982604874583012393835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9408655069916388674929223 14112982604874583012393835)
      ·
        refine ⟨21169473907311874518590753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14112982604874583012393835 21169473907311874518590753)
        ·
          refine ⟨15877105430483905888943065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21169473907311874518590753 15877105430483905888943065)
          ·
            refine ⟨11907829072862929416707299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15877105430483905888943065 11907829072862929416707299)
            ·
              refine ⟨17861743609294394125060949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11907829072862929416707299 17861743609294394125060949)
              ·
                refine ⟨104658653960709340576529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17861743609294394125060949 104658653960709340576529)
                ·
                  rfl

theorem cell22_2751597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 9].length) (baseStart_2751597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751597 prefixEnd_2751597 := by exact prefixLift 2751597
  have htrace : WordTrace (prefixWord ++ tailWord_2751597) baseStart_2751597 baseEnd_2751597 := by
    simpa [prefixWord, tailWord_2751597, baseEnd_2751597] using wordTrace_append hprefix tailTrace_2751597
  have hstable : (prefixWord ++ tailWord_2751597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751597).length < 2 ^ (prefixWord ++ tailWord_2751597).sum := by decide
  have hdescent : baseEnd_2751597 < baseStart_2751597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751605 : List Nat := [1, 3, 4, 3, 2, 1, 1, 2, 1, 4]
def baseStart_2751605 : Nat := 118140960795 + 2751605 * 2 ^ 59
def prefixEnd_2751605 : Nat := 4983230072969 + 3 ^ 40 * 2751605 * 2
def baseEnd_2751605 : Nat := 941930624209874710988737

theorem tailTrace_2751605 : CollatzResearch.WordTrace tailWord_2751605 prefixEnd_2751605 941930624209874710988737 := by
  unfold tailWord_2751605
  simp only [CollatzResearch.WordTrace]
  refine ⟨100359279196412496565536269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66906186130941664377024179 100359279196412496565536269)
  ·
    refine ⟨37634729698654686212076101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100359279196412496565536269 37634729698654686212076101)
    ·
      refine ⟨7056511818497753664764269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37634729698654686212076101 7056511818497753664764269)
      ·
        refine ⟨2646191931936657624286601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7056511818497753664764269 2646191931936657624286601)
        ·
          refine ⟨1984643948952493218214951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2646191931936657624286601 1984643948952493218214951)
          ·
            refine ⟨2976965923428739827322427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1984643948952493218214951 2976965923428739827322427)
            ·
              refine ⟨4465448885143109740983641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976965923428739827322427 4465448885143109740983641)
              ·
                refine ⟨3349086663857332305737731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4465448885143109740983641 3349086663857332305737731)
                ·
                  refine ⟨5023629995785998458606597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3349086663857332305737731 5023629995785998458606597)
                  ·
                    refine ⟨941930624209874710988737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5023629995785998458606597 941930624209874710988737)
                    ·
                      rfl

theorem cell22_2751605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_2751605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751605 prefixEnd_2751605 := by exact prefixLift 2751605
  have htrace : WordTrace (prefixWord ++ tailWord_2751605) baseStart_2751605 baseEnd_2751605 := by
    simpa [prefixWord, tailWord_2751605, baseEnd_2751605] using wordTrace_append hprefix tailTrace_2751605
  have hstable : (prefixWord ++ tailWord_2751605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751605).length < 2 ^ (prefixWord ++ tailWord_2751605).sum := by decide
  have hdescent : baseEnd_2751605 < baseStart_2751605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751693 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 7]
def baseStart_2751693 : Nat := 118140960795 + 2751693 * 2 ^ 59
def prefixEnd_2751693 : Nat := 4983230072969 + 3 ^ 40 * 2751693 * 2
def baseEnd_2751693 : Nat := 313986916136090604929489

theorem tailTrace_2751693 : CollatzResearch.WordTrace tailWord_2751693 prefixEnd_2751693 313986916136090604929489 := by
  unfold tailWord_2751693
  simp only [CollatzResearch.WordTrace]
  refine ⟨100362488820093687594739733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66908325880062458396493155 100362488820093687594739733)
  ·
    refine ⟨4704491663441891606003425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100362488820093687594739733 4704491663441891606003425)
    ·
      refine ⟨3528368747581418704502569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4704491663441891606003425 3528368747581418704502569)
      ·
        refine ⟨2646276560686064028376927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3528368747581418704502569 2646276560686064028376927)
        ·
          refine ⟨3969414841029096042565391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2646276560686064028376927 3969414841029096042565391)
          ·
            refine ⟨5954122261543644063848087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3969414841029096042565391 5954122261543644063848087)
            ·
              refine ⟨8931183392315466095772131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5954122261543644063848087 8931183392315466095772131)
              ·
                refine ⟨13396775088473199143658197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8931183392315466095772131 13396775088473199143658197)
                ·
                  refine ⟨313986916136090604929489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13396775088473199143658197 313986916136090604929489)
                  ·
                    rfl

theorem cell22_2751693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_2751693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751693 prefixEnd_2751693 := by exact prefixLift 2751693
  have htrace : WordTrace (prefixWord ++ tailWord_2751693) baseStart_2751693 baseEnd_2751693 := by
    simpa [prefixWord, tailWord_2751693, baseEnd_2751693] using wordTrace_append hprefix tailTrace_2751693
  have hstable : (prefixWord ++ tailWord_2751693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751693).length < 2 ^ (prefixWord ++ tailWord_2751693).sum := by decide
  have hdescent : baseEnd_2751693 < baseStart_2751693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751770 : List Nat := [3, 1, 1, 3, 3, 3, 2, 1, 2, 3]
def baseStart_2751770 : Nat := 118140960795 + 2751770 * 2 ^ 59
def prefixEnd_2751770 : Nat := 4983230072969 + 3 ^ 40 * 2751770 * 2
def baseEnd_2751770 : Nat := 941987107081869280613231

theorem tailTrace_2751770 : CollatzResearch.WordTrace tailWord_2751770 prefixEnd_2751770 941987107081869280613231 := by
  unfold tailWord_2751770
  simp only [CollatzResearch.WordTrace]
  refine ⟨25091324310203682436323191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66910198160543153163528509 25091324310203682436323191)
  ·
    refine ⟨37636986465305523654484787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25091324310203682436323191 37636986465305523654484787)
    ·
      refine ⟨56455479697958285481727181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37636986465305523654484787 56455479697958285481727181)
      ·
        refine ⟨21170804886734357055647693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56455479697958285481727181 21170804886734357055647693)
        ·
          refine ⟨7939051832525383895867885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21170804886734357055647693 7939051832525383895867885)
          ·
            refine ⟨2977144437197018960950457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7939051832525383895867885 2977144437197018960950457)
            ·
              refine ⟨2232858327897764220712843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2977144437197018960950457 2232858327897764220712843)
              ·
                refine ⟨3349287491846646331069265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2232858327897764220712843 3349287491846646331069265)
                ·
                  refine ⟨2511965618884984748301949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3349287491846646331069265 2511965618884984748301949)
                  ·
                    refine ⟨941987107081869280613231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2511965618884984748301949 941987107081869280613231)
                    ·
                      rfl

theorem cell22_2751770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_2751770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751770 prefixEnd_2751770 := by exact prefixLift 2751770
  have htrace : WordTrace (prefixWord ++ tailWord_2751770) baseStart_2751770 baseEnd_2751770 := by
    simpa [prefixWord, tailWord_2751770, baseEnd_2751770] using wordTrace_append hprefix tailTrace_2751770
  have hstable : (prefixWord ++ tailWord_2751770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751770).length < 2 ^ (prefixWord ++ tailWord_2751770).sum := by decide
  have hdescent : baseEnd_2751770 < baseStart_2751770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751815 : List Nat := [1, 1, 4, 1, 2, 3, 4, 2, 1, 3]
def baseStart_2751815 : Nat := 118140960795 + 2751815 * 2 ^ 59
def prefixEnd_2751815 : Nat := 4983230072969 + 3 ^ 40 * 2751815 * 2
def baseEnd_2751815 : Nat := 942002511501504163238093

theorem tailTrace_2751815 : CollatzResearch.WordTrace tailWord_2751815 prefixEnd_2751815 942002511501504163238093 := by
  unfold tailWord_2751815
  simp only [CollatzResearch.WordTrace]
  refine ⟨100366938525651702430680899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66911292350434468287120599 100366938525651702430680899)
  ·
    refine ⟨150550407788477553646021349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100366938525651702430680899 150550407788477553646021349)
    ·
      refine ⟨28228201460339541308629003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150550407788477553646021349 28228201460339541308629003)
      ·
        refine ⟨42342302190509311962943505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28228201460339541308629003 42342302190509311962943505)
        ·
          refine ⟨31756726642881983972207629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42342302190509311962943505 31756726642881983972207629)
          ·
            refine ⟨11908772491080743989577861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31756726642881983972207629 11908772491080743989577861)
            ·
              refine ⟨2232894842077639498045849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11908772491080743989577861 2232894842077639498045849)
              ·
                refine ⟨1674671131558229623534387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2232894842077639498045849 1674671131558229623534387)
                ·
                  refine ⟨2512006697337344435301581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674671131558229623534387 2512006697337344435301581)
                  ·
                    refine ⟨942002511501504163238093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2512006697337344435301581 942002511501504163238093)
                    ·
                      rfl

theorem cell22_2751815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_2751815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751815 prefixEnd_2751815 := by exact prefixLift 2751815
  have htrace : WordTrace (prefixWord ++ tailWord_2751815) baseStart_2751815 baseEnd_2751815 := by
    simpa [prefixWord, tailWord_2751815, baseEnd_2751815] using wordTrace_append hprefix tailTrace_2751815
  have hstable : (prefixWord ++ tailWord_2751815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751815).length < 2 ^ (prefixWord ++ tailWord_2751815).sum := by decide
  have hdescent : baseEnd_2751815 < baseStart_2751815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751824 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 5, 4]
def baseStart_2751824 : Nat := 118140960795 + 2751824 * 2 ^ 59
def prefixEnd_2751824 : Nat := 4983230072969 + 3 ^ 40 * 2751824 * 2
def baseEnd_2751824 : Nat := 942005592385431139763065

theorem tailTrace_2751824 : CollatzResearch.WordTrace tailWord_2751824 prefixEnd_2751824 942005592385431139763065 := by
  unfold tailWord_2751824
  simp only [CollatzResearch.WordTrace]
  refine ⟨50183633391309548483879263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66911511188412731311839017 50183633391309548483879263)
  ·
    refine ⟨75275450086964322725818895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50183633391309548483879263 75275450086964322725818895)
    ·
      refine ⟨112913175130446484088728343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75275450086964322725818895 112913175130446484088728343)
      ·
        refine ⟨169369762695669726133092515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112913175130446484088728343 169369762695669726133092515)
        ·
          refine ⟨254054644043504589199638773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169369762695669726133092515 254054644043504589199638773)
          ·
            refine ⟨23817622879078555237466135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 254054644043504589199638773 23817622879078555237466135)
            ·
              refine ⟨35726434318617832856199203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23817622879078555237466135 35726434318617832856199203)
              ·
                refine ⟨53589651477926749284298805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35726434318617832856199203 53589651477926749284298805)
                ·
                  refine ⟨5024029826055632745403013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53589651477926749284298805 5024029826055632745403013)
                  ·
                    refine ⟨942005592385431139763065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5024029826055632745403013 942005592385431139763065)
                    ·
                      rfl

theorem cell22_2751824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_2751824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751824 prefixEnd_2751824 := by exact prefixLift 2751824
  have htrace : WordTrace (prefixWord ++ tailWord_2751824) baseStart_2751824 baseEnd_2751824 := by
    simpa [prefixWord, tailWord_2751824, baseEnd_2751824] using wordTrace_append hprefix tailTrace_2751824
  have hstable : (prefixWord ++ tailWord_2751824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751824).length < 2 ^ (prefixWord ++ tailWord_2751824).sum := by decide
  have hdescent : baseEnd_2751824 < baseStart_2751824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751873 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 6]
def baseStart_2751873 : Nat := 118140960795 + 2751873 * 2 ^ 59
def prefixEnd_2751873 : Nat := 4983230072969 + 3 ^ 40 * 2751873 * 2
def baseEnd_2751873 : Nat := 314007455362270448429305

theorem tailTrace_2751873 : CollatzResearch.WordTrace tailWord_2751873 prefixEnd_2751873 314007455362270448429305 := by
  unfold tailWord_2751873
  simp only [CollatzResearch.WordTrace]
  refine ⟨100369053959441578336292273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66912702639627718890861515 100369053959441578336292273)
  ·
    refine ⟨75276790469581183752219205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100369053959441578336292273 75276790469581183752219205)
    ·
      refine ⟨14114398213046471953541101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75276790469581183752219205 14114398213046471953541101)
      ·
        refine ⟨5292899329892426982577913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14114398213046471953541101 5292899329892426982577913)
        ·
          refine ⟨3969674497419320236933435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5292899329892426982577913 3969674497419320236933435)
          ·
            refine ⟨5954511746128980355400153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3969674497419320236933435 5954511746128980355400153)
            ·
              refine ⟨4465883809596735266550115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5954511746128980355400153 4465883809596735266550115)
              ·
                refine ⟨6698825714395102899825173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4465883809596735266550115 6698825714395102899825173)
                ·
                  refine ⟨314007455362270448429305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6698825714395102899825173 314007455362270448429305)
                  ·
                    rfl

theorem cell22_2751873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 6].length) (baseStart_2751873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751873 prefixEnd_2751873 := by exact prefixLift 2751873
  have htrace : WordTrace (prefixWord ++ tailWord_2751873) baseStart_2751873 baseEnd_2751873 := by
    simpa [prefixWord, tailWord_2751873, baseEnd_2751873] using wordTrace_append hprefix tailTrace_2751873
  have hstable : (prefixWord ++ tailWord_2751873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751873).length < 2 ^ (prefixWord ++ tailWord_2751873).sum := by decide
  have hdescent : baseEnd_2751873 < baseStart_2751873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751884 : List Nat := [2, 2, 1, 2, 1, 3, 2, 9]
def baseStart_2751884 : Nat := 118140960795 + 2751884 * 2 ^ 59
def prefixEnd_2751884 : Nat := 4983230072969 + 3 ^ 40 * 2751884 * 2
def baseEnd_2751884 : Nat := 104669570179067887029209

theorem tailTrace_2751884 : CollatzResearch.WordTrace tailWord_2751884 prefixEnd_2751884 104669570179067887029209 := by
  unfold tailWord_2751884
  simp only [CollatzResearch.WordTrace]
  refine ⟨50184727581200863607471353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66912970108267818143295137 50184727581200863607471353)
  ·
    refine ⟨37638545685900647705603515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50184727581200863607471353 37638545685900647705603515)
    ·
      refine ⟨56457818528850971558405273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37638545685900647705603515 56457818528850971558405273)
      ·
        refine ⟨42343363896638228668803955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56457818528850971558405273 42343363896638228668803955)
        ·
          refine ⟨63515045844957343003205933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42343363896638228668803955 63515045844957343003205933)
          ·
            refine ⟨23818142191859003626202225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63515045844957343003205933 23818142191859003626202225)
            ·
              refine ⟨17863606643894252719651669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23818142191859003626202225 17863606643894252719651669)
              ·
                refine ⟨104669570179067887029209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17863606643894252719651669 104669570179067887029209)
                ·
                  rfl

theorem cell22_2751884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 9].length) (baseStart_2751884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751884 prefixEnd_2751884 := by exact prefixLift 2751884
  have htrace : WordTrace (prefixWord ++ tailWord_2751884) baseStart_2751884 baseEnd_2751884 := by
    simpa [prefixWord, tailWord_2751884, baseEnd_2751884] using wordTrace_append hprefix tailTrace_2751884
  have hstable : (prefixWord ++ tailWord_2751884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751884).length < 2 ^ (prefixWord ++ tailWord_2751884).sum := by decide
  have hdescent : baseEnd_2751884 < baseStart_2751884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751901 : List Nat := [1, 4, 2, 1, 3, 2, 1, 8]
def baseStart_2751901 : Nat := 118140960795 + 2751901 * 2 ^ 59
def prefixEnd_2751901 : Nat := 4983230072969 + 3 ^ 40 * 2751901 * 2
def baseEnd_2751901 : Nat := 104670216784336511731981

theorem tailTrace_2751901 : CollatzResearch.WordTrace tailWord_2751901 prefixEnd_2751901 104670216784336511731981 := by
  unfold tailWord_2751901
  simp only [CollatzResearch.WordTrace]
  refine ⟨100370075203340139118311557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66913383468893426078874371 100370075203340139118311557)
  ·
    refine ⟨18819389100626276084683417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100370075203340139118311557 18819389100626276084683417)
    ·
      refine ⟨14114541825469707063512563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18819389100626276084683417 14114541825469707063512563)
      ·
        refine ⟨21171812738204560595268845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14114541825469707063512563 21171812738204560595268845)
        ·
          refine ⟨7939429776826710223225817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21171812738204560595268845 7939429776826710223225817)
          ·
            refine ⟨5954572332620032667419363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7939429776826710223225817 5954572332620032667419363)
            ·
              refine ⟨8931858498930049001129045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5954572332620032667419363 8931858498930049001129045)
              ·
                refine ⟨104670216784336511731981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8931858498930049001129045 104670216784336511731981)
                ·
                  rfl

theorem cell22_2751901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 8].length) (baseStart_2751901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751901 prefixEnd_2751901 := by exact prefixLift 2751901
  have htrace : WordTrace (prefixWord ++ tailWord_2751901) baseStart_2751901 baseEnd_2751901 := by
    simpa [prefixWord, tailWord_2751901, baseEnd_2751901] using wordTrace_append hprefix tailTrace_2751901
  have hstable : (prefixWord ++ tailWord_2751901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751901).length < 2 ^ (prefixWord ++ tailWord_2751901).sum := by decide
  have hdescent : baseEnd_2751901 < baseStart_2751901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2751916 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 5, 3]
def baseStart_2751916 : Nat := 118140960795 + 2751916 * 2 ^ 59
def prefixEnd_2751916 : Nat := 4983230072969 + 3 ^ 40 * 2751916 * 2
def baseEnd_2751916 : Nat := 942037085865573566462783

theorem tailTrace_2751916 : CollatzResearch.WordTrace tailWord_2751916 prefixEnd_2751916 942037085865573566462783 := by
  unfold tailWord_2751916
  simp only [CollatzResearch.WordTrace]
  refine ⟨50185311149142898340053801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66913748198857197786738401 50185311149142898340053801)
  ·
    refine ⟨37638983361857173755040351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50185311149142898340053801 37638983361857173755040351)
    ·
      refine ⟨56458475042785760632560527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37638983361857173755040351 56458475042785760632560527)
      ·
        refine ⟨84687712564178640948840791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56458475042785760632560527 84687712564178640948840791)
        ·
          refine ⟨127031568846267961423261187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84687712564178640948840791 127031568846267961423261187)
          ·
            refine ⟨190547353269401942134891781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127031568846267961423261187 190547353269401942134891781)
            ·
              refine ⟨35727628738012864150292209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190547353269401942134891781 35727628738012864150292209)
              ·
                refine ⟨26795721553509648112719157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35727628738012864150292209 26795721553509648112719157)
                ·
                  refine ⟨2512098895641529510567421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26795721553509648112719157 2512098895641529510567421)
                  ·
                    refine ⟨942037085865573566462783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2512098895641529510567421 942037085865573566462783)
                    ·
                      rfl

theorem cell22_2751916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_2751916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2751916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2751916 prefixEnd_2751916 := by exact prefixLift 2751916
  have htrace : WordTrace (prefixWord ++ tailWord_2751916) baseStart_2751916 baseEnd_2751916 := by
    simpa [prefixWord, tailWord_2751916, baseEnd_2751916] using wordTrace_append hprefix tailTrace_2751916
  have hstable : (prefixWord ++ tailWord_2751916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2751916).length < 2 ^ (prefixWord ++ tailWord_2751916).sum := by decide
  have hdescent : baseEnd_2751916 < baseStart_2751916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2751916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752057 : List Nat := [1, 2, 1, 5, 1, 3, 3, 1, 2, 3]
def baseStart_2752057 : Nat := 118140960795 + 2752057 * 2 ^ 59
def prefixEnd_2752057 : Nat := 4983230072969 + 3 ^ 40 * 2752057 * 2
def baseEnd_2752057 : Nat := 942085353047096198687351

theorem tailTrace_2752057 : CollatzResearch.WordTrace tailWord_2752057 prefixEnd_2752057 942085353047096198687351 := by
  unfold tailWord_2752057
  simp only [CollatzResearch.WordTrace]
  refine ⟨100375764990774977760990425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66917176660516651840660283 100375764990774977760990425)
  ·
    refine ⟨75281823743081233320742819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100375764990774977760990425 75281823743081233320742819)
    ·
      refine ⟨112922735614621849981114229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75281823743081233320742819 112922735614621849981114229)
      ·
        refine ⟨10586506463870798435729459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112922735614621849981114229 10586506463870798435729459)
        ·
          refine ⟨15879759695806197653594189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10586506463870798435729459 15879759695806197653594189)
          ·
            refine ⟨5954909885927324120097821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15879759695806197653594189 5954909885927324120097821)
            ·
              refine ⟨2233091207222746545036683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5954909885927324120097821 2233091207222746545036683)
              ·
                refine ⟨3349636810834119817555025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2233091207222746545036683 3349636810834119817555025)
                ·
                  refine ⟨2512227608125589863166269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3349636810834119817555025 2512227608125589863166269)
                  ·
                    refine ⟨942085353047096198687351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2512227608125589863166269 942085353047096198687351)
                    ·
                      rfl

theorem cell22_2752057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 2, 3].length) (baseStart_2752057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752057 prefixEnd_2752057 := by exact prefixLift 2752057
  have htrace : WordTrace (prefixWord ++ tailWord_2752057) baseStart_2752057 baseEnd_2752057 := by
    simpa [prefixWord, tailWord_2752057, baseEnd_2752057] using wordTrace_append hprefix tailTrace_2752057
  have hstable : (prefixWord ++ tailWord_2752057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752057).length < 2 ^ (prefixWord ++ tailWord_2752057).sum := by decide
  have hdescent : baseEnd_2752057 < baseStart_2752057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752081 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 9]
def baseStart_2752081 : Nat := 118140960795 + 2752081 * 2 ^ 59
def prefixEnd_2752081 : Nat := 4983230072969 + 3 ^ 40 * 2752081 * 2
def baseEnd_2752081 : Nat := 314031189579189378695759

theorem tailTrace_2752081 : CollatzResearch.WordTrace tailWord_2752081 prefixEnd_2752081 314031189579189378695759 := by
  unfold tailWord_2752081
  simp only [CollatzResearch.WordTrace]
  refine ⟨100376640342688029859864097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66917760228458686573242731 100376640342688029859864097)
  ·
    refine ⟨75282480257016022394898073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100376640342688029859864097 75282480257016022394898073)
    ·
      refine ⟨56461860192762016796173555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75282480257016022394898073 56461860192762016796173555)
      ·
        refine ⟨84692790289143025194260333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56461860192762016796173555 84692790289143025194260333)
        ·
          refine ⟨31759796358428634447847625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84692790289143025194260333 31759796358428634447847625)
          ·
            refine ⟨23819847268821475835885719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31759796358428634447847625 23819847268821475835885719)
            ·
              refine ⟨35729770903232213753828579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23819847268821475835885719 35729770903232213753828579)
              ·
                refine ⟨53594656354848320630742869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35729770903232213753828579 53594656354848320630742869)
                ·
                  refine ⟨314031189579189378695759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53594656354848320630742869 314031189579189378695759)
                  ·
                    rfl

theorem cell22_2752081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 9].length) (baseStart_2752081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752081 prefixEnd_2752081 := by exact prefixLift 2752081
  have htrace : WordTrace (prefixWord ++ tailWord_2752081) baseStart_2752081 baseEnd_2752081 := by
    simpa [prefixWord, tailWord_2752081, baseEnd_2752081] using wordTrace_append hprefix tailTrace_2752081
  have hstable : (prefixWord ++ tailWord_2752081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752081).length < 2 ^ (prefixWord ++ tailWord_2752081).sum := by decide
  have hdescent : baseEnd_2752081 < baseStart_2752081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752111 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 2, 8]
def baseStart_2752111 : Nat := 118140960795 + 2752111 * 2 ^ 59
def prefixEnd_2752111 : Nat := 4983230072969 + 3 ^ 40 * 2752111 * 2
def baseEnd_2752111 : Nat := 942103838350658057837185

theorem tailTrace_2752111 : CollatzResearch.WordTrace tailWord_2752111 prefixEnd_2752111 942103838350658057837185 := by
  unfold tailWord_2752111
  simp only [CollatzResearch.WordTrace]
  refine ⟨100377734532579344983456187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66918489688386229988970791 100377734532579344983456187)
  ·
    refine ⟨150566601798869017475184281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100377734532579344983456187 150566601798869017475184281)
    ·
      refine ⟨112924951349151763106388211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150566601798869017475184281 112924951349151763106388211)
      ·
        refine ⟨169387427023727644659582317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112924951349151763106388211 169387427023727644659582317)
        ·
          refine ⟨63520285133897866747343369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169387427023727644659582317 63520285133897866747343369)
          ·
            refine ⟨47640213850423400060507527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63520285133897866747343369 47640213850423400060507527)
            ·
              refine ⟨71460320775635100090761291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47640213850423400060507527 71460320775635100090761291)
              ·
                refine ⟨107190481163452650136141937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71460320775635100090761291 107190481163452650136141937)
                ·
                  refine ⟨80392860872589487602106453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107190481163452650136141937 80392860872589487602106453)
                  ·
                    refine ⟨942103838350658057837185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80392860872589487602106453 942103838350658057837185)
                    ·
                      rfl

theorem cell22_2752111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_2752111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752111 prefixEnd_2752111 := by exact prefixLift 2752111
  have htrace : WordTrace (prefixWord ++ tailWord_2752111) baseStart_2752111 baseEnd_2752111 := by
    simpa [prefixWord, tailWord_2752111, baseEnd_2752111] using wordTrace_append hprefix tailTrace_2752111
  have hstable : (prefixWord ++ tailWord_2752111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752111).length < 2 ^ (prefixWord ++ tailWord_2752111).sum := by decide
  have hdescent : baseEnd_2752111 < baseStart_2752111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752128 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 3, 4]
def baseStart_2752128 : Nat := 118140960795 + 2752128 * 2 ^ 59
def prefixEnd_2752128 : Nat := 4983230072969 + 3 ^ 40 * 2752128 * 2
def baseEnd_2752128 : Nat := 942109657798075680162133

theorem tailTrace_2752128 : CollatzResearch.WordTrace tailWord_2752128 prefixEnd_2752128 942109657798075680162133 := by
  unfold tailWord_2752128
  simp only [CollatzResearch.WordTrace]
  refine ⟨50189177286758878443412519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66918903049011837924550025 50189177286758878443412519)
  ·
    refine ⟨75283765930138317665118779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50189177286758878443412519 75283765930138317665118779)
    ·
      refine ⟨112925648895207476497678169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75283765930138317665118779 112925648895207476497678169)
      ·
        refine ⟨84694236671405607373258627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112925648895207476497678169 84694236671405607373258627)
        ·
          refine ⟨127041355007108411059887941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84694236671405607373258627 127041355007108411059887941)
          ·
            refine ⟨23820254063832827073728989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127041355007108411059887941 23820254063832827073728989)
            ·
              refine ⟨8932595273937310152648371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23820254063832827073728989 8932595273937310152648371)
              ·
                refine ⟨13398892910905965228972557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8932595273937310152648371 13398892910905965228972557)
                ·
                  refine ⟨5024584841589736960864709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13398892910905965228972557 5024584841589736960864709)
                  ·
                    refine ⟨942109657798075680162133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5024584841589736960864709 942109657798075680162133)
                    ·
                      rfl

theorem cell22_2752128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_2752128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752128 prefixEnd_2752128 := by exact prefixLift 2752128
  have htrace : WordTrace (prefixWord ++ tailWord_2752128) baseStart_2752128 baseEnd_2752128 := by
    simpa [prefixWord, tailWord_2752128, baseEnd_2752128] using wordTrace_append hprefix tailTrace_2752128
  have hstable : (prefixWord ++ tailWord_2752128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752128).length < 2 ^ (prefixWord ++ tailWord_2752128).sum := by decide
  have hdescent : baseEnd_2752128 < baseStart_2752128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752175 : List Nat := [1, 1, 2, 1, 2, 4, 1, 5, 2, 3]
def baseStart_2752175 : Nat := 118140960795 + 2752175 * 2 ^ 59
def prefixEnd_2752175 : Nat := 4983230072969 + 3 ^ 40 * 2752175 * 2
def baseEnd_2752175 : Nat := 942125746858583224236989

theorem tailTrace_2752175 : CollatzResearch.WordTrace tailWord_2752175 prefixEnd_2752175 942125746858583224236989 := by
  unfold tailWord_2752175
  simp only [CollatzResearch.WordTrace]
  refine ⟨100380068804347483913785979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66920045869564989275857319 100380068804347483913785979)
  ·
    refine ⟨150570103206521225870678969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100380068804347483913785979 150570103206521225870678969)
    ·
      refine ⟨112927577404890919403009227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150570103206521225870678969 112927577404890919403009227)
      ·
        refine ⟨169391366107336379104513841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112927577404890919403009227 169391366107336379104513841)
        ·
          refine ⟨127043524580502284328385381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169391366107336379104513841 127043524580502284328385381)
          ·
            refine ⟨23820660858844178311572259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127043524580502284328385381 23820660858844178311572259)
            ·
              refine ⟨35730991288266267467358389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23820660858844178311572259 35730991288266267467358389)
              ·
                refine ⟨3349780433274962575064849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35730991288266267467358389 3349780433274962575064849)
                ·
                  refine ⟨2512335324956221931298637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3349780433274962575064849 2512335324956221931298637)
                  ·
                    refine ⟨942125746858583224236989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2512335324956221931298637 942125746858583224236989)
                    ·
                      rfl

theorem cell22_2752175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 3].length) (baseStart_2752175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752175 prefixEnd_2752175 := by exact prefixLift 2752175
  have htrace : WordTrace (prefixWord ++ tailWord_2752175) baseStart_2752175 baseEnd_2752175 := by
    simpa [prefixWord, tailWord_2752175, baseEnd_2752175] using wordTrace_append hprefix tailTrace_2752175
  have hstable : (prefixWord ++ tailWord_2752175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752175).length < 2 ^ (prefixWord ++ tailWord_2752175).sum := by decide
  have hdescent : baseEnd_2752175 < baseStart_2752175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752190 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2752190 : Nat := 118140960795 + 2752190 * 2 ^ 59
def prefixEnd_2752190 : Nat := 4983230072969 + 3 ^ 40 * 2752190 * 2
def baseEnd_2752190 : Nat := 942130881665128185111943

theorem tailTrace_2752190 : CollatzResearch.WordTrace tailWord_2752190 prefixEnd_2752190 942130881665128185111943 := by
  unfold tailWord_2752190
  simp only [CollatzResearch.WordTrace]
  refine ⟨12547576987411642684447753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66920410599528760983721349 12547576987411642684447753)
  ·
    refine ⟨9410682740558732013335815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12547576987411642684447753 9410682740558732013335815)
    ·
      refine ⟨14116024110838098020003723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9410682740558732013335815 14116024110838098020003723)
      ·
        refine ⟨21174036166257147030005585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14116024110838098020003723 21174036166257147030005585)
        ·
          refine ⟨15880527124692860272504189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21174036166257147030005585 15880527124692860272504189)
          ·
            refine ⟨5955197671759822602189071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15880527124692860272504189 5955197671759822602189071)
            ·
              refine ⟨8932796507639733903283607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5955197671759822602189071 8932796507639733903283607)
              ·
                refine ⟨13399194761459600854925411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8932796507639733903283607 13399194761459600854925411)
                ·
                  refine ⟨20098792142189401282388117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13399194761459600854925411 20098792142189401282388117)
                  ·
                    refine ⟨942130881665128185111943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20098792142189401282388117 942130881665128185111943)
                    ·
                      rfl

theorem cell22_2752190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2752190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752190 prefixEnd_2752190 := by exact prefixLift 2752190
  have htrace : WordTrace (prefixWord ++ tailWord_2752190) baseStart_2752190 baseEnd_2752190 := by
    simpa [prefixWord, tailWord_2752190, baseEnd_2752190] using wordTrace_append hprefix tailTrace_2752190
  have hstable : (prefixWord ++ tailWord_2752190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752190).length < 2 ^ (prefixWord ++ tailWord_2752190).sum := by decide
  have hdescent : baseEnd_2752190 < baseStart_2752190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752237 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_2752237 : Nat := 118140960795 + 2752237 * 2 ^ 59
def prefixEnd_2752237 : Nat := 4983230072969 + 3 ^ 40 * 2752237 * 2
def baseEnd_2752237 : Nat := 942146970725635729186799

theorem tailTrace_2752237 : CollatzResearch.WordTrace tailWord_2752237 prefixEnd_2752237 942146970725635729186799 := by
  unfold tailWord_2752237
  simp only [CollatzResearch.WordTrace]
  refine ⟨100382330130122868502542965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66921553420081912335028643 100382330130122868502542965)
  ·
    refine ⟨9410843449699018922113403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100382330130122868502542965 9410843449699018922113403)
    ·
      refine ⟨14116265174548528383170105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9410843449699018922113403 14116265174548528383170105)
      ·
        refine ⟨10587198880911396287377579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14116265174548528383170105 10587198880911396287377579)
        ·
          refine ⟨15880798321367094431066369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10587198880911396287377579 15880798321367094431066369)
          ·
            refine ⟨11910598741025320823299777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15880798321367094431066369 11910598741025320823299777)
            ·
              refine ⟨8932949055768990617474833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11910598741025320823299777 8932949055768990617474833)
              ·
                refine ⟨6699711791826742963106125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8932949055768990617474833 6699711791826742963106125)
                ·
                  refine ⟨2512391921935028611164797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6699711791826742963106125 2512391921935028611164797)
                  ·
                    refine ⟨942146970725635729186799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2512391921935028611164797 942146970725635729186799)
                    ·
                      rfl

theorem cell22_2752237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_2752237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752237 prefixEnd_2752237 := by exact prefixLift 2752237
  have htrace : WordTrace (prefixWord ++ tailWord_2752237) baseStart_2752237 baseEnd_2752237 := by
    simpa [prefixWord, tailWord_2752237, baseEnd_2752237] using wordTrace_append hprefix tailTrace_2752237
  have hstable : (prefixWord ++ tailWord_2752237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752237).length < 2 ^ (prefixWord ++ tailWord_2752237).sum := by decide
  have hdescent : baseEnd_2752237 < baseStart_2752237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752248 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 4, 5]
def baseStart_2752248 : Nat := 118140960795 + 2752248 * 2 ^ 59
def prefixEnd_2752248 : Nat := 4983230072969 + 3 ^ 40 * 2752248 * 2
def baseEnd_2752248 : Nat := 942150736250435367161765

theorem tailTrace_2752248 : CollatzResearch.WordTrace tailWord_2752248 prefixEnd_2752248 942150736250435367161765 := by
  unfold tailWord_2752248
  simp only [CollatzResearch.WordTrace]
  refine ⟨50191365666541508690596699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66921820888722011587462265 50191365666541508690596699)
  ·
    refine ⟨75287048499812263035895049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50191365666541508690596699 75287048499812263035895049)
    ·
      refine ⟨56465286374859197276921287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75287048499812263035895049 56465286374859197276921287)
      ·
        refine ⟨84697929562288795915381931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56465286374859197276921287 84697929562288795915381931)
        ·
          refine ⟨127046894343433193873072897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84697929562288795915381931 127046894343433193873072897)
          ·
            refine ⟨95285170757574895404804673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127046894343433193873072897 95285170757574895404804673)
            ·
              refine ⟨71463878068181171553603505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95285170757574895404804673 71463878068181171553603505)
              ·
                refine ⟨53597908551135878665202629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71463878068181171553603505 53597908551135878665202629)
                ·
                  refine ⟨10049607853337977249725493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53597908551135878665202629 10049607853337977249725493)
                  ·
                    refine ⟨942150736250435367161765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10049607853337977249725493 942150736250435367161765)
                    ·
                      rfl

theorem cell22_2752248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_2752248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752248 prefixEnd_2752248 := by exact prefixLift 2752248
  have htrace : WordTrace (prefixWord ++ tailWord_2752248) baseStart_2752248 baseEnd_2752248 := by
    simpa [prefixWord, tailWord_2752248, baseEnd_2752248] using wordTrace_append hprefix tailTrace_2752248
  have hstable : (prefixWord ++ tailWord_2752248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752248).length < 2 ^ (prefixWord ++ tailWord_2752248).sum := by decide
  have hdescent : baseEnd_2752248 < baseStart_2752248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752262 : List Nat := [6, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2752262 : Nat := 118140960795 + 2752262 * 2 ^ 59
def prefixEnd_2752262 : Nat := 4983230072969 + 3 ^ 40 * 2752262 * 2
def baseEnd_2752262 : Nat := 314051842912181332437241

theorem tailTrace_2752262 : CollatzResearch.WordTrace tailWord_2752262 prefixEnd_2752262 314051842912181332437241 := by
  unfold tailWord_2752262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3136976311094759305381345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66922161303354865181468693 3136976311094759305381345)
  ·
    refine ⟨2352732233321069479036009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3136976311094759305381345 2352732233321069479036009)
    ·
      refine ⟨1764549174990802109277007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2352732233321069479036009 1764549174990802109277007)
      ·
        refine ⟨2646823762486203163915511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1764549174990802109277007 2646823762486203163915511)
        ·
          refine ⟨3970235643729304745873267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2646823762486203163915511 3970235643729304745873267)
          ·
            refine ⟨5955353465593957118809901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3970235643729304745873267 5955353465593957118809901)
            ·
              refine ⟨2233257549597733919553713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5955353465593957118809901 2233257549597733919553713)
              ·
                refine ⟨1674943162198300439665285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2233257549597733919553713 1674943162198300439665285)
                ·
                  refine ⟨314051842912181332437241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1674943162198300439665285 314051842912181332437241)
                  ·
                    rfl

theorem cell22_2752262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2752262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752262 prefixEnd_2752262 := by exact prefixLift 2752262
  have htrace : WordTrace (prefixWord ++ tailWord_2752262) baseStart_2752262 baseEnd_2752262 := by
    simpa [prefixWord, tailWord_2752262, baseEnd_2752262] using wordTrace_append hprefix tailTrace_2752262
  have hstable : (prefixWord ++ tailWord_2752262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752262).length < 2 ^ (prefixWord ++ tailWord_2752262).sum := by decide
  have hdescent : baseEnd_2752262 < baseStart_2752262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752314 : List Nat := [3, 1, 1, 1, 5, 2, 3, 1, 1, 4]
def baseStart_2752314 : Nat := 118140960795 + 2752314 * 2 ^ 59
def prefixEnd_2752314 : Nat := 4983230072969 + 3 ^ 40 * 2752314 * 2
def baseEnd_2752314 : Nat := 942173329399233195011563

theorem tailTrace_2752314 : CollatzResearch.WordTrace tailWord_2752314 prefixEnd_2752314 942173329399233195011563 := by
  unfold tailWord_2752314
  simp only [CollatzResearch.WordTrace]
  refine ⟨25096284637710977663273999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66923425700562607102063997 25096284637710977663273999)
  ·
    refine ⟨37644426956566466494910999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25096284637710977663273999 37644426956566466494910999)
    ·
      refine ⟨56466640434849699742366499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37644426956566466494910999 56466640434849699742366499)
      ·
        refine ⟨84699960652274549613549749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56466640434849699742366499 84699960652274549613549749)
        ·
          refine ⟨7940621311150739026270289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84699960652274549613549749 7940621311150739026270289)
          ·
            refine ⟨5955465983363054269702717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7940621311150739026270289 5955465983363054269702717)
            ·
              refine ⟨2233299743761145351138519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5955465983363054269702717 2233299743761145351138519)
              ·
                refine ⟨3349949615641718026707779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2233299743761145351138519 3349949615641718026707779)
                ·
                  refine ⟨5024924423462577040061669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3349949615641718026707779 5024924423462577040061669)
                  ·
                    refine ⟨942173329399233195011563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5024924423462577040061669 942173329399233195011563)
                    ·
                      rfl

theorem cell22_2752314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_2752314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752314 prefixEnd_2752314 := by exact prefixLift 2752314
  have htrace : WordTrace (prefixWord ++ tailWord_2752314) baseStart_2752314 baseEnd_2752314 := by
    simpa [prefixWord, tailWord_2752314, baseEnd_2752314] using wordTrace_append hprefix tailTrace_2752314
  have hstable : (prefixWord ++ tailWord_2752314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752314).length < 2 ^ (prefixWord ++ tailWord_2752314).sum := by decide
  have hdescent : baseEnd_2752314 < baseStart_2752314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752323 : List Nat := [1, 1, 1, 3, 1, 15]
def baseStart_2752323 : Nat := 118140960795 + 2752323 * 2 ^ 59
def prefixEnd_2752323 : Nat := 4983230072969 + 3 ^ 40 * 2752323 * 2
def baseEnd_2752323 : Nat := 11631807534360002117735

theorem tailTrace_2752323 : CollatzResearch.WordTrace tailWord_2752323 prefixEnd_2752323 11631807534360002117735 := by
  unfold tailWord_2752323
  simp only [CollatzResearch.WordTrace]
  refine ⟨100385466807811305190173623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66923644538540870126782415 100385466807811305190173623)
  ·
    refine ⟨150578200211716957785260435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100385466807811305190173623 150578200211716957785260435)
    ·
      refine ⟨225867300317575436677890653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150578200211716957785260435 225867300317575436677890653)
      ·
        refine ⟨84700237619090788754208995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225867300317575436677890653 84700237619090788754208995)
        ·
          refine ⟨127050356428636183131313493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84700237619090788754208995 127050356428636183131313493)
          ·
            refine ⟨11631807534360002117735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 127050356428636183131313493 11631807534360002117735)
            ·
              rfl

theorem cell22_2752323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 15].length) (baseStart_2752323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752323 prefixEnd_2752323 := by exact prefixLift 2752323
  have htrace : WordTrace (prefixWord ++ tailWord_2752323) baseStart_2752323 baseEnd_2752323 := by
    simpa [prefixWord, tailWord_2752323, baseEnd_2752323] using wordTrace_append hprefix tailTrace_2752323
  have hstable : (prefixWord ++ tailWord_2752323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752323).length < 2 ^ (prefixWord ++ tailWord_2752323).sum := by decide
  have hdescent : baseEnd_2752323 < baseStart_2752323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752325 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 2, 4]
def baseStart_2752325 : Nat := 118140960795 + 2752325 * 2 ^ 59
def prefixEnd_2752325 : Nat := 4983230072969 + 3 ^ 40 * 2752325 * 2
def baseEnd_2752325 : Nat := 942177094924032832986529

theorem tailTrace_2752325 : CollatzResearch.WordTrace tailWord_2752325 prefixEnd_2752325 942177094924032832986529 := by
  unfold tailWord_2752325
  simp only [CollatzResearch.WordTrace]
  refine ⟨100385539753804059531746429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66923693169202706354497619 100385539753804059531746429)
  ·
    refine ⟨37644577407676522324404911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100385539753804059531746429 37644577407676522324404911)
    ·
      refine ⟨56466866111514783486607367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37644577407676522324404911 56466866111514783486607367)
      ·
        refine ⟨84700299167272175229911051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56466866111514783486607367 84700299167272175229911051)
        ·
          refine ⟨127050448750908262844866577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84700299167272175229911051 127050448750908262844866577)
          ·
            refine ⟨95287836563181197133649933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127050448750908262844866577 95287836563181197133649933)
            ·
              refine ⟨35732938711192948925118725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95287836563181197133649933 35732938711192948925118725)
              ·
                refine ⟨6699926008348677923459761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35732938711192948925118725 6699926008348677923459761)
                ·
                  refine ⟨5024944506261508442594821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6699926008348677923459761 5024944506261508442594821)
                  ·
                    refine ⟨942177094924032832986529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5024944506261508442594821 942177094924032832986529)
                    ·
                      rfl

theorem cell22_2752325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_2752325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752325 prefixEnd_2752325 := by exact prefixLift 2752325
  have htrace : WordTrace (prefixWord ++ tailWord_2752325) baseStart_2752325 baseEnd_2752325 := by
    simpa [prefixWord, tailWord_2752325, baseEnd_2752325] using wordTrace_append hprefix tailTrace_2752325
  have hstable : (prefixWord ++ tailWord_2752325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752325).length < 2 ^ (prefixWord ++ tailWord_2752325).sum := by decide
  have hdescent : baseEnd_2752325 < baseStart_2752325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752327 : List Nat := [1, 1, 4, 1, 2, 1, 3, 4, 2, 3]
def baseStart_2752327 : Nat := 118140960795 + 2752327 * 2 ^ 59
def prefixEnd_2752327 : Nat := 4983230072969 + 3 ^ 40 * 2752327 * 2
def baseEnd_2752327 : Nat := 942177779564905494436523

theorem tailTrace_2752327 : CollatzResearch.WordTrace tailWord_2752327 prefixEnd_2752327 942177779564905494436523 := by
  unfold tailWord_2752327
  simp only [CollatzResearch.WordTrace]
  refine ⟨100385612699796813873319235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66923741799864542582212823 100385612699796813873319235)
  ·
    refine ⟨150578419049695220809978853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100385612699796813873319235 150578419049695220809978853)
    ·
      refine ⟨28233453571817853901871035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150578419049695220809978853 28233453571817853901871035)
      ·
        refine ⟨42350180357726780852806553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28233453571817853901871035 42350180357726780852806553)
        ·
          refine ⟨31762635268295085639604915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42350180357726780852806553 31762635268295085639604915)
          ·
            refine ⟨47643952902442628459407373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31762635268295085639604915 47643952902442628459407373)
            ·
              refine ⟨17866482338415985672277765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47643952902442628459407373 17866482338415985672277765)
              ·
                refine ⟨3349965438452997313552081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17866482338415985672277765 3349965438452997313552081)
                ·
                  refine ⟨2512474078839747985164061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3349965438452997313552081 2512474078839747985164061)
                  ·
                    refine ⟨942177779564905494436523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2512474078839747985164061 942177779564905494436523)
                    ·
                      rfl

theorem cell22_2752327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_2752327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752327 prefixEnd_2752327 := by exact prefixLift 2752327
  have htrace : WordTrace (prefixWord ++ tailWord_2752327) baseStart_2752327 baseEnd_2752327 := by
    simpa [prefixWord, tailWord_2752327, baseEnd_2752327] using wordTrace_append hprefix tailTrace_2752327
  have hstable : (prefixWord ++ tailWord_2752327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752327).length < 2 ^ (prefixWord ++ tailWord_2752327).sum := by decide
  have hdescent : baseEnd_2752327 < baseStart_2752327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752389 : List Nat := [1, 3, 1, 1, 3, 2, 1, 6, 1, 3]
def baseStart_2752389 : Nat := 118140960795 + 2752389 * 2 ^ 59
def prefixEnd_2752389 : Nat := 4983230072969 + 3 ^ 40 * 2752389 * 2
def baseEnd_2752389 : Nat := 942199003431957999386333

theorem tailTrace_2752389 : CollatzResearch.WordTrace tailWord_2752389 prefixEnd_2752389 942199003431957999386333 := by
  unfold tailWord_2752389
  simp only [CollatzResearch.WordTrace]
  refine ⟨100387874025572198462076221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66925249350381465641384147 100387874025572198462076221)
  ·
    refine ⟨37645452759589574423278583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100387874025572198462076221 37645452759589574423278583)
    ·
      refine ⟨56468179139384361634917875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37645452759589574423278583 56468179139384361634917875)
      ·
        refine ⟨84702268709076542452376813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56468179139384361634917875 84702268709076542452376813)
        ·
          refine ⟨31763350765903703419641305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84702268709076542452376813 31763350765903703419641305)
          ·
            refine ⟨23822513074427777564730979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31763350765903703419641305 23822513074427777564730979)
            ·
              refine ⟨35733769611641666347096469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23822513074427777564730979 35733769611641666347096469)
              ·
                refine ⟨1675020450545703110020147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35733769611641666347096469 1675020450545703110020147)
                ·
                  refine ⟨2512530675818554665030221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675020450545703110020147 2512530675818554665030221)
                  ·
                    refine ⟨942199003431957999386333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2512530675818554665030221 942199003431957999386333)
                    ·
                      rfl

theorem cell22_2752389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_2752389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752389 prefixEnd_2752389 := by exact prefixLift 2752389
  have htrace : WordTrace (prefixWord ++ tailWord_2752389) baseStart_2752389 baseEnd_2752389 := by
    simpa [prefixWord, tailWord_2752389, baseEnd_2752389] using wordTrace_append hprefix tailTrace_2752389
  have hstable : (prefixWord ++ tailWord_2752389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752389).length < 2 ^ (prefixWord ++ tailWord_2752389).sum := by decide
  have hdescent : baseEnd_2752389 < baseStart_2752389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752423 : List Nat := [1, 1, 6, 1, 2, 3, 1, 3, 1, 3]
def baseStart_2752423 : Nat := 118140960795 + 2752423 * 2 ^ 59
def prefixEnd_2752423 : Nat := 4983230072969 + 3 ^ 40 * 2752423 * 2
def baseEnd_2752423 : Nat := 942210642326793244036229

theorem tailTrace_2752423 : CollatzResearch.WordTrace tailWord_2752423 prefixEnd_2752423 942210642326793244036229 := by
  unfold tailWord_2752423
  simp only [CollatzResearch.WordTrace]
  refine ⟨100389114107449022268813923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66926076071632681512542615 100389114107449022268813923)
  ·
    refine ⟨150583671161173533403220885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100389114107449022268813923 150583671161173533403220885)
    ·
      refine ⟨7058609585680009378275979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 150583671161173533403220885 7058609585680009378275979)
      ·
        refine ⟨10587914378520014067413969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7058609585680009378275979 10587914378520014067413969)
        ·
          refine ⟨7940935783890010550560477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10587914378520014067413969 7940935783890010550560477)
          ·
            refine ⟨2977850918958753956460179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7940935783890010550560477 2977850918958753956460179)
            ·
              refine ⟨4466776378438130934690269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2977850918958753956460179 4466776378438130934690269)
              ·
                refine ⟨1675041141914299100508851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4466776378438130934690269 1675041141914299100508851)
                ·
                  refine ⟨2512561712871448650763277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675041141914299100508851 2512561712871448650763277)
                  ·
                    refine ⟨942210642326793244036229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2512561712871448650763277 942210642326793244036229)
                    ·
                      rfl

theorem cell22_2752423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_2752423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752423 prefixEnd_2752423 := by exact prefixLift 2752423
  have htrace : WordTrace (prefixWord ++ tailWord_2752423) baseStart_2752423 baseEnd_2752423 := by
    simpa [prefixWord, tailWord_2752423, baseEnd_2752423] using wordTrace_append hprefix tailTrace_2752423
  have hstable : (prefixWord ++ tailWord_2752423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752423).length < 2 ^ (prefixWord ++ tailWord_2752423).sum := by decide
  have hdescent : baseEnd_2752423 < baseStart_2752423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752462 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_2752462 : Nat := 118140960795 + 2752462 * 2 ^ 59
def prefixEnd_2752462 : Nat := 4983230072969 + 3 ^ 40 * 2752462 * 2
def baseEnd_2752462 : Nat := 942223992823810142311109

theorem tailTrace_2752462 : CollatzResearch.WordTrace tailWord_2752462 prefixEnd_2752462 942223992823810142311109 := by
  unfold tailWord_2752462
  simp only [CollatzResearch.WordTrace]
  refine ⟨12548817069288466491185455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66927024369538487952989093 12548817069288466491185455)
  ·
    refine ⟨18823225603932699736778183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12548817069288466491185455 18823225603932699736778183)
    ·
      refine ⟨28234838405899049605167275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18823225603932699736778183 28234838405899049605167275)
      ·
        refine ⟨42352257608848574407750913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28234838405899049605167275 42352257608848574407750913)
        ·
          refine ⟨31764193206636430805813185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42352257608848574407750913 31764193206636430805813185)
          ·
            refine ⟨23823144904977323104359889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31764193206636430805813185 23823144904977323104359889)
            ·
              refine ⟨17867358678732992328269917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23823144904977323104359889 17867358678732992328269917)
              ·
                refine ⟨6700259504524872123101219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17867358678732992328269917 6700259504524872123101219)
                ·
                  refine ⟨10050389256787308184651829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6700259504524872123101219 10050389256787308184651829)
                  ·
                    refine ⟨942223992823810142311109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10050389256787308184651829 942223992823810142311109)
                    ·
                      rfl

theorem cell22_2752462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_2752462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752462 prefixEnd_2752462 := by exact prefixLift 2752462
  have htrace : WordTrace (prefixWord ++ tailWord_2752462) baseStart_2752462 baseEnd_2752462 := by
    simpa [prefixWord, tailWord_2752462, baseEnd_2752462] using wordTrace_append hprefix tailTrace_2752462
  have hstable : (prefixWord ++ tailWord_2752462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752462).length < 2 ^ (prefixWord ++ tailWord_2752462).sum := by decide
  have hdescent : baseEnd_2752462 < baseStart_2752462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752494 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_2752494 : Nat := 118140960795 + 2752494 * 2 ^ 59
def prefixEnd_2752494 : Nat := 4983230072969 + 3 ^ 40 * 2752494 * 2
def baseEnd_2752494 : Nat := 942234947077772725511011

theorem tailTrace_2752494 : CollatzResearch.WordTrace tailWord_2752494 prefixEnd_2752494 942234947077772725511011 := by
  unfold tailWord_2752494
  simp only [CollatzResearch.WordTrace]
  refine ⟨12548962961273975174331067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66927802460127867596432357 12548962961273975174331067)
  ·
    refine ⟨18823444441910962761496601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12548962961273975174331067 18823444441910962761496601)
    ·
      refine ⟨14117583331433222071122451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18823444441910962761496601 14117583331433222071122451)
      ·
        refine ⟨21176374997149833106683677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14117583331433222071122451 21176374997149833106683677)
        ·
          refine ⟨7941140623931187415006379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21176374997149833106683677 7941140623931187415006379)
          ·
            refine ⟨11911710935896781122509569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7941140623931187415006379 11911710935896781122509569)
            ·
              refine ⟨8933783201922585841882177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11911710935896781122509569 8933783201922585841882177)
              ·
                refine ⟨6700337401441939381411633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8933783201922585841882177 6700337401441939381411633)
                ·
                  refine ⟨5025253051081454536058725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6700337401441939381411633 5025253051081454536058725)
                  ·
                    refine ⟨942234947077772725511011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5025253051081454536058725 942234947077772725511011)
                    ·
                      rfl

theorem cell22_2752494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_2752494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752494 prefixEnd_2752494 := by exact prefixLift 2752494
  have htrace : WordTrace (prefixWord ++ tailWord_2752494) baseStart_2752494 baseEnd_2752494 := by
    simpa [prefixWord, tailWord_2752494, baseEnd_2752494] using wordTrace_append hprefix tailTrace_2752494
  have hstable : (prefixWord ++ tailWord_2752494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752494).length < 2 ^ (prefixWord ++ tailWord_2752494).sum := by decide
  have hdescent : baseEnd_2752494 < baseStart_2752494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752524 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 3, 3]
def baseStart_2752524 : Nat := 118140960795 + 2752524 * 2 ^ 59
def prefixEnd_2752524 : Nat := 4983230072969 + 3 ^ 40 * 2752524 * 2
def baseEnd_2752524 : Nat := 942245216690862647260919

theorem tailTrace_2752524 : CollatzResearch.WordTrace tailWord_2752524 prefixEnd_2752524 942245216690862647260919 := by
  unfold tailWord_2752524
  simp only [CollatzResearch.WordTrace]
  refine ⟨50196398940041558259120313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66928531920055411012160417 50196398940041558259120313)
  ·
    refine ⟨37647299205031168694340235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50196398940041558259120313 37647299205031168694340235)
    ·
      refine ⟨56470948807546753041510353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37647299205031168694340235 56470948807546753041510353)
      ·
        refine ⟨42353211605660064781132765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56470948807546753041510353 42353211605660064781132765)
        ·
          refine ⟨15882454352122524292924787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42353211605660064781132765 15882454352122524292924787)
          ·
            refine ⟨23823681528183786439387181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15882454352122524292924787 23823681528183786439387181)
            ·
              refine ⟨8933880573068919914770193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23823681528183786439387181 8933880573068919914770193)
              ·
                refine ⟨6700410429801689936077645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8933880573068919914770193 6700410429801689936077645)
                ·
                  refine ⟨2512653911175633726029117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6700410429801689936077645 2512653911175633726029117)
                  ·
                    refine ⟨942245216690862647260919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2512653911175633726029117 942245216690862647260919)
                    ·
                      rfl

theorem cell22_2752524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_2752524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752524 prefixEnd_2752524 := by exact prefixLift 2752524
  have htrace : WordTrace (prefixWord ++ tailWord_2752524) baseStart_2752524 baseEnd_2752524 := by
    simpa [prefixWord, tailWord_2752524, baseEnd_2752524] using wordTrace_append hprefix tailTrace_2752524
  have hstable : (prefixWord ++ tailWord_2752524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752524).length < 2 ^ (prefixWord ++ tailWord_2752524).sum := by decide
  have hdescent : baseEnd_2752524 < baseStart_2752524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752554 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 7]
def baseStart_2752554 : Nat := 118140960795 + 2752554 * 2 ^ 59
def prefixEnd_2752554 : Nat := 4983230072969 + 3 ^ 40 * 2752554 * 2
def baseEnd_2752554 : Nat := 314085162101317523003609

theorem tailTrace_2752554 : CollatzResearch.WordTrace tailWord_2752554 prefixEnd_2752554 314085162101317523003609 := by
  unfold tailWord_2752554
  simp only [CollatzResearch.WordTrace]
  refine ⟨25098473017493607910458179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66929261379982954427888477 25098473017493607910458179)
  ·
    refine ⟨37647709526240411865687269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25098473017493607910458179 37647709526240411865687269)
    ·
      refine ⟨7058945536170077224816363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37647709526240411865687269 7058945536170077224816363)
      ·
        refine ⟨10588418304255115837224545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7058945536170077224816363 10588418304255115837224545)
        ·
          refine ⟨7941313728191336877918409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10588418304255115837224545 7941313728191336877918409)
          ·
            refine ⟨5955985296143502658438807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7941313728191336877918409 5955985296143502658438807)
            ·
              refine ⟨8933977944215253987658211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5955985296143502658438807 8933977944215253987658211)
              ·
                refine ⟨13400966916322880981487317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8933977944215253987658211 13400966916322880981487317)
                ·
                  refine ⟨314085162101317523003609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13400966916322880981487317 314085162101317523003609)
                  ·
                    rfl

theorem cell22_2752554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_2752554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752554 prefixEnd_2752554 := by exact prefixLift 2752554
  have htrace : WordTrace (prefixWord ++ tailWord_2752554) baseStart_2752554 baseEnd_2752554 := by
    simpa [prefixWord, tailWord_2752554, baseEnd_2752554] using wordTrace_append hprefix tailTrace_2752554
  have hstable : (prefixWord ++ tailWord_2752554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752554).length < 2 ^ (prefixWord ++ tailWord_2752554).sum := by decide
  have hdescent : baseEnd_2752554 < baseStart_2752554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752558 : List Nat := [4, 1, 3, 1, 1, 2, 2, 4, 1, 3]
def baseStart_2752558 : Nat := 118140960795 + 2752558 * 2 ^ 59
def prefixEnd_2752558 : Nat := 4983230072969 + 3 ^ 40 * 2752558 * 2
def baseEnd_2752558 : Nat := 942256855585697891910815

theorem tailTrace_2752558 : CollatzResearch.WordTrace tailWord_2752558 prefixEnd_2752558 942256855585697891910815 := by
  unfold tailWord_2752558
  simp only [CollatzResearch.WordTrace]
  refine ⟨12549254745244992540622291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66929358641306626883318885 12549254745244992540622291)
  ·
    refine ⟨18823882117867488810933437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12549254745244992540622291 18823882117867488810933437)
    ·
      refine ⟨7058955794200308304100039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18823882117867488810933437 7058955794200308304100039)
      ·
        refine ⟨10588433691300462456150059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7058955794200308304100039 10588433691300462456150059)
        ·
          refine ⟨15882650536950693684225089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10588433691300462456150059 15882650536950693684225089)
          ·
            refine ⟨11911987902713020263168817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15882650536950693684225089 11911987902713020263168817)
            ·
              refine ⟨8933990927034765197376613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11911987902713020263168817 8933990927034765197376613)
              ·
                refine ⟨1675123298819018474508115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8933990927034765197376613 1675123298819018474508115)
                ·
                  refine ⟨2512684948228527711762173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675123298819018474508115 2512684948228527711762173)
                  ·
                    refine ⟨942256855585697891910815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2512684948228527711762173 942256855585697891910815)
                    ·
                      rfl

theorem cell22_2752558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_2752558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752558 prefixEnd_2752558 := by exact prefixLift 2752558
  have htrace : WordTrace (prefixWord ++ tailWord_2752558) baseStart_2752558 baseEnd_2752558 := by
    simpa [prefixWord, tailWord_2752558, baseEnd_2752558] using wordTrace_append hprefix tailTrace_2752558
  have hstable : (prefixWord ++ tailWord_2752558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752558).length < 2 ^ (prefixWord ++ tailWord_2752558).sum := by decide
  have hdescent : baseEnd_2752558 < baseStart_2752558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752567 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 5, 4]
def baseStart_2752567 : Nat := 118140960795 + 2752567 * 2 ^ 59
def prefixEnd_2752567 : Nat := 4983230072969 + 3 ^ 40 * 2752567 * 2
def baseEnd_2752567 : Nat := 942259936469624868435787

theorem tailTrace_2752567 : CollatzResearch.WordTrace tailWord_2752567 prefixEnd_2752567 942259936469624868435787 := by
  unfold tailWord_2752567
  simp only [CollatzResearch.WordTrace]
  refine ⟨100394366218927334862055955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66929577479284889908037303 100394366218927334862055955)
  ·
    refine ⟨150591549328391002293083933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100394366218927334862055955 150591549328391002293083933)
    ·
      refine ⟨56471830998146625859906475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150591549328391002293083933 56471830998146625859906475)
      ·
        refine ⟨84707746497219938789859713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56471830998146625859906475 84707746497219938789859713)
        ·
          refine ⟨63530809872914954092394785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84707746497219938789859713 63530809872914954092394785)
          ·
            refine ⟨47648107404686215569296089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63530809872914954092394785 47648107404686215569296089)
            ·
              refine ⟨35736080553514661676972067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47648107404686215569296089 35736080553514661676972067)
              ·
                refine ⟨53604120830271992515458101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35736080553514661676972067 53604120830271992515458101)
                ·
                  refine ⟨5025386327837999298324197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53604120830271992515458101 5025386327837999298324197)
                  ·
                    refine ⟨942259936469624868435787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5025386327837999298324197 942259936469624868435787)
                    ·
                      rfl

theorem cell22_2752567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_2752567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752567 prefixEnd_2752567 := by exact prefixLift 2752567
  have htrace : WordTrace (prefixWord ++ tailWord_2752567) baseStart_2752567 baseEnd_2752567 := by
    simpa [prefixWord, tailWord_2752567, baseEnd_2752567] using wordTrace_append hprefix tailTrace_2752567
  have hstable : (prefixWord ++ tailWord_2752567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752567).length < 2 ^ (prefixWord ++ tailWord_2752567).sum := by decide
  have hdescent : baseEnd_2752567 < baseStart_2752567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752631 : List Nat := [1, 1, 3, 1, 1, 6, 1, 3, 2, 3]
def baseStart_2752631 : Nat := 118140960795 + 2752631 * 2 ^ 59
def prefixEnd_2752631 : Nat := 4983230072969 + 3 ^ 40 * 2752631 * 2
def baseEnd_2752631 : Nat := 942281844977550034835591

theorem tailTrace_2752631 : CollatzResearch.WordTrace tailWord_2752631 prefixEnd_2752631 942281844977550034835591 := by
  unfold tailWord_2752631
  simp only [CollatzResearch.WordTrace]
  refine ⟨100396700490695473792385747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66931133660463649194923831 100396700490695473792385747)
  ·
    refine ⟨150595050736043210688578621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100396700490695473792385747 150595050736043210688578621)
    ·
      refine ⟨56473144026016204008216983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150595050736043210688578621 56473144026016204008216983)
      ·
        refine ⟨84709716039024306012325475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56473144026016204008216983 84709716039024306012325475)
        ·
          refine ⟨127064574058536459018488213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84709716039024306012325475 127064574058536459018488213)
          ·
            refine ⟨5956151908993896516491635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 127064574058536459018488213 5956151908993896516491635)
            ·
              refine ⟨8934227863490844774737453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5956151908993896516491635 8934227863490844774737453)
              ·
                refine ⟨3350335448809066790526545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8934227863490844774737453 3350335448809066790526545)
                ·
                  refine ⟨2512751586606800092894909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3350335448809066790526545 2512751586606800092894909)
                  ·
                    refine ⟨942281844977550034835591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2512751586606800092894909 942281844977550034835591)
                    ·
                      rfl

theorem cell22_2752631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_2752631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752631 prefixEnd_2752631 := by exact prefixLift 2752631
  have htrace : WordTrace (prefixWord ++ tailWord_2752631) baseStart_2752631 baseEnd_2752631 := by
    simpa [prefixWord, tailWord_2752631, baseEnd_2752631] using wordTrace_append hprefix tailTrace_2752631
  have hstable : (prefixWord ++ tailWord_2752631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752631).length < 2 ^ (prefixWord ++ tailWord_2752631).sum := by decide
  have hdescent : baseEnd_2752631 < baseStart_2752631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752657 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 6, 6]
def baseStart_2752657 : Nat := 118140960795 + 2752657 * 2 ^ 59
def prefixEnd_2752657 : Nat := 4983230072969 + 3 ^ 40 * 2752657 * 2
def baseEnd_2752657 : Nat := 942290745308894633685511

theorem tailTrace_2752657 : CollatzResearch.WordTrace tailWord_2752657 prefixEnd_2752657 942290745308894633685511 := by
  unfold tailWord_2752657
  simp only [CollatzResearch.WordTrace]
  refine ⟨100397648788601280232832225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66931765859067520155221483 100397648788601280232832225)
  ·
    refine ⟨75298236591450960174624169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100397648788601280232832225 75298236591450960174624169)
    ·
      refine ⟨56473677443588220130968127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75298236591450960174624169 56473677443588220130968127)
      ·
        refine ⟨84710516165382330196452191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56473677443588220130968127 84710516165382330196452191)
        ·
          refine ⟨127065774248073495294678287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84710516165382330196452191 127065774248073495294678287)
          ·
            refine ⟨190598661372110242942017431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127065774248073495294678287 190598661372110242942017431)
            ·
              refine ⟨285897992058165364413026147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190598661372110242942017431 285897992058165364413026147)
              ·
                refine ⟨428846988087248046619539221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285897992058165364413026147 428846988087248046619539221)
                ·
                  refine ⟨20102202566589752185290901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 428846988087248046619539221 20102202566589752185290901)
                  ·
                    refine ⟨942290745308894633685511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20102202566589752185290901 942290745308894633685511)
                    ·
                      rfl

theorem cell22_2752657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_2752657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752657 prefixEnd_2752657 := by exact prefixLift 2752657
  have htrace : WordTrace (prefixWord ++ tailWord_2752657) baseStart_2752657 baseEnd_2752657 := by
    simpa [prefixWord, tailWord_2752657, baseEnd_2752657] using wordTrace_append hprefix tailTrace_2752657
  have hstable : (prefixWord ++ tailWord_2752657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752657).length < 2 ^ (prefixWord ++ tailWord_2752657).sum := by decide
  have hdescent : baseEnd_2752657 < baseStart_2752657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752766 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2752766 : Nat := 118140960795 + 2752766 * 2 ^ 59
def prefixEnd_2752766 : Nat := 4983230072969 + 3 ^ 40 * 2752766 * 2
def baseEnd_2752766 : Nat := 942328058236454682710177

theorem tailTrace_2752766 : CollatzResearch.WordTrace tailWord_2752766 prefixEnd_2752766 942328058236454682710177 := by
  unfold tailWord_2752766
  simp only [CollatzResearch.WordTrace]
  refine ⟨12550203043150798981068769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66934416230137594565700101 12550203043150798981068769)
  ·
    refine ⟨9412652282363099235801577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12550203043150798981068769 9412652282363099235801577)
    ·
      refine ⟨7059489211772324426851183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9412652282363099235801577 7059489211772324426851183)
      ·
        refine ⟨10589233817658486640276775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7059489211772324426851183 10589233817658486640276775)
        ·
          refine ⟨15883850726487729960415163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10589233817658486640276775 15883850726487729960415163)
          ·
            refine ⟨23825776089731594940622745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15883850726487729960415163 23825776089731594940622745)
            ·
              refine ⟨17869332067298696205467059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23825776089731594940622745 17869332067298696205467059)
              ·
                refine ⟨26803998100948044308200589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17869332067298696205467059 26803998100948044308200589)
                ·
                  refine ⟨10051499287855516615575221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26803998100948044308200589 10051499287855516615575221)
                  ·
                    refine ⟨942328058236454682710177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10051499287855516615575221 942328058236454682710177)
                    ·
                      rfl

theorem cell22_2752766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2752766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752766 prefixEnd_2752766 := by exact prefixLift 2752766
  have htrace : WordTrace (prefixWord ++ tailWord_2752766) baseStart_2752766 baseEnd_2752766 := by
    simpa [prefixWord, tailWord_2752766, baseEnd_2752766] using wordTrace_append hprefix tailTrace_2752766
  have hstable : (prefixWord ++ tailWord_2752766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752766).length < 2 ^ (prefixWord ++ tailWord_2752766).sum := by decide
  have hdescent : baseEnd_2752766 < baseStart_2752766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752800 : List Nat := [2, 1, 1, 5, 2, 1, 4, 1, 2, 3]
def baseStart_2752800 : Nat := 118140960795 + 2752800 * 2 ^ 59
def prefixEnd_2752800 : Nat := 4983230072969 + 3 ^ 40 * 2752800 * 2
def baseEnd_2752800 : Nat := 942339697131289927360073

theorem tailTrace_2752800 : CollatzResearch.WordTrace tailWord_2752800 prefixEnd_2752800 942339697131289927360073 := by
  unfold tailWord_2752800
  simp only [CollatzResearch.WordTrace]
  refine ⟨50201432213541607827643927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66935242951388810436858569 50201432213541607827643927)
  ·
    refine ⟨75302148320312411741465891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50201432213541607827643927 75302148320312411741465891)
    ·
      refine ⟨112953222480468617612198837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75302148320312411741465891 112953222480468617612198837)
      ·
        refine ⟨10589364607543932901143641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112953222480468617612198837 10589364607543932901143641)
        ·
          refine ⟨7942023455657949675857731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10589364607543932901143641 7942023455657949675857731)
          ·
            refine ⟨11913035183486924513786597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7942023455657949675857731 11913035183486924513786597)
            ·
              refine ⟨2233694096903798346334987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11913035183486924513786597 2233694096903798346334987)
              ·
                refine ⟨3350541145355697519502481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2233694096903798346334987 3350541145355697519502481)
                ·
                  refine ⟨2512905859016773139626861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3350541145355697519502481 2512905859016773139626861)
                  ·
                    refine ⟨942339697131289927360073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2512905859016773139626861 942339697131289927360073)
                    ·
                      rfl

theorem cell22_2752800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 2, 3].length) (baseStart_2752800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752800 prefixEnd_2752800 := by exact prefixLift 2752800
  have htrace : WordTrace (prefixWord ++ tailWord_2752800) baseStart_2752800 baseEnd_2752800 := by
    simpa [prefixWord, tailWord_2752800, baseEnd_2752800] using wordTrace_append hprefix tailTrace_2752800
  have hstable : (prefixWord ++ tailWord_2752800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752800).length < 2 ^ (prefixWord ++ tailWord_2752800).sum := by decide
  have hdescent : baseEnd_2752800 < baseStart_2752800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752824 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 9]
def baseStart_2752824 : Nat := 118140960795 + 2752824 * 2 ^ 59
def prefixEnd_2752824 : Nat := 4983230072969 + 3 ^ 40 * 2752824 * 2
def baseEnd_2752824 : Nat := 314115970940587288253333

theorem tailTrace_2752824 : CollatzResearch.WordTrace tailWord_2752824 prefixEnd_2752824 314115970940587288253333 := by
  unfold tailWord_2752824
  simp only [CollatzResearch.WordTrace]
  refine ⟨50201869889498133877080763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66935826519330845169441017 50201869889498133877080763)
  ·
    refine ⟨75302804834247200815621145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50201869889498133877080763 75302804834247200815621145)
    ·
      refine ⟨56477103625685400611715859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75302804834247200815621145 56477103625685400611715859)
      ·
        refine ⟨84715655438528100917573789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56477103625685400611715859 84715655438528100917573789)
        ·
          refine ⟨31768370789448037844090171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84715655438528100917573789 31768370789448037844090171)
          ·
            refine ⟨47652556184172056766135257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31768370789448037844090171 47652556184172056766135257)
            ·
              refine ⟨35739417138129042574601443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47652556184172056766135257 35739417138129042574601443)
              ·
                refine ⟨53609125707193563861902165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35739417138129042574601443 53609125707193563861902165)
                ·
                  refine ⟨314115970940587288253333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53609125707193563861902165 314115970940587288253333)
                  ·
                    rfl

theorem cell22_2752824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 9].length) (baseStart_2752824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752824 prefixEnd_2752824 := by exact prefixLift 2752824
  have htrace : WordTrace (prefixWord ++ tailWord_2752824) baseStart_2752824 baseEnd_2752824 := by
    simpa [prefixWord, tailWord_2752824, baseEnd_2752824] using wordTrace_append hprefix tailTrace_2752824
  have hstable : (prefixWord ++ tailWord_2752824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752824).length < 2 ^ (prefixWord ++ tailWord_2752824).sum := by decide
  have hdescent : baseEnd_2752824 < baseStart_2752824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752903 : List Nat := [1, 1, 4, 2, 2, 1, 1, 6, 4]
def baseStart_2752903 : Nat := 118140960795 + 2752903 * 2 ^ 59
def prefixEnd_2752903 : Nat := 4983230072969 + 3 ^ 40 * 2752903 * 2
def baseEnd_2752903 : Nat := 314124985378743997344919

theorem tailTrace_2752903 : CollatzResearch.WordTrace tailWord_2752903 prefixEnd_2752903 314124985378743997344919 := by
  unfold tailWord_2752903
  simp only [CollatzResearch.WordTrace]
  refine ⟨100406621145710064246287363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66937747430473376164191575 100406621145710064246287363)
  ·
    refine ⟨150609931718565096369431045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100406621145710064246287363 150609931718565096369431045)
    ·
      refine ⟨28239362197230955569268321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150609931718565096369431045 28239362197230955569268321)
      ·
        refine ⟨21179521647923216676951241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28239362197230955569268321 21179521647923216676951241)
        ·
          refine ⟨15884641235942412507713431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21179521647923216676951241 15884641235942412507713431)
          ·
            refine ⟨23826961853913618761570147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15884641235942412507713431 23826961853913618761570147)
            ·
              refine ⟨35740442780870428142355221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23826961853913618761570147 35740442780870428142355221)
              ·
                refine ⟨1675333255353301319172901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35740442780870428142355221 1675333255353301319172901)
                ·
                  refine ⟨314124985378743997344919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1675333255353301319172901 314124985378743997344919)
                  ·
                    rfl

theorem cell22_2752903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 4].length) (baseStart_2752903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752903 prefixEnd_2752903 := by exact prefixLift 2752903
  have htrace : WordTrace (prefixWord ++ tailWord_2752903) baseStart_2752903 baseEnd_2752903 := by
    simpa [prefixWord, tailWord_2752903, baseEnd_2752903] using wordTrace_append hprefix tailTrace_2752903
  have hstable : (prefixWord ++ tailWord_2752903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752903).length < 2 ^ (prefixWord ++ tailWord_2752903).sum := by decide
  have hdescent : baseEnd_2752903 < baseStart_2752903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752931 : List Nat := [1, 1, 1, 4, 1, 5, 1, 8]
def baseStart_2752931 : Nat := 118140960795 + 2752931 * 2 ^ 59
def prefixEnd_2752931 : Nat := 4983230072969 + 3 ^ 40 * 2752931 * 2
def baseEnd_2752931 : Nat := 104709393456494361370519

theorem tailTrace_2752931 : CollatzResearch.WordTrace tailWord_2752931 prefixEnd_2752931 104709393456494361370519 := by
  unfold tailWord_2752931
  simp only [CollatzResearch.WordTrace]
  refine ⟨100407642389608625028306647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66938428259739083352204431 100407642389608625028306647)
  ·
    refine ⟨150611463584412937542459971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100407642389608625028306647 150611463584412937542459971)
    ·
      refine ⟨225917195376619406313689957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150611463584412937542459971 225917195376619406313689957)
      ·
        refine ⟨42359474133116138683816867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225917195376619406313689957 42359474133116138683816867)
        ·
          refine ⟨63539211199674208025725301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42359474133116138683816867 63539211199674208025725301)
          ·
            refine ⟨5956801049969457002411747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63539211199674208025725301 5956801049969457002411747)
            ·
              refine ⟨8935201574954185503617621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5956801049969457002411747 8935201574954185503617621)
              ·
                refine ⟨104709393456494361370519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8935201574954185503617621 104709393456494361370519)
                ·
                  rfl

theorem cell22_2752931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 8].length) (baseStart_2752931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2752931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2752931 prefixEnd_2752931 := by exact prefixLift 2752931
  have htrace : WordTrace (prefixWord ++ tailWord_2752931) baseStart_2752931 baseEnd_2752931 := by
    simpa [prefixWord, tailWord_2752931, baseEnd_2752931] using wordTrace_append hprefix tailTrace_2752931
  have hstable : (prefixWord ++ tailWord_2752931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752931).length < 2 ^ (prefixWord ++ tailWord_2752931).sum := by decide
  have hdescent : baseEnd_2752931 < baseStart_2752931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753038 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_2753038 : Nat := 118140960795 + 2753038 * 2 ^ 59
def prefixEnd_2753038 : Nat := 4983230072969 + 3 ^ 40 * 2753038 * 2
def baseEnd_2753038 : Nat := 314140389798378879969781

theorem tailTrace_2753038 : CollatzResearch.WordTrace tailWord_2753038 prefixEnd_2753038 314140389798378879969781 := by
  unfold tailWord_2753038
  simp only [CollatzResearch.WordTrace]
  refine ⟨12551443125027622787806471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66941030000147321534967845 12551443125027622787806471)
  ·
    refine ⟨18827164687541434181709707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12551443125027622787806471 18827164687541434181709707)
    ·
      refine ⟨28240747031312151272564561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18827164687541434181709707 28240747031312151272564561)
      ·
        refine ⟨21180560273484113454423421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28240747031312151272564561 21180560273484113454423421)
        ·
          refine ⟨7942710102556542545408783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21180560273484113454423421 7942710102556542545408783)
          ·
            refine ⟨11914065153834813818113175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7942710102556542545408783 11914065153834813818113175)
            ·
              refine ⟨17871097730752220727169763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11914065153834813818113175 17871097730752220727169763)
              ·
                refine ⟨26806646596128331090754645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17871097730752220727169763 26806646596128331090754645)
                ·
                  refine ⟨314140389798378879969781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26806646596128331090754645 314140389798378879969781)
                  ·
                    rfl

theorem cell22_2753038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_2753038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753038 prefixEnd_2753038 := by exact prefixLift 2753038
  have htrace : WordTrace (prefixWord ++ tailWord_2753038) baseStart_2753038 baseEnd_2753038 := by
    simpa [prefixWord, tailWord_2753038, baseEnd_2753038] using wordTrace_append hprefix tailTrace_2753038
  have hstable : (prefixWord ++ tailWord_2753038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753038).length < 2 ^ (prefixWord ++ tailWord_2753038).sum := by decide
  have hdescent : baseEnd_2753038 < baseStart_2753038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753068 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 2, 4]
def baseStart_2753068 : Nat := 118140960795 + 2753068 * 2 ^ 59
def prefixEnd_2753068 : Nat := 4983230072969 + 3 ^ 40 * 2753068 * 2
def baseEnd_2753068 : Nat := 942431439008226561659251

theorem tailTrace_2753068 : CollatzResearch.WordTrace tailWord_2753068 prefixEnd_2753068 942431439008226561659251 := by
  unfold tailWord_2753068
  simp only [CollatzResearch.WordTrace]
  refine ⟨50206319595056148713021929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66941759460074864950695905 50206319595056148713021929)
  ·
    refine ⟨37654739696292111534766447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50206319595056148713021929 37654739696292111534766447)
    ·
      refine ⟨56482109544438167302149671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37654739696292111534766447 56482109544438167302149671)
      ·
        refine ⟨84723164316657250953224507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56482109544438167302149671 84723164316657250953224507)
        ·
          refine ⟨127084746474985876429836761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84723164316657250953224507 127084746474985876429836761)
          ·
            refine ⟨95313559856239407322377571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127084746474985876429836761 95313559856239407322377571)
            ·
              refine ⟨142970339784359110983566357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95313559856239407322377571 142970339784359110983566357)
              ·
                refine ⟨6701734677391833327354673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142970339784359110983566357 6701734677391833327354673)
                ·
                  refine ⟨5026301008043874995516005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6701734677391833327354673 5026301008043874995516005)
                  ·
                    refine ⟨942431439008226561659251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5026301008043874995516005 942431439008226561659251)
                    ·
                      rfl

theorem cell22_2753068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_2753068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753068 prefixEnd_2753068 := by exact prefixLift 2753068
  have htrace : WordTrace (prefixWord ++ tailWord_2753068) baseStart_2753068 baseEnd_2753068 := by
    simpa [prefixWord, tailWord_2753068, baseEnd_2753068] using wordTrace_append hprefix tailTrace_2753068
  have hstable : (prefixWord ++ tailWord_2753068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753068).length < 2 ^ (prefixWord ++ tailWord_2753068).sum := by decide
  have hdescent : baseEnd_2753068 < baseStart_2753068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753087 : List Nat := [1, 1, 2, 2, 3, 2, 5, 1, 2, 3]
def baseStart_2753087 : Nat := 118140960795 + 2753087 * 2 ^ 59
def prefixEnd_2753087 : Nat := 4983230072969 + 3 ^ 40 * 2753087 * 2
def baseEnd_2753087 : Nat := 942437943096516845434193

theorem tailTrace_2753087 : CollatzResearch.WordTrace tailWord_2753087 prefixEnd_2753087 942437943096516845434193 := by
  unfold tailWord_2753087
  simp only [CollatzResearch.WordTrace]
  refine ⟨100413332177043463670985515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66942221451362309113990343 100413332177043463670985515)
  ·
    refine ⟨150619998265565195506478273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100413332177043463670985515 150619998265565195506478273)
    ·
      refine ⟨112964998699173896629858705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150619998265565195506478273 112964998699173896629858705)
      ·
        refine ⟨84723749024380422472394029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112964998699173896629858705 84723749024380422472394029)
        ·
          refine ⟨31771405884142658427147761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84723749024380422472394029 31771405884142658427147761)
          ·
            refine ⟨23828554413106993820360821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31771405884142658427147761 23828554413106993820360821)
            ·
              refine ⟨2233926976228780670658827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23828554413106993820360821 2233926976228780670658827)
              ·
                refine ⟨3350890464343171005988241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2233926976228780670658827 3350890464343171005988241)
                ·
                  refine ⟨2513167848257378254491181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3350890464343171005988241 2513167848257378254491181)
                  ·
                    refine ⟨942437943096516845434193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2513167848257378254491181 942437943096516845434193)
                    ·
                      rfl

theorem cell22_2753087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 2, 3].length) (baseStart_2753087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753087 prefixEnd_2753087 := by exact prefixLift 2753087
  have htrace : WordTrace (prefixWord ++ tailWord_2753087) baseStart_2753087 baseEnd_2753087 := by
    simpa [prefixWord, tailWord_2753087, baseEnd_2753087] using wordTrace_append hprefix tailTrace_2753087
  have hstable : (prefixWord ++ tailWord_2753087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753087).length < 2 ^ (prefixWord ++ tailWord_2753087).sum := by decide
  have hdescent : baseEnd_2753087 < baseStart_2753087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753132 : List Nat := [2, 2, 1, 1, 3, 1, 2, 6, 1, 3]
def baseStart_2753132 : Nat := 118140960795 + 2753132 * 2 ^ 59
def prefixEnd_2753132 : Nat := 4983230072969 + 3 ^ 40 * 2753132 * 2
def baseEnd_2753132 : Nat := 942453347516151728059055

theorem tailTrace_2753132 : CollatzResearch.WordTrace tailWord_2753132 prefixEnd_2753132 942453347516151728059055 := by
  unfold tailWord_2753132
  simp only [CollatzResearch.WordTrace]
  refine ⟨50207486730940218178186825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66943315641253624237582433 50207486730940218178186825)
  ·
    refine ⟨37655615048205163633640119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50207486730940218178186825 37655615048205163633640119)
    ·
      refine ⟨56483422572307745450460179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37655615048205163633640119 56483422572307745450460179)
      ·
        refine ⟨84725133858461618175690269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56483422572307745450460179 84725133858461618175690269)
        ·
          refine ⟨31771925196923106815883851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84725133858461618175690269 31771925196923106815883851)
          ·
            refine ⟨47657887795384660223825777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31771925196923106815883851 47657887795384660223825777)
            ·
              refine ⟨35743415846538495167869333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47657887795384660223825777 35743415846538495167869333)
              ·
                refine ⟨1675472617806491960993875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35743415846538495167869333 1675472617806491960993875)
                ·
                  refine ⟨2513208926709737941490813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675472617806491960993875 2513208926709737941490813)
                  ·
                    refine ⟨942453347516151728059055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2513208926709737941490813 942453347516151728059055)
                    ·
                      rfl

theorem cell22_2753132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_2753132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753132 prefixEnd_2753132 := by exact prefixLift 2753132
  have htrace : WordTrace (prefixWord ++ tailWord_2753132) baseStart_2753132 baseEnd_2753132 := by
    simpa [prefixWord, tailWord_2753132, baseEnd_2753132] using wordTrace_append hprefix tailTrace_2753132
  have hstable : (prefixWord ++ tailWord_2753132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753132).length < 2 ^ (prefixWord ++ tailWord_2753132).sum := by decide
  have hdescent : baseEnd_2753132 < baseStart_2753132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753143 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 2, 5]
def baseStart_2753143 : Nat := 118140960795 + 2753143 * 2 ^ 59
def prefixEnd_2753143 : Nat := 4983230072969 + 3 ^ 40 * 2753143 * 2
def baseEnd_2753143 : Nat := 942457113040951366034021

theorem tailTrace_2753143 : CollatzResearch.WordTrace tailWord_2753143 prefixEnd_2753143 942457113040951366034021 := by
  unfold tailWord_2753143
  simp only [CollatzResearch.WordTrace]
  refine ⟨100415374664840585235024083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66943583109893723490016055 100415374664840585235024083)
  ·
    refine ⟨150623061997260877852536125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100415374664840585235024083 150623061997260877852536125)
    ·
      refine ⟨56483648248972829194701047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150623061997260877852536125 56483648248972829194701047)
      ·
        refine ⟨84725472373459243792051571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56483648248972829194701047 84725472373459243792051571)
        ·
          refine ⟨127088208560188865688077357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84725472373459243792051571 127088208560188865688077357)
          ·
            refine ⟨47658078210070824633029009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127088208560188865688077357 47658078210070824633029009)
            ·
              refine ⟨35743558657553118474771757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47658078210070824633029009 35743558657553118474771757)
              ·
                refine ⟨13403834496582419428039409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35743558657553118474771757 13403834496582419428039409)
                ·
                  refine ⟨10052875872436814571029557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13403834496582419428039409 10052875872436814571029557)
                  ·
                    refine ⟨942457113040951366034021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10052875872436814571029557 942457113040951366034021)
                    ·
                      rfl

theorem cell22_2753143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_2753143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753143 prefixEnd_2753143 := by exact prefixLift 2753143
  have htrace : WordTrace (prefixWord ++ tailWord_2753143) baseStart_2753143 baseEnd_2753143 := by
    simpa [prefixWord, tailWord_2753143, baseEnd_2753143] using wordTrace_append hprefix tailTrace_2753143
  have hstable : (prefixWord ++ tailWord_2753143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753143).length < 2 ^ (prefixWord ++ tailWord_2753143).sum := by decide
  have hdescent : baseEnd_2753143 < baseStart_2753143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753145 : List Nat := [1, 2, 1, 3, 3, 3, 1, 3, 5]
def baseStart_2753145 : Nat := 118140960795 + 2753145 * 2 ^ 59
def prefixEnd_2753145 : Nat := 4983230072969 + 3 ^ 40 * 2753145 * 2
def baseEnd_2753145 : Nat := 314152599227274675828005

theorem tailTrace_2753145 : CollatzResearch.WordTrace tailWord_2753145 prefixEnd_2753145 314152599227274675828005 := by
  unfold tailWord_2753145
  simp only [CollatzResearch.WordTrace]
  refine ⟨100415447610833339576596889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66943631740555559717731259 100415447610833339576596889)
  ·
    refine ⟨75311585708125004682447667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100415447610833339576596889 75311585708125004682447667)
    ·
      refine ⟨112967378562187507023671501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75311585708125004682447667 112967378562187507023671501)
      ·
        refine ⟨42362766960820315133876813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112967378562187507023671501 42362766960820315133876813)
        ·
          refine ⟨15886037610307618175203805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42362766960820315133876813 15886037610307618175203805)
          ·
            refine ⟨5957264103865356815701427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15886037610307618175203805 5957264103865356815701427)
            ·
              refine ⟨8935896155798035223552141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5957264103865356815701427 8935896155798035223552141)
              ·
                refine ⟨3350961058424263208832053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8935896155798035223552141 3350961058424263208832053)
                ·
                  refine ⟨314152599227274675828005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3350961058424263208832053 314152599227274675828005)
                  ·
                    rfl

theorem cell22_2753145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 5].length) (baseStart_2753145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753145 prefixEnd_2753145 := by exact prefixLift 2753145
  have htrace : WordTrace (prefixWord ++ tailWord_2753145) baseStart_2753145 baseEnd_2753145 := by
    simpa [prefixWord, tailWord_2753145, baseEnd_2753145] using wordTrace_append hprefix tailTrace_2753145
  have hstable : (prefixWord ++ tailWord_2753145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753145).length < 2 ^ (prefixWord ++ tailWord_2753145).sum := by decide
  have hdescent : baseEnd_2753145 < baseStart_2753145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753194 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2753194 : Nat := 118140960795 + 2753194 * 2 ^ 59
def prefixEnd_2753194 : Nat := 4983230072969 + 3 ^ 40 * 2753194 * 2
def baseEnd_2753194 : Nat := 942474571383204233008865

theorem tailTrace_2753194 : CollatzResearch.WordTrace tailWord_2753194 prefixEnd_2753194 942474571383204233008865 := by
  unfold tailWord_2753194
  simp only [CollatzResearch.WordTrace]
  refine ⟨25104308696913955236282659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66944823191770547296753757 25104308696913955236282659)
  ·
    refine ⟨37656463045370932854423989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25104308696913955236282659 37656463045370932854423989)
    ·
      refine ⟨3530293410503524955102249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37656463045370932854423989 3530293410503524955102249)
      ·
        refine ⟨2647720057877643716326687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3530293410503524955102249 2647720057877643716326687)
        ·
          refine ⟨3971580086816465574490031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2647720057877643716326687 3971580086816465574490031)
          ·
            refine ⟨5957370130224698361735047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3971580086816465574490031 5957370130224698361735047)
            ·
              refine ⟨8936055195337047542602571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5957370130224698361735047 8936055195337047542602571)
              ·
                refine ⟨13404082793005571313903857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8936055195337047542602571 13404082793005571313903857)
                ·
                  refine ⟨10053062094754178485427893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13404082793005571313903857 10053062094754178485427893)
                  ·
                    refine ⟨942474571383204233008865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10053062094754178485427893 942474571383204233008865)
                    ·
                      rfl

theorem cell22_2753194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2753194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753194 prefixEnd_2753194 := by exact prefixLift 2753194
  have htrace : WordTrace (prefixWord ++ tailWord_2753194) baseStart_2753194 baseEnd_2753194 := by
    simpa [prefixWord, tailWord_2753194, baseEnd_2753194] using wordTrace_append hprefix tailTrace_2753194
  have hstable : (prefixWord ++ tailWord_2753194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753194).length < 2 ^ (prefixWord ++ tailWord_2753194).sum := by decide
  have hdescent : baseEnd_2753194 < baseStart_2753194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753239 : List Nat := [1, 1, 3, 2, 1, 6, 1, 2, 2, 3]
def baseStart_2753239 : Nat := 118140960795 + 2753239 * 2 ^ 59
def prefixEnd_2753239 : Nat := 4983230072969 + 3 ^ 40 * 2753239 * 2
def baseEnd_2753239 : Nat := 942489975802839115633727

theorem tailTrace_2753239 : CollatzResearch.WordTrace tailWord_2753239 prefixEnd_2753239 942489975802839115633727 := by
  unfold tailWord_2753239
  simp only [CollatzResearch.WordTrace]
  refine ⟨100418876072492793630518771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66945917381661862420345847 100418876072492793630518771)
  ·
    refine ⟨150628314108739190445778157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100418876072492793630518771 150628314108739190445778157)
    ·
      refine ⟨56485617790777196417166809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150628314108739190445778157 56485617790777196417166809)
      ·
        refine ⟨42364213343082897312875107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56485617790777196417166809 42364213343082897312875107)
        ·
          refine ⟨63546320014624345969312661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42364213343082897312875107 63546320014624345969312661)
          ·
            refine ⟨2978733750685516217311531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 63546320014624345969312661 2978733750685516217311531)
            ·
              refine ⟨4468100626028274325967297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2978733750685516217311531 4468100626028274325967297)
              ·
                refine ⟨3351075469521205744475473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4468100626028274325967297 3351075469521205744475473)
                ·
                  refine ⟨2513306602140904308356605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3351075469521205744475473 2513306602140904308356605)
                  ·
                    refine ⟨942489975802839115633727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2513306602140904308356605 942489975802839115633727)
                    ·
                      rfl

theorem cell22_2753239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_2753239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753239 prefixEnd_2753239 := by exact prefixLift 2753239
  have htrace : WordTrace (prefixWord ++ tailWord_2753239) baseStart_2753239 baseEnd_2753239 := by
    simpa [prefixWord, tailWord_2753239, baseEnd_2753239] using wordTrace_append hprefix tailTrace_2753239
  have hstable : (prefixWord ++ tailWord_2753239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753239).length < 2 ^ (prefixWord ++ tailWord_2753239).sum := by decide
  have hdescent : baseEnd_2753239 < baseStart_2753239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753256 : List Nat := [2, 1, 4, 1, 4, 1, 3, 1, 2, 3]
def baseStart_2753256 : Nat := 118140960795 + 2753256 * 2 ^ 59
def prefixEnd_2753256 : Nat := 4983230072969 + 3 ^ 40 * 2753256 * 2
def baseEnd_2753256 : Nat := 942495795250256737958675

theorem tailTrace_2753256 : CollatzResearch.WordTrace tailWord_2753256 prefixEnd_2753256 942495795250256737958675 := by
  unfold tailWord_2753256
  simp only [CollatzResearch.WordTrace]
  refine ⟨50209748056715602766943811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66946330742287470355925081 50209748056715602766943811)
  ·
    refine ⟨75314622085073404150415717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50209748056715602766943811 75314622085073404150415717)
    ·
      refine ⟨14121491640951263278202947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75314622085073404150415717 14121491640951263278202947)
      ·
        refine ⟨21182237461426894917304421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14121491640951263278202947 21182237461426894917304421)
        ·
          refine ⟨3971669524017542796994579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21182237461426894917304421 3971669524017542796994579)
          ·
            refine ⟨5957504286026314195491869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3971669524017542796994579 5957504286026314195491869)
            ·
              refine ⟨2234064107259867823309451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5957504286026314195491869 2234064107259867823309451)
              ·
                refine ⟨3351096160889801734964177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234064107259867823309451 3351096160889801734964177)
                ·
                  refine ⟨2513322120667351301223133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3351096160889801734964177 2513322120667351301223133)
                  ·
                    refine ⟨942495795250256737958675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2513322120667351301223133 942495795250256737958675)
                    ·
                      rfl

theorem cell22_2753256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_2753256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753256 prefixEnd_2753256 := by exact prefixLift 2753256
  have htrace : WordTrace (prefixWord ++ tailWord_2753256) baseStart_2753256 baseEnd_2753256 := by
    simpa [prefixWord, tailWord_2753256, baseEnd_2753256] using wordTrace_append hprefix tailTrace_2753256
  have hstable : (prefixWord ++ tailWord_2753256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753256).length < 2 ^ (prefixWord ++ tailWord_2753256).sum := by decide
  have hdescent : baseEnd_2753256 < baseStart_2753256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753301 : List Nat := [1, 3, 2, 1, 2, 2, 5, 2, 1, 3]
def baseStart_2753301 : Nat := 118140960795 + 2753301 * 2 ^ 59
def prefixEnd_2753301 : Nat := 4983230072969 + 3 ^ 40 * 2753301 * 2
def baseEnd_2753301 : Nat := 942511199669891620583537

theorem tailTrace_2753301 : CollatzResearch.WordTrace tailWord_2753301 prefixEnd_2753301 942511199669891620583537 := by
  unfold tailWord_2753301
  simp only [CollatzResearch.WordTrace]
  refine ⟨100421137398268178219275757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66947424932178785479517171 100421137398268178219275757)
  ·
    refine ⟨37657926524350566832228409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100421137398268178219275757 37657926524350566832228409)
    ·
      refine ⟨28243444893262925124171307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37657926524350566832228409 28243444893262925124171307)
      ·
        refine ⟨42365167339894387686256961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28243444893262925124171307 42365167339894387686256961)
        ·
          refine ⟨31773875504920790764692721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42365167339894387686256961 31773875504920790764692721)
          ·
            refine ⟨23830406628690593073519541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31773875504920790764692721 23830406628690593073519541)
            ·
              refine ⟨2234100621439743100642457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23830406628690593073519541 2234100621439743100642457)
              ·
                refine ⟨1675575466079807325481843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2234100621439743100642457 1675575466079807325481843)
                ·
                  refine ⟨2513363199119710988222765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675575466079807325481843 2513363199119710988222765)
                  ·
                    refine ⟨942511199669891620583537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2513363199119710988222765 942511199669891620583537)
                    ·
                      rfl

theorem cell22_2753301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_2753301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753301 prefixEnd_2753301 := by exact prefixLift 2753301
  have htrace : WordTrace (prefixWord ++ tailWord_2753301) baseStart_2753301 baseEnd_2753301 := by
    simpa [prefixWord, tailWord_2753301, baseEnd_2753301] using wordTrace_append hprefix tailTrace_2753301
  have hstable : (prefixWord ++ tailWord_2753301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753301).length < 2 ^ (prefixWord ++ tailWord_2753301).sum := by decide
  have hdescent : baseEnd_2753301 < baseStart_2753301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753314 : List Nat := [3, 3, 1, 1, 2, 2, 4, 1, 5]
def baseStart_2753314 : Nat := 118140960795 + 2753314 * 2 ^ 59
def prefixEnd_2753314 : Nat := 4983230072969 + 3 ^ 40 * 2753314 * 2
def baseEnd_2753314 : Nat := 314171883278521306669499

theorem tailTrace_2753314 : CollatzResearch.WordTrace tailWord_2753314 prefixEnd_2753314 314171883278521306669499 := by
  unfold tailWord_2753314
  simp only [CollatzResearch.WordTrace]
  refine ⟨25105402886805270359874749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66947741031480720959665997 25105402886805270359874749)
  ·
    refine ⟨9414526082551976384953031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25105402886805270359874749 9414526082551976384953031)
    ·
      refine ⟨14121789123827964577429547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9414526082551976384953031 14121789123827964577429547)
      ·
        refine ⟨21182683685741946866144321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14121789123827964577429547 21182683685741946866144321)
        ·
          refine ⟨15887012764306460149608241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21182683685741946866144321 15887012764306460149608241)
          ·
            refine ⟨11915259573229845112206181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15887012764306460149608241 11915259573229845112206181)
            ·
              refine ⟨2234111169980595958538659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11915259573229845112206181 2234111169980595958538659)
              ·
                refine ⟨3351166754970893937807989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234111169980595958538659 3351166754970893937807989)
                ·
                  refine ⟨314171883278521306669499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3351166754970893937807989 314171883278521306669499)
                  ·
                    rfl

theorem cell22_2753314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_2753314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753314 prefixEnd_2753314 := by exact prefixLift 2753314
  have htrace : WordTrace (prefixWord ++ tailWord_2753314) baseStart_2753314 baseEnd_2753314 := by
    simpa [prefixWord, tailWord_2753314, baseEnd_2753314] using wordTrace_append hprefix tailTrace_2753314
  have hstable : (prefixWord ++ tailWord_2753314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753314).length < 2 ^ (prefixWord ++ tailWord_2753314).sum := by decide
  have hdescent : baseEnd_2753314 < baseStart_2753314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753400 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 1, 8]
def baseStart_2753400 : Nat := 118140960795 + 2753400 * 2 ^ 59
def prefixEnd_2753400 : Nat := 4983230072969 + 3 ^ 40 * 2753400 * 2
def baseEnd_2753400 : Nat := 942545089393088362358233

theorem tailTrace_2753400 : CollatzResearch.WordTrace tailWord_2753400 prefixEnd_2753400 942545089393088362358233 := by
  unfold tailWord_2753400
  simp only [CollatzResearch.WordTrace]
  refine ⟨50212374112454759063564827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66949832149939678751419769 50212374112454759063564827)
  ·
    refine ⟨75318561168682138595347241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50212374112454759063564827 75318561168682138595347241)
    ·
      refine ⟨56488920876511603946510431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75318561168682138595347241 56488920876511603946510431)
      ·
        refine ⟨84733381314767405919765647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56488920876511603946510431 84733381314767405919765647)
        ·
          refine ⟨127100071972151108879648471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84733381314767405919765647 127100071972151108879648471)
          ·
            refine ⟨190650107958226663319472707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127100071972151108879648471 190650107958226663319472707)
            ·
              refine ⟨285975161937339994979209061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190650107958226663319472707 285975161937339994979209061)
              ·
                refine ⟨53620342863251249058601699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 285975161937339994979209061 53620342863251249058601699)
                ·
                  refine ⟨80430514294876873587902549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53620342863251249058601699 80430514294876873587902549)
                  ·
                    refine ⟨942545089393088362358233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80430514294876873587902549 942545089393088362358233)
                    ·
                      rfl

theorem cell22_2753400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_2753400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753400 prefixEnd_2753400 := by exact prefixLift 2753400
  have htrace : WordTrace (prefixWord ++ tailWord_2753400) baseStart_2753400 baseEnd_2753400 := by
    simpa [prefixWord, tailWord_2753400, baseEnd_2753400] using wordTrace_append hprefix tailTrace_2753400
  have hstable : (prefixWord ++ tailWord_2753400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753400).length < 2 ^ (prefixWord ++ tailWord_2753400).sum := by decide
  have hdescent : baseEnd_2753400 < baseStart_2753400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753402 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 7, 3]
def baseStart_2753402 : Nat := 118140960795 + 2753402 * 2 ^ 59
def prefixEnd_2753402 : Nat := 4983230072969 + 3 ^ 40 * 2753402 * 2
def baseEnd_2753402 : Nat := 942545774033961023808227

theorem tailTrace_2753402 : CollatzResearch.WordTrace tailWord_2753402 prefixEnd_2753402 942545774033961023808227 := by
  unfold tailWord_2753402
  simp only [CollatzResearch.WordTrace]
  refine ⟨25106205292725568117175615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66949880780601514979134973 25106205292725568117175615)
  ·
    refine ⟨37659307939088352175763423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25106205292725568117175615 37659307939088352175763423)
    ·
      refine ⟨56488961908632528263645135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37659307939088352175763423 56488961908632528263645135)
      ·
        refine ⟨84733442862948792395467703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56488961908632528263645135 84733442862948792395467703)
        ·
          refine ⟨127100164294423188593201555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84733442862948792395467703 127100164294423188593201555)
          ·
            refine ⟨190650246441634782889802333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127100164294423188593201555 190650246441634782889802333)
            ·
              refine ⟨71493842415613043583675875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190650246441634782889802333 71493842415613043583675875)
              ·
                refine ⟨107240763623419565375513813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71493842415613043583675875 107240763623419565375513813)
                ·
                  refine ⟨2513455397423896063488605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 107240763623419565375513813 2513455397423896063488605)
                  ·
                    refine ⟨942545774033961023808227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2513455397423896063488605 942545774033961023808227)
                    ·
                      rfl

theorem cell22_2753402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_2753402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753402 prefixEnd_2753402 := by exact prefixLift 2753402
  have htrace : WordTrace (prefixWord ++ tailWord_2753402) baseStart_2753402 baseEnd_2753402 := by
    simpa [prefixWord, tailWord_2753402, baseEnd_2753402] using wordTrace_append hprefix tailTrace_2753402
  have hstable : (prefixWord ++ tailWord_2753402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753402).length < 2 ^ (prefixWord ++ tailWord_2753402).sum := by decide
  have hdescent : baseEnd_2753402 < baseStart_2753402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753496 : List Nat := [2, 1, 2, 2, 2, 5, 1, 2, 1, 4]
def baseStart_2753496 : Nat := 118140960795 + 2753496 * 2 ^ 59
def prefixEnd_2753496 : Nat := 4983230072969 + 3 ^ 40 * 2753496 * 2
def baseEnd_2753496 : Nat := 942577952154976111957939

theorem tailTrace_2753496 : CollatzResearch.WordTrace tailWord_2753496 prefixEnd_2753496 942577952154976111957939 := by
  unfold tailWord_2753496
  simp only [CollatzResearch.WordTrace]
  refine ⟨50214124816280863261312171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66952166421707817681749561 50214124816280863261312171)
  ·
    refine ⟨75321187224421294891968257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50214124816280863261312171 75321187224421294891968257)
    ·
      refine ⟨56490890418315971168976193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75321187224421294891968257 56490890418315971168976193)
      ·
        refine ⟨42368167813736978376732145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56490890418315971168976193 42368167813736978376732145)
        ·
          refine ⟨31776125860302733782549109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42368167813736978376732145 31776125860302733782549109)
          ·
            refine ⟨2979011799403381292113979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31776125860302733782549109 2979011799403381292113979)
            ·
              refine ⟨4468517699105071938170969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2979011799403381292113979 4468517699105071938170969)
              ·
                refine ⟨3351388274328803953628227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4468517699105071938170969 3351388274328803953628227)
                ·
                  refine ⟨5027082411493205930442341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3351388274328803953628227 5027082411493205930442341)
                  ·
                    refine ⟨942577952154976111957939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5027082411493205930442341 942577952154976111957939)
                    ·
                      rfl

theorem cell22_2753496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_2753496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753496 prefixEnd_2753496 := by exact prefixLift 2753496
  have htrace : WordTrace (prefixWord ++ tailWord_2753496) baseStart_2753496 baseEnd_2753496 := by
    simpa [prefixWord, tailWord_2753496, baseEnd_2753496] using wordTrace_append hprefix tailTrace_2753496
  have hstable : (prefixWord ++ tailWord_2753496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753496).length < 2 ^ (prefixWord ++ tailWord_2753496).sum := by decide
  have hdescent : baseEnd_2753496 < baseStart_2753496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753588 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_2753588 : Nat := 118140960795 + 2753588 * 2 ^ 59
def prefixEnd_2753588 : Nat := 4983230072969 + 3 ^ 40 * 2753588 * 2
def baseEnd_2753588 : Nat := 942609445635118538657657

theorem tailTrace_2753588 : CollatzResearch.WordTrace tailWord_2753588 prefixEnd_2753588 942609445635118538657657 := by
  unfold tailWord_2753588
  simp only [CollatzResearch.WordTrace]
  refine ⟨50215802574114213117486709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66954403432152284156648945 50215802574114213117486709)
  ·
    refine ⟨4707731491323207479764379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50215802574114213117486709 4707731491323207479764379)
    ·
      refine ⟨7061597236984811219646569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4707731491323207479764379 7061597236984811219646569)
      ·
        refine ⟨5296197927738608414734927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7061597236984811219646569 5296197927738608414734927)
        ·
          refine ⟨7944296891607912622102391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5296197927738608414734927 7944296891607912622102391)
          ·
            refine ⟨11916445337411868933153587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7944296891607912622102391 11916445337411868933153587)
            ·
              refine ⟨17874668006117803399730381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11916445337411868933153587 17874668006117803399730381)
              ·
                refine ⟨6703000502294176274898893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17874668006117803399730381 6703000502294176274898893)
                ·
                  refine ⟨2513625188360316103087085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6703000502294176274898893 2513625188360316103087085)
                  ·
                    refine ⟨942609445635118538657657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2513625188360316103087085 942609445635118538657657)
                    ·
                      rfl

theorem cell22_2753588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_2753588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753588 prefixEnd_2753588 := by exact prefixLift 2753588
  have htrace : WordTrace (prefixWord ++ tailWord_2753588) baseStart_2753588 baseEnd_2753588 := by
    simpa [prefixWord, tailWord_2753588, baseEnd_2753588] using wordTrace_append hprefix tailTrace_2753588
  have hstable : (prefixWord ++ tailWord_2753588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753588).length < 2 ^ (prefixWord ++ tailWord_2753588).sum := by decide
  have hdescent : baseEnd_2753588 < baseStart_2753588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753646 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_2753646 : Nat := 118140960795 + 2753646 * 2 ^ 59
def prefixEnd_2753646 : Nat := 4983230072969 + 3 ^ 40 * 2753646 * 2
def baseEnd_2753646 : Nat := 314209766740141906902493

theorem tailTrace_2753646 : CollatzResearch.WordTrace tailWord_2753646 prefixEnd_2753646 314209766740141906902493 := by
  unfold tailWord_2753646
  simp only [CollatzResearch.WordTrace]
  refine ⟨12554215072752287767573099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66955813721345534760389861 12554215072752287767573099)
  ·
    refine ⟨18831322609128431651359649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12554215072752287767573099 18831322609128431651359649)
    ·
      refine ⟨14123491956846323738519737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18831322609128431651359649 14123491956846323738519737)
      ·
        refine ⟨10592618967634742803889803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14123491956846323738519737 10592618967634742803889803)
        ·
          refine ⟨15888928451452114205834705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10592618967634742803889803 15888928451452114205834705)
          ·
            refine ⟨11916696338589085654376029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15888928451452114205834705 11916696338589085654376029)
            ·
              refine ⟨4468761126970907120391011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11916696338589085654376029 4468761126970907120391011)
              ·
                refine ⟨6703141690456360680586517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4468761126970907120391011 6703141690456360680586517)
                ·
                  refine ⟨314209766740141906902493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6703141690456360680586517 314209766740141906902493)
                  ·
                    rfl

theorem cell22_2753646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_2753646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753646 prefixEnd_2753646 := by exact prefixLift 2753646
  have htrace : WordTrace (prefixWord ++ tailWord_2753646) baseStart_2753646 baseEnd_2753646 := by
    simpa [prefixWord, tailWord_2753646, baseEnd_2753646] using wordTrace_append hprefix tailTrace_2753646
  have hstable : (prefixWord ++ tailWord_2753646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753646).length < 2 ^ (prefixWord ++ tailWord_2753646).sum := by decide
  have hdescent : baseEnd_2753646 < baseStart_2753646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753674 : List Nat := [3, 1, 2, 3, 1, 1, 1, 10]
def baseStart_2753674 : Nat := 118140960795 + 2753674 * 2 ^ 59
def prefixEnd_2753674 : Nat := 4983230072969 + 3 ^ 40 * 2753674 * 2
def baseEnd_2753674 : Nat := 104737653910293664556377

theorem tailTrace_2753674 : CollatzResearch.WordTrace tailWord_2753674 prefixEnd_2753674 104737653910293664556377 := by
  unfold tailWord_2753674
  simp only [CollatzResearch.WordTrace]
  refine ⟨25108685456479215730651019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66956494550611241948402717 25108685456479215730651019)
  ·
    refine ⟨37663028184718823595976529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25108685456479215730651019 37663028184718823595976529)
    ·
      refine ⟨28247271138539117696982397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37663028184718823595976529 28247271138539117696982397)
      ·
        refine ⟨10592726676952169136368399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28247271138539117696982397 10592726676952169136368399)
        ·
          refine ⟨15889090015428253704552599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10592726676952169136368399 15889090015428253704552599)
          ·
            refine ⟨23833635023142380556828899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15889090015428253704552599 23833635023142380556828899)
            ·
              refine ⟨35750452534713570835243349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23833635023142380556828899 35750452534713570835243349)
              ·
                refine ⟨104737653910293664556377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35750452534713570835243349 104737653910293664556377)
                ·
                  rfl

theorem cell22_2753674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 10].length) (baseStart_2753674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753674 prefixEnd_2753674 := by exact prefixLift 2753674
  have htrace : WordTrace (prefixWord ++ tailWord_2753674) baseStart_2753674 baseEnd_2753674 := by
    simpa [prefixWord, tailWord_2753674, baseEnd_2753674] using wordTrace_append hprefix tailTrace_2753674
  have hstable : (prefixWord ++ tailWord_2753674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753674).length < 2 ^ (prefixWord ++ tailWord_2753674).sum := by decide
  have hdescent : baseEnd_2753674 < baseStart_2753674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753695 : List Nat := [1, 1, 2, 6, 2, 1, 2, 2, 2, 3]
def baseStart_2753695 : Nat := 118140960795 + 2753695 * 2 ^ 59
def prefixEnd_2753695 : Nat := 4983230072969 + 3 ^ 40 * 2753695 * 2
def baseEnd_2753695 : Nat := 942646073921805926232329

theorem tailTrace_2753695 : CollatzResearch.WordTrace tailWord_2753695 prefixEnd_2753695 942646073921805926232329 := by
  unfold tailWord_2753695
  simp only [CollatzResearch.WordTrace]
  refine ⟨100435507758840783509118539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66957005172560522339412359 100435507758840783509118539)
  ·
    refine ⟨150653261638261175263677809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100435507758840783509118539 150653261638261175263677809)
    ·
      refine ⟨112989946228695881447758357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150653261638261175263677809 112989946228695881447758357)
      ·
        refine ⟨5296403729470119442863673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 112989946228695881447758357 5296403729470119442863673)
        ·
          refine ⟨3972302797102589582147755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5296403729470119442863673 3972302797102589582147755)
          ·
            refine ⟨5958454195653884373221633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3972302797102589582147755 5958454195653884373221633)
            ·
              refine ⟨4468840646740413279916225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5958454195653884373221633 4468840646740413279916225)
              ·
                refine ⟨3351630485055309959937169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4468840646740413279916225 3351630485055309959937169)
                ·
                  refine ⟨2513722863791482469952877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3351630485055309959937169 2513722863791482469952877)
                  ·
                    refine ⟨942646073921805926232329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2513722863791482469952877 942646073921805926232329)
                    ·
                      rfl

theorem cell22_2753695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 3].length) (baseStart_2753695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753695 prefixEnd_2753695 := by exact prefixLift 2753695
  have htrace : WordTrace (prefixWord ++ tailWord_2753695) baseStart_2753695 baseEnd_2753695 := by
    simpa [prefixWord, tailWord_2753695, baseEnd_2753695] using wordTrace_append hprefix tailTrace_2753695
  have hstable : (prefixWord ++ tailWord_2753695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753695).length < 2 ^ (prefixWord ++ tailWord_2753695).sum := by decide
  have hdescent : baseEnd_2753695 < baseStart_2753695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753813 : List Nat := [1, 3, 2, 1, 2, 1, 1, 6, 2, 3]
def baseStart_2753813 : Nat := 118140960795 + 2753813 * 2 ^ 59
def prefixEnd_2753813 : Nat := 4983230072969 + 3 ^ 40 * 2753813 * 2
def baseEnd_2753813 : Nat := 942686467733292951781967

theorem tailTrace_2753813 : CollatzResearch.WordTrace tailWord_2753813 prefixEnd_2753813 942686467733292951781967 := by
  unfold tailWord_2753813
  simp only [CollatzResearch.WordTrace]
  refine ⟨100439811572413289661914093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66959874381608859774609395 100439811572413289661914093)
  ·
    refine ⟨37664929339654983623217785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100439811572413289661914093 37664929339654983623217785)
    ·
      refine ⟨28248697004741237717413339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37664929339654983623217785 28248697004741237717413339)
      ·
        refine ⟨42373045507111856576120009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28248697004741237717413339 42373045507111856576120009)
        ·
          refine ⟨31779784130333892432090007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42373045507111856576120009 31779784130333892432090007)
          ·
            refine ⟨47669676195500838648135011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31779784130333892432090007 47669676195500838648135011)
            ·
              refine ⟨71504514293251257972202517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47669676195500838648135011 71504514293251257972202517)
              ·
                refine ⟨3351774107496152717446993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71504514293251257972202517 3351774107496152717446993)
                ·
                  refine ⟨2513830580622114538085245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3351774107496152717446993 2513830580622114538085245)
                  ·
                    refine ⟨942686467733292951781967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2513830580622114538085245 942686467733292951781967)
                    ·
                      rfl

theorem cell22_2753813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_2753813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753813 prefixEnd_2753813 := by exact prefixLift 2753813
  have htrace : WordTrace (prefixWord ++ tailWord_2753813) baseStart_2753813 baseEnd_2753813 := by
    simpa [prefixWord, tailWord_2753813, baseEnd_2753813] using wordTrace_append hprefix tailTrace_2753813
  have hstable : (prefixWord ++ tailWord_2753813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753813).length < 2 ^ (prefixWord ++ tailWord_2753813).sum := by decide
  have hdescent : baseEnd_2753813 < baseStart_2753813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753815 : List Nat := [1, 1, 3, 4, 1, 1, 5, 2, 4]
def baseStart_2753815 : Nat := 118140960795 + 2753815 * 2 ^ 59
def prefixEnd_2753815 : Nat := 4983230072969 + 3 ^ 40 * 2753815 * 2
def baseEnd_2753815 : Nat := 314229050791388537743987

theorem tailTrace_2753815 : CollatzResearch.WordTrace tailWord_2753815 prefixEnd_2753815 314229050791388537743987 := by
  unfold tailWord_2753815
  simp only [CollatzResearch.WordTrace]
  refine ⟨100439884518406044003486899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66959923012270696002324599 100439884518406044003486899)
  ·
    refine ⟨150659826777609066005230349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100439884518406044003486899 150659826777609066005230349)
    ·
      refine ⟨56497435041603399751961381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150659826777609066005230349 56497435041603399751961381)
      ·
        refine ⟨10593269070300637453492759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56497435041603399751961381 10593269070300637453492759)
        ·
          refine ⟨15889903605450956180239139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10593269070300637453492759 15889903605450956180239139)
          ·
            refine ⟨23834855408176434270358709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15889903605450956180239139 23834855408176434270358709)
            ·
              refine ⟨2234517694516540712846129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23834855408176434270358709 2234517694516540712846129)
              ·
                refine ⟨1675888270887405534634597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2234517694516540712846129 1675888270887405534634597)
                ·
                  refine ⟨314229050791388537743987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1675888270887405534634597 314229050791388537743987)
                  ·
                    rfl

theorem cell22_2753815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 4].length) (baseStart_2753815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753815 prefixEnd_2753815 := by exact prefixLift 2753815
  have htrace : WordTrace (prefixWord ++ tailWord_2753815) baseStart_2753815 baseEnd_2753815 := by
    simpa [prefixWord, tailWord_2753815, baseEnd_2753815] using wordTrace_append hprefix tailTrace_2753815
  have hstable : (prefixWord ++ tailWord_2753815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753815).length < 2 ^ (prefixWord ++ tailWord_2753815).sum := by decide
  have hdescent : baseEnd_2753815 < baseStart_2753815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753875 : List Nat := [1, 1, 1, 2, 1, 1, 7, 4, 1, 3]
def baseStart_2753875 : Nat := 118140960795 + 2753875 * 2 ^ 59
def prefixEnd_2753875 : Nat := 4983230072969 + 3 ^ 40 * 2753875 * 2
def baseEnd_2753875 : Nat := 942707691600345456731777

theorem tailTrace_2753875 : CollatzResearch.WordTrace tailWord_2753875 prefixEnd_2753875 942707691600345456731777 := by
  unfold tailWord_2753875
  simp only [CollatzResearch.WordTrace]
  refine ⟨100442072898188674250671079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66961381932125782833780719 100442072898188674250671079)
  ·
    refine ⟨150663109347283011376006619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100442072898188674250671079 150663109347283011376006619)
    ·
      refine ⟨225994664020924517064009929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150663109347283011376006619 225994664020924517064009929)
      ·
        refine ⟨169495998015693387798007447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225994664020924517064009929 169495998015693387798007447)
        ·
          refine ⟨254243997023540081697011171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169495998015693387798007447 254243997023540081697011171)
          ·
            refine ⟨381365995535310122545516757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254243997023540081697011171 381365995535310122545516757)
            ·
              refine ⟨8938265520358830997160549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 381365995535310122545516757 8938265520358830997160549)
              ·
                refine ⟨1675924785067280811967603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8938265520358830997160549 1675924785067280811967603)
                ·
                  refine ⟨2513887177600921217951405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675924785067280811967603 2513887177600921217951405)
                  ·
                    refine ⟨942707691600345456731777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2513887177600921217951405 942707691600345456731777)
                    ·
                      rfl

theorem cell22_2753875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 1, 3].length) (baseStart_2753875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753875 prefixEnd_2753875 := by exact prefixLift 2753875
  have htrace : WordTrace (prefixWord ++ tailWord_2753875) baseStart_2753875 baseEnd_2753875 := by
    simpa [prefixWord, tailWord_2753875, baseEnd_2753875] using wordTrace_append hprefix tailTrace_2753875
  have hstable : (prefixWord ++ tailWord_2753875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753875).length < 2 ^ (prefixWord ++ tailWord_2753875).sum := by decide
  have hdescent : baseEnd_2753875 < baseStart_2753875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753888 : List Nat := [2, 1, 1, 3, 4, 1, 2, 3, 5]
def baseStart_2753888 : Nat := 118140960795 + 2753888 * 2 ^ 59
def prefixEnd_2753888 : Nat := 4983230072969 + 3 ^ 40 * 2753888 * 2
def baseEnd_2753888 : Nat := 314237380588672585385579

theorem tailTrace_2753888 : CollatzResearch.WordTrace tailWord_2753888 prefixEnd_2753888 314237380588672585385579 := by
  unfold tailWord_2753888
  simp only [CollatzResearch.WordTrace]
  refine ⟨50221273523570788735447159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66961698031427718313929545 50221273523570788735447159)
  ·
    refine ⟨75331910285356183103170739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50221273523570788735447159 75331910285356183103170739)
    ·
      refine ⟨112997865428034274654756109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75331910285356183103170739 112997865428034274654756109)
      ·
        refine ⟨42374199535512852995533541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112997865428034274654756109 42374199535512852995533541)
        ·
          refine ⟨7945162412908659936662539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42374199535512852995533541 7945162412908659936662539)
          ·
            refine ⟨11917743619362989904993809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7945162412908659936662539 11917743619362989904993809)
            ·
              refine ⟨8938307714522242428745357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11917743619362989904993809 8938307714522242428745357)
              ·
                refine ⟨3351865392945840910779509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8938307714522242428745357 3351865392945840910779509)
                ·
                  refine ⟨314237380588672585385579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3351865392945840910779509 314237380588672585385579)
                  ·
                    rfl

theorem cell22_2753888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 5].length) (baseStart_2753888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753888 prefixEnd_2753888 := by exact prefixLift 2753888
  have htrace : WordTrace (prefixWord ++ tailWord_2753888) baseStart_2753888 baseEnd_2753888 := by
    simpa [prefixWord, tailWord_2753888, baseEnd_2753888] using wordTrace_append hprefix tailTrace_2753888
  have hstable : (prefixWord ++ tailWord_2753888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753888).length < 2 ^ (prefixWord ++ tailWord_2753888).sum := by decide
  have hdescent : baseEnd_2753888 < baseStart_2753888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753909 : List Nat := [1, 3, 4, 1, 3, 1, 2, 3, 1, 3]
def baseStart_2753909 : Nat := 118140960795 + 2753909 * 2 ^ 59
def prefixEnd_2753909 : Nat := 4983230072969 + 3 ^ 40 * 2753909 * 2
def baseEnd_2753909 : Nat := 942719330495180701381673

theorem tailTrace_2753909 : CollatzResearch.WordTrace tailWord_2753909 prefixEnd_2753909 942719330495180701381673 := by
  unfold tailWord_2753909
  simp only [CollatzResearch.WordTrace]
  refine ⟨100443312980065498057408781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66962208653376998704939187 100443312980065498057408781)
  ·
    refine ⟨37666242367524561771528293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100443312980065498057408781 37666242367524561771528293)
    ·
      refine ⟨7062420443910855332161555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37666242367524561771528293 7062420443910855332161555)
      ·
        refine ⟨10593630665866282998242333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7062420443910855332161555 10593630665866282998242333)
        ·
          refine ⟨3972611499699856124340875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10593630665866282998242333 3972611499699856124340875)
          ·
            refine ⟨5958917249549784186511313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3972611499699856124340875 5958917249549784186511313)
            ·
              refine ⟨4469187937162338139883485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5958917249549784186511313 4469187937162338139883485)
              ·
                refine ⟨1675945476435876802456307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4469187937162338139883485 1675945476435876802456307)
                ·
                  refine ⟨2513918214653815203684461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675945476435876802456307 2513918214653815203684461)
                  ·
                    refine ⟨942719330495180701381673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2513918214653815203684461 942719330495180701381673)
                    ·
                      rfl

theorem cell22_2753909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_2753909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753909 prefixEnd_2753909 := by exact prefixLift 2753909
  have htrace : WordTrace (prefixWord ++ tailWord_2753909) baseStart_2753909 baseEnd_2753909 := by
    simpa [prefixWord, tailWord_2753909, baseEnd_2753909] using wordTrace_append hprefix tailTrace_2753909
  have hstable : (prefixWord ++ tailWord_2753909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753909).length < 2 ^ (prefixWord ++ tailWord_2753909).sum := by decide
  have hdescent : baseEnd_2753909 < baseStart_2753909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753916 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 8]
def baseStart_2753916 : Nat := 118140960795 + 2753916 * 2 ^ 59
def prefixEnd_2753916 : Nat := 4983230072969 + 3 ^ 40 * 2753916 * 2
def baseEnd_2753916 : Nat := 314240575579411672152217

theorem tailTrace_2753916 : CollatzResearch.WordTrace tailWord_2753916 prefixEnd_2753916 314240575579411672152217 := by
  unfold tailWord_2753916
  simp only [CollatzResearch.WordTrace]
  refine ⟨50221784145520069126456801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66962378860693425501942401 50221784145520069126456801)
  ·
    refine ⟨37666338109140051844842601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50221784145520069126456801 37666338109140051844842601)
    ·
      refine ⟨28249753581855038883631951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37666338109140051844842601 28249753581855038883631951)
      ·
        refine ⟨42374630372782558325447927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28249753581855038883631951 42374630372782558325447927)
        ·
          refine ⟨63561945559173837488171891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42374630372782558325447927 63561945559173837488171891)
          ·
            refine ⟨95342918338760756232257837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63561945559173837488171891 95342918338760756232257837)
            ·
              refine ⟨35753594377035283587096689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95342918338760756232257837 35753594377035283587096689)
              ·
                refine ⟨26815195782776462690322517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35753594377035283587096689 26815195782776462690322517)
                ·
                  refine ⟨314240575579411672152217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26815195782776462690322517 314240575579411672152217)
                  ·
                    rfl

theorem cell22_2753916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_2753916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753916 prefixEnd_2753916 := by exact prefixLift 2753916
  have htrace : WordTrace (prefixWord ++ tailWord_2753916) baseStart_2753916 baseEnd_2753916 := by
    simpa [prefixWord, tailWord_2753916, baseEnd_2753916] using wordTrace_append hprefix tailTrace_2753916
  have hstable : (prefixWord ++ tailWord_2753916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753916).length < 2 ^ (prefixWord ++ tailWord_2753916).sum := by decide
  have hdescent : baseEnd_2753916 < baseStart_2753916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2753922 : List Nat := [3, 4, 2, 1, 1, 1, 3, 2, 5]
def baseStart_2753922 : Nat := 118140960795 + 2753922 * 2 ^ 59
def prefixEnd_2753922 : Nat := 4983230072969 + 3 ^ 40 * 2753922 * 2
def baseEnd_2753922 : Nat := 314241260220284333602211

theorem tailTrace_2753922 : CollatzResearch.WordTrace tailWord_2753922 prefixEnd_2753922 314241260220284333602211 := by
  unfold tailWord_2753922
  simp only [CollatzResearch.WordTrace]
  refine ⟨25110946782254600319408005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66962524752678934185088013 25110946782254600319408005)
  ·
    refine ⟨4708302521672737559889001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25110946782254600319408005 4708302521672737559889001)
    ·
      refine ⟨3531226891254553169916751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4708302521672737559889001 3531226891254553169916751)
      ·
        refine ⟨5296840336881829754875127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531226891254553169916751 5296840336881829754875127)
        ·
          refine ⟨7945260505322744632312691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5296840336881829754875127 7945260505322744632312691)
          ·
            refine ⟨11917890757984116948469037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7945260505322744632312691 11917890757984116948469037)
            ·
              refine ⟨4469209034244043855675889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11917890757984116948469037 4469209034244043855675889)
              ·
                refine ⟨3351906775683032891756917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4469209034244043855675889 3351906775683032891756917)
                ·
                  refine ⟨314241260220284333602211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3351906775683032891756917 314241260220284333602211)
                  ·
                    rfl

theorem cell22_2753922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_2753922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2753922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2753922 prefixEnd_2753922 := by exact prefixLift 2753922
  have htrace : WordTrace (prefixWord ++ tailWord_2753922) baseStart_2753922 baseEnd_2753922 := by
    simpa [prefixWord, tailWord_2753922, baseEnd_2753922] using wordTrace_append hprefix tailTrace_2753922
  have hstable : (prefixWord ++ tailWord_2753922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2753922).length < 2 ^ (prefixWord ++ tailWord_2753922).sum := by decide
  have hdescent : baseEnd_2753922 < baseStart_2753922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2753922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754040 : List Nat := [2, 1, 2, 1, 1, 6, 2, 2, 5]
def baseStart_2754040 : Nat := 118140960795 + 2754040 * 2 ^ 59
def prefixEnd_2754040 : Nat := 4983230072969 + 3 ^ 40 * 2754040 * 2
def baseEnd_2754040 : Nat := 314254724824113342118757

theorem tailTrace_2754040 : CollatzResearch.WordTrace tailWord_2754040 prefixEnd_2754040 314254724824113342118757 := by
  unfold tailWord_2754040
  simp only [CollatzResearch.WordTrace]
  refine ⟨50224045471295453715213787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66965393961727271620285049 50224045471295453715213787)
  ·
    refine ⟨75336068206943180572820681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50224045471295453715213787 75336068206943180572820681)
    ·
      refine ⟨56502051155207385429615511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75336068206943180572820681 56502051155207385429615511)
      ·
        refine ⟨84753076732811078144423267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56502051155207385429615511 84753076732811078144423267)
        ·
          refine ⟨127129615099216617216634901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84753076732811078144423267 127129615099216617216634901)
          ·
            refine ⟨5959200707775778932029761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 127129615099216617216634901 5959200707775778932029761)
            ·
              refine ⟨4469400530831834199022321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5959200707775778932029761 4469400530831834199022321)
              ·
                refine ⟨3352050398123875649266741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4469400530831834199022321 3352050398123875649266741)
                ·
                  refine ⟨314254724824113342118757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3352050398123875649266741 314254724824113342118757)
                  ·
                    rfl

theorem cell22_2754040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 5].length) (baseStart_2754040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754040 prefixEnd_2754040 := by exact prefixLift 2754040
  have htrace : WordTrace (prefixWord ++ tailWord_2754040) baseStart_2754040 baseEnd_2754040 := by
    simpa [prefixWord, tailWord_2754040, baseEnd_2754040] using wordTrace_append hprefix tailTrace_2754040
  have hstable : (prefixWord ++ tailWord_2754040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754040).length < 2 ^ (prefixWord ++ tailWord_2754040).sum := by decide
  have hdescent : baseEnd_2754040 < baseStart_2754040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754044 : List Nat := [2, 2, 2, 1, 2, 1, 6, 2, 1, 3]
def baseStart_2754044 : Nat := 118140960795 + 2754044 * 2 ^ 59
def prefixEnd_2754044 : Nat := 4983230072969 + 3 ^ 40 * 2754044 * 2
def baseEnd_2754044 : Nat := 942765543754085349256259

theorem tailTrace_2754044 : CollatzResearch.WordTrace tailWord_2754044 prefixEnd_2754044 942765543754085349256259 := by
  unfold tailWord_2754044
  simp only [CollatzResearch.WordTrace]
  refine ⟨50224118417288208056786593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66965491223050944075715457 50224118417288208056786593)
  ·
    refine ⟨37668088812966156042589945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50224118417288208056786593 37668088812966156042589945)
    ·
      refine ⟨28251066609724617031942459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37668088812966156042589945 28251066609724617031942459)
      ·
        refine ⟨42376599914586925547913689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28251066609724617031942459 42376599914586925547913689)
        ·
          refine ⟨31782449935940194160935267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42376599914586925547913689 31782449935940194160935267)
          ·
            refine ⟨47673674903910291241402901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31782449935940194160935267 47673674903910291241402901)
            ·
              refine ⟨2234703511120794901940761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47673674903910291241402901 2234703511120794901940761)
              ·
                refine ⟨1676027633340596176455571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2234703511120794901940761 1676027633340596176455571)
                ·
                  refine ⟨2514041450010894264683357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676027633340596176455571 2514041450010894264683357)
                  ·
                    refine ⟨942765543754085349256259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2514041450010894264683357 942765543754085349256259)
                    ·
                      rfl

theorem cell22_2754044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_2754044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754044 prefixEnd_2754044 := by exact prefixLift 2754044
  have htrace : WordTrace (prefixWord ++ tailWord_2754044) baseStart_2754044 baseEnd_2754044 := by
    simpa [prefixWord, tailWord_2754044, baseEnd_2754044] using wordTrace_append hprefix tailTrace_2754044
  have hstable : (prefixWord ++ tailWord_2754044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754044).length < 2 ^ (prefixWord ++ tailWord_2754044).sum := by decide
  have hdescent : baseEnd_2754044 < baseStart_2754044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754055 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 2, 5]
def baseStart_2754055 : Nat := 118140960795 + 2754055 * 2 ^ 59
def prefixEnd_2754055 : Nat := 4983230072969 + 3 ^ 40 * 2754055 * 2
def baseEnd_2754055 : Nat := 942769309278884987231225

theorem tailTrace_2754055 : CollatzResearch.WordTrace tailWord_2754055 prefixEnd_2754055 942769309278884987231225 := by
  unfold tailWord_2754055
  simp only [CollatzResearch.WordTrace]
  refine ⟨100448638037536564992223619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66965758691691043328149079 100448638037536564992223619)
  ·
    refine ⟨150672957056304847488335429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100448638037536564992223619 150672957056304847488335429)
    ·
      refine ⟨28251179448057158904062893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150672957056304847488335429 28251179448057158904062893)
      ·
        refine ⟨10594192293021434589023585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28251179448057158904062893 10594192293021434589023585)
        ·
          refine ⟨7945644219766075941767689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10594192293021434589023585 7945644219766075941767689)
          ·
            refine ⟨5959233164824556956325767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7945644219766075941767689 5959233164824556956325767)
            ·
              refine ⟨8938849747236835434488651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5959233164824556956325767 8938849747236835434488651)
              ·
                refine ⟨13408274620855253151732977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8938849747236835434488651 13408274620855253151732977)
                ·
                  refine ⟨10056205965641439863799733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13408274620855253151732977 10056205965641439863799733)
                  ·
                    refine ⟨942769309278884987231225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10056205965641439863799733 942769309278884987231225)
                    ·
                      rfl

theorem cell22_2754055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_2754055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754055 prefixEnd_2754055 := by exact prefixLift 2754055
  have htrace : WordTrace (prefixWord ++ tailWord_2754055) baseStart_2754055 baseEnd_2754055 := by
    simpa [prefixWord, tailWord_2754055, baseEnd_2754055] using wordTrace_append hprefix tailTrace_2754055
  have hstable : (prefixWord ++ tailWord_2754055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754055).length < 2 ^ (prefixWord ++ tailWord_2754055).sum := by decide
  have hdescent : baseEnd_2754055 < baseStart_2754055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754061 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2754061 : Nat := 118140960795 + 2754061 * 2 ^ 59
def prefixEnd_2754061 : Nat := 4983230072969 + 3 ^ 40 * 2754061 * 2
def baseEnd_2754061 : Nat := 942771363201502971581207

theorem tailTrace_2754061 : CollatzResearch.WordTrace tailWord_2754061 prefixEnd_2754061 942771363201502971581207 := by
  unfold tailWord_2754061
  simp only [CollatzResearch.WordTrace]
  refine ⟨100448856875514828016942037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66965904583676552011294691 100448856875514828016942037)
  ·
    refine ⟨2354270083019878781647079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 100448856875514828016942037 2354270083019878781647079)
    ·
      refine ⟨3531405124529818172470619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2354270083019878781647079 3531405124529818172470619)
      ·
        refine ⟨5297107686794727258705929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531405124529818172470619 5297107686794727258705929)
        ·
          refine ⟨3972830765096045444029447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5297107686794727258705929 3972830765096045444029447)
          ·
            refine ⟨5959246147644068166044171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3972830765096045444029447 5959246147644068166044171)
            ·
              refine ⟨8938869221466102249066257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5959246147644068166044171 8938869221466102249066257)
              ·
                refine ⟨6704151916099576686799693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8938869221466102249066257 6704151916099576686799693)
                ·
                  refine ⟨2514056968537341257549885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6704151916099576686799693 2514056968537341257549885)
                  ·
                    refine ⟨942771363201502971581207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2514056968537341257549885 942771363201502971581207)
                    ·
                      rfl

theorem cell22_2754061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2754061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754061 prefixEnd_2754061 := by exact prefixLift 2754061
  have htrace : WordTrace (prefixWord ++ tailWord_2754061) baseStart_2754061 baseEnd_2754061 := by
    simpa [prefixWord, tailWord_2754061, baseEnd_2754061] using wordTrace_append hprefix tailTrace_2754061
  have hstable : (prefixWord ++ tailWord_2754061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754061).length < 2 ^ (prefixWord ++ tailWord_2754061).sum := by decide
  have hdescent : baseEnd_2754061 < baseStart_2754061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754128 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 2, 7]
def baseStart_2754128 : Nat := 118140960795 + 2754128 * 2 ^ 59
def prefixEnd_2754128 : Nat := 4983230072969 + 3 ^ 40 * 2754128 * 2
def baseEnd_2754128 : Nat := 942794298670737130156001

theorem tailTrace_2754128 : CollatzResearch.WordTrace tailWord_2754128 prefixEnd_2754128 942794298670737130156001 := by
  unfold tailWord_2754128
  simp only [CollatzResearch.WordTrace]
  refine ⟨50225650283136049229815519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66967533710848065639754025 50225650283136049229815519)
  ·
    refine ⟨75338475424704073844723279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50225650283136049229815519 75338475424704073844723279)
    ·
      refine ⟨113007713137056110767084919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75338475424704073844723279 113007713137056110767084919)
      ·
        refine ⟨169511569705584166150627379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113007713137056110767084919 169511569705584166150627379)
        ·
          refine ⟨254267354558376249225941069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169511569705584166150627379 254267354558376249225941069)
          ·
            refine ⟨95350257959391093459727901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254267354558376249225941069 95350257959391093459727901)
            ·
              refine ⟨35756346734771660047397963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95350257959391093459727901 35756346734771660047397963)
              ·
                refine ⟨53634520102157490071096945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35756346734771660047397963 53634520102157490071096945)
                ·
                  refine ⟨40225890076618117553322709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53634520102157490071096945 40225890076618117553322709)
                  ·
                    refine ⟨942794298670737130156001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40225890076618117553322709 942794298670737130156001)
                    ·
                      rfl

theorem cell22_2754128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_2754128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754128 prefixEnd_2754128 := by exact prefixLift 2754128
  have htrace : WordTrace (prefixWord ++ tailWord_2754128) baseStart_2754128 baseEnd_2754128 := by
    simpa [prefixWord, tailWord_2754128, baseEnd_2754128] using wordTrace_append hprefix tailTrace_2754128
  have hstable : (prefixWord ++ tailWord_2754128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754128).length < 2 ^ (prefixWord ++ tailWord_2754128).sum := by decide
  have hdescent : baseEnd_2754128 < baseStart_2754128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754130 : List Nat := [3, 2, 2, 1, 2, 3, 1, 8]
def baseStart_2754130 : Nat := 118140960795 + 2754130 * 2 ^ 59
def prefixEnd_2754130 : Nat := 4983230072969 + 3 ^ 40 * 2754130 * 2
def baseEnd_2754130 : Nat := 104754998145734421289555

theorem tailTrace_2754130 : CollatzResearch.WordTrace tailWord_2754130 prefixEnd_2754130 104754998145734421289555 := by
  unfold tailWord_2754130
  simp only [CollatzResearch.WordTrace]
  refine ⟨25112843378066213200300961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66967582341509901867469229 25112843378066213200300961)
  ·
    refine ⟨18834632533549659900225721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25112843378066213200300961 18834632533549659900225721)
    ·
      refine ⟨14125974400162244925169291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18834632533549659900225721 14125974400162244925169291)
      ·
        refine ⟨21188961600243367387753937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14125974400162244925169291 21188961600243367387753937)
        ·
          refine ⟨15891721200182525540815453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21188961600243367387753937 15891721200182525540815453)
          ·
            refine ⟨5959395450068447077805795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15891721200182525540815453 5959395450068447077805795)
            ·
              refine ⟨8939093175102670616708693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5959395450068447077805795 8939093175102670616708693)
              ·
                refine ⟨104754998145734421289555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8939093175102670616708693 104754998145734421289555)
                ·
                  rfl

theorem cell22_2754130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 8].length) (baseStart_2754130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754130 prefixEnd_2754130 := by exact prefixLift 2754130
  have htrace : WordTrace (prefixWord ++ tailWord_2754130) baseStart_2754130 baseEnd_2754130 := by
    simpa [prefixWord, tailWord_2754130, baseEnd_2754130] using wordTrace_append hprefix tailTrace_2754130
  have hstable : (prefixWord ++ tailWord_2754130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754130).length < 2 ^ (prefixWord ++ tailWord_2754130).sum := by decide
  have hdescent : baseEnd_2754130 < baseStart_2754130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754143 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 3, 8]
def baseStart_2754143 : Nat := 118140960795 + 2754143 * 2 ^ 59
def prefixEnd_2754143 : Nat := 4983230072969 + 3 ^ 40 * 2754143 * 2
def baseEnd_2754143 : Nat := 942799433477282091030955

theorem tailTrace_2754143 : CollatzResearch.WordTrace tailWord_2754143 prefixEnd_2754143 942799433477282091030955 := by
  unfold tailWord_2754143
  simp only [CollatzResearch.WordTrace]
  refine ⟨100451847661217756021427083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66967898440811837347618055 100451847661217756021427083)
  ·
    refine ⟨150677771491826634032140625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100451847661217756021427083 150677771491826634032140625)
    ·
      refine ⟨113008328618869975524105469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150677771491826634032140625 113008328618869975524105469)
      ·
        refine ⟨42378123232076240821539551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113008328618869975524105469 42378123232076240821539551)
        ·
          refine ⟨63567184848114361232309327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42378123232076240821539551 63567184848114361232309327)
          ·
            refine ⟨95350777272171541848463991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63567184848114361232309327 95350777272171541848463991)
            ·
              refine ⟨143026165908257312772695987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95350777272171541848463991 143026165908257312772695987)
              ·
                refine ⟨214539248862385969159043981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143026165908257312772695987 214539248862385969159043981)
                ·
                  refine ⟨80452218323394738434641493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214539248862385969159043981 80452218323394738434641493)
                  ·
                    refine ⟨942799433477282091030955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80452218323394738434641493 942799433477282091030955)
                    ·
                      rfl

theorem cell22_2754143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_2754143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754143 prefixEnd_2754143 := by exact prefixLift 2754143
  have htrace : WordTrace (prefixWord ++ tailWord_2754143) baseStart_2754143 baseEnd_2754143 := by
    simpa [prefixWord, tailWord_2754143, baseEnd_2754143] using wordTrace_append hprefix tailTrace_2754143
  have hstable : (prefixWord ++ tailWord_2754143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754143).length < 2 ^ (prefixWord ++ tailWord_2754143).sum := by decide
  have hdescent : baseEnd_2754143 < baseStart_2754143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754254 : List Nat := [4, 1, 1, 1, 3, 1, 4, 3, 4]
def baseStart_2754254 : Nat := 118140960795 + 2754254 * 2 ^ 59
def prefixEnd_2754254 : Nat := 4983230072969 + 3 ^ 40 * 2754254 * 2
def baseEnd_2754254 : Nat := 314279143681904933835205

theorem tailTrace_2754254 : CollatzResearch.WordTrace tailWord_2754254 prefixEnd_2754254 314279143681904933835205 := by
  unfold tailWord_2754254
  simp only [CollatzResearch.WordTrace]
  refine ⟨12556987020476952747339727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66970597442543747985811877 12556987020476952747339727)
  ·
    refine ⟨18835480530715429121009591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12556987020476952747339727 18835480530715429121009591)
    ·
      refine ⟨28253220796073143681514387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18835480530715429121009591 28253220796073143681514387)
      ·
        refine ⟨42379831194109715522271581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28253220796073143681514387 42379831194109715522271581)
        ·
          refine ⟨15892436697791143320851843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42379831194109715522271581 15892436697791143320851843)
          ·
            refine ⟨23838655046686714981277765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15892436697791143320851843 23838655046686714981277765)
            ·
              refine ⟨4469747821253759058989581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23838655046686714981277765 4469747821253759058989581)
              ·
                refine ⟨1676155432970159647121093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4469747821253759058989581 1676155432970159647121093)
                ·
                  refine ⟨314279143681904933835205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1676155432970159647121093 314279143681904933835205)
                  ·
                    rfl

theorem cell22_2754254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_2754254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754254 prefixEnd_2754254 := by exact prefixLift 2754254
  have htrace : WordTrace (prefixWord ++ tailWord_2754254) baseStart_2754254 baseEnd_2754254 := by
    simpa [prefixWord, tailWord_2754254, baseEnd_2754254] using wordTrace_append hprefix tailTrace_2754254
  have hstable : (prefixWord ++ tailWord_2754254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754254).length < 2 ^ (prefixWord ++ tailWord_2754254).sum := by decide
  have hdescent : baseEnd_2754254 < baseStart_2754254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754265 : List Nat := [1, 2, 1, 2, 3, 4, 9]
def baseStart_2754265 : Nat := 118140960795 + 2754265 * 2 ^ 59
def prefixEnd_2754265 : Nat := 4983230072969 + 3 ^ 40 * 2754265 * 2
def baseEnd_2754265 : Nat := 34920044317426460721503

theorem tailTrace_2754265 : CollatzResearch.WordTrace tailWord_2754265 prefixEnd_2754265 34920044317426460721503 := by
  unfold tailWord_2754265
  simp only [CollatzResearch.WordTrace]
  refine ⟨100456297366775770857368249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66970864911183847238245499 100456297366775770857368249)
  ·
    refine ⟨75342223025081828143026187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100456297366775770857368249 75342223025081828143026187)
    ·
      refine ⟨113013334537622742214539281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75342223025081828143026187 113013334537622742214539281)
      ·
        refine ⟨84760000903217056660904461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113013334537622742214539281 84760000903217056660904461)
        ·
          refine ⟨31785000338706396247839173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84760000903217056660904461 31785000338706396247839173)
          ·
            refine ⟨5959687563507449296469845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31785000338706396247839173 5959687563507449296469845)
            ·
              refine ⟨34920044317426460721503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5959687563507449296469845 34920044317426460721503)
              ·
                rfl

theorem cell22_2754265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 9].length) (baseStart_2754265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754265 prefixEnd_2754265 := by exact prefixLift 2754265
  have htrace : WordTrace (prefixWord ++ tailWord_2754265) baseStart_2754265 baseEnd_2754265 := by
    simpa [prefixWord, tailWord_2754265, baseEnd_2754265] using wordTrace_append hprefix tailTrace_2754265
  have hstable : (prefixWord ++ tailWord_2754265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754265).length < 2 ^ (prefixWord ++ tailWord_2754265).sum := by decide
  have hdescent : baseEnd_2754265 < baseStart_2754265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754286 : List Nat := [4, 1, 2, 1, 1, 2, 5, 1, 2, 3]
def baseStart_2754286 : Nat := 118140960795 + 2754286 * 2 ^ 59
def prefixEnd_2754286 : Nat := 4983230072969 + 3 ^ 40 * 2754286 * 2
def baseEnd_2754286 : Nat := 942848385299677384705517

theorem tailTrace_2754286 : CollatzResearch.WordTrace tailWord_2754286 prefixEnd_2754286 942848385299677384705517 := by
  unfold tailWord_2754286
  simp only [CollatzResearch.WordTrace]
  refine ⟨12557132912462461430485339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66971375533133127629255141 12557132912462461430485339)
  ·
    refine ⟨18835699368693692145728009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12557132912462461430485339 18835699368693692145728009)
    ·
      refine ⟨14126774526520269109296007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18835699368693692145728009 14126774526520269109296007)
      ·
        refine ⟨21190161789780403663944011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14126774526520269109296007 21190161789780403663944011)
        ·
          refine ⟨31785242684670605495916017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21190161789780403663944011 31785242684670605495916017)
          ·
            refine ⟨23838932013502954121937013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31785242684670605495916017 23838932013502954121937013)
            ·
              refine ⟨2234899876265901948931595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23838932013502954121937013 2234899876265901948931595)
              ·
                refine ⟨3352349814398852923397393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234899876265901948931595 3352349814398852923397393)
                ·
                  refine ⟨2514262360799139692548045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3352349814398852923397393 2514262360799139692548045)
                  ·
                    refine ⟨942848385299677384705517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2514262360799139692548045 942848385299677384705517)
                    ·
                      rfl

theorem cell22_2754286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_2754286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754286 prefixEnd_2754286 := by exact prefixLift 2754286
  have htrace : WordTrace (prefixWord ++ tailWord_2754286) baseStart_2754286 baseEnd_2754286 := by
    simpa [prefixWord, tailWord_2754286, baseEnd_2754286] using wordTrace_append hprefix tailTrace_2754286
  have hstable : (prefixWord ++ tailWord_2754286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754286).length < 2 ^ (prefixWord ++ tailWord_2754286).sum := by decide
  have hdescent : baseEnd_2754286 < baseStart_2754286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754295 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 2, 6]
def baseStart_2754295 : Nat := 118140960795 + 2754295 * 2 ^ 59
def prefixEnd_2754295 : Nat := 4983230072969 + 3 ^ 40 * 2754295 * 2
def baseEnd_2754295 : Nat := 942851466183604361230489

theorem tailTrace_2754295 : CollatzResearch.WordTrace tailWord_2754295 prefixEnd_2754295 942851466183604361230489 := by
  unfold tailWord_2754295
  simp only [CollatzResearch.WordTrace]
  refine ⟨100457391556667085980960339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66971594371111390653973559 100457391556667085980960339)
  ·
    refine ⟨150686087335000628971440509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100457391556667085980960339 150686087335000628971440509)
    ·
      refine ⟨56507282750625235864290191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150686087335000628971440509 56507282750625235864290191)
      ·
        refine ⟨84760924125937853796435287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56507282750625235864290191 84760924125937853796435287)
        ·
          refine ⟨127141386188906780694652931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84760924125937853796435287 127141386188906780694652931)
          ·
            refine ⟨190712079283360171041979397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127141386188906780694652931 190712079283360171041979397)
            ·
              refine ⟨35758514865630032070371137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190712079283360171041979397 35758514865630032070371137)
              ·
                refine ⟨26818886149222524052778353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35758514865630032070371137 26818886149222524052778353)
                ·
                  refine ⟨20114164611916893039583765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26818886149222524052778353 20114164611916893039583765)
                  ·
                    refine ⟨942851466183604361230489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20114164611916893039583765 942851466183604361230489)
                    ·
                      rfl

theorem cell22_2754295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_2754295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754295 prefixEnd_2754295 := by exact prefixLift 2754295
  have htrace : WordTrace (prefixWord ++ tailWord_2754295) baseStart_2754295 baseEnd_2754295 := by
    simpa [prefixWord, tailWord_2754295, baseEnd_2754295] using wordTrace_append hprefix tailTrace_2754295
  have hstable : (prefixWord ++ tailWord_2754295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754295).length < 2 ^ (prefixWord ++ tailWord_2754295).sum := by decide
  have hdescent : baseEnd_2754295 < baseStart_2754295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754327 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 7]
def baseStart_2754327 : Nat := 118140960795 + 2754327 * 2 ^ 59
def prefixEnd_2754327 : Nat := 4983230072969 + 3 ^ 40 * 2754327 * 2
def baseEnd_2754327 : Nat := 314287473479188981476797

theorem tailTrace_2754327 : CollatzResearch.WordTrace tailWord_2754327 prefixEnd_2754327 314287473479188981476797 := by
  unfold tailWord_2754327
  simp only [CollatzResearch.WordTrace]
  refine ⟨100458558692551155446125235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66972372461700770297416823 100458558692551155446125235)
  ·
    refine ⟨150687838038826733169187853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100458558692551155446125235 150687838038826733169187853)
    ·
      refine ⟨56507939264560024938445445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150687838038826733169187853 56507939264560024938445445)
      ·
        refine ⟨10595238612105004675958521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56507939264560024938445445 10595238612105004675958521)
        ·
          refine ⟨7946428959078753506968891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10595238612105004675958521 7946428959078753506968891)
          ·
            refine ⟨11919643438618130260453337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7946428959078753506968891 11919643438618130260453337)
            ·
              refine ⟨8939732578963597695340003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11919643438618130260453337 8939732578963597695340003)
              ·
                refine ⟨13409598868445396543010005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8939732578963597695340003 13409598868445396543010005)
                ·
                  refine ⟨314287473479188981476797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13409598868445396543010005 314287473479188981476797)
                  ·
                    rfl

theorem cell22_2754327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 7].length) (baseStart_2754327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754327 prefixEnd_2754327 := by exact prefixLift 2754327
  have htrace : WordTrace (prefixWord ++ tailWord_2754327) baseStart_2754327 baseEnd_2754327 := by
    simpa [prefixWord, tailWord_2754327, baseEnd_2754327] using wordTrace_append hprefix tailTrace_2754327
  have hstable : (prefixWord ++ tailWord_2754327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754327).length < 2 ^ (prefixWord ++ tailWord_2754327).sum := by decide
  have hdescent : baseEnd_2754327 < baseStart_2754327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754344 : List Nat := [2, 1, 5, 1, 1, 3, 1, 3, 5]
def baseStart_2754344 : Nat := 118140960795 + 2754344 * 2 ^ 59
def prefixEnd_2754344 : Nat := 4983230072969 + 3 ^ 40 * 2754344 * 2
def baseEnd_2754344 : Nat := 314289413294994855585113

theorem tailTrace_2754344 : CollatzResearch.WordTrace tailWord_2754344 prefixEnd_2754344 314289413294994855585113 := by
  unfold tailWord_2754344
  simp only [CollatzResearch.WordTrace]
  refine ⟨50229589366744783674747043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66972785822326378232996057 50229589366744783674747043)
  ·
    refine ⟨75344384050117175512120565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50229589366744783674747043 75344384050117175512120565)
    ·
      refine ⟨7063536004698485204261303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75344384050117175512120565 7063536004698485204261303)
      ·
        refine ⟨10595304007047727806391955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7063536004698485204261303 10595304007047727806391955)
        ·
          refine ⟨15892956010571591709587933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10595304007047727806391955 15892956010571591709587933)
          ·
            refine ⟨5959858503964346891095475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15892956010571591709587933 5959858503964346891095475)
            ·
              refine ⟨8939787755946520336643213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5959858503964346891095475 8939787755946520336643213)
              ·
                refine ⟨3352420408479945126241205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8939787755946520336643213 3352420408479945126241205)
                ·
                  refine ⟨314289413294994855585113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3352420408479945126241205 314289413294994855585113)
                  ·
                    rfl

theorem cell22_2754344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 5].length) (baseStart_2754344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754344 prefixEnd_2754344 := by exact prefixLift 2754344
  have htrace : WordTrace (prefixWord ++ tailWord_2754344) baseStart_2754344 baseEnd_2754344 := by
    simpa [prefixWord, tailWord_2754344, baseEnd_2754344] using wordTrace_append hprefix tailTrace_2754344
  have hstable : (prefixWord ++ tailWord_2754344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754344).length < 2 ^ (prefixWord ++ tailWord_2754344).sum := by decide
  have hdescent : baseEnd_2754344 < baseStart_2754344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754449 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 3, 3]
def baseStart_2754449 : Nat := 118140960795 + 2754449 * 2 ^ 59
def prefixEnd_2754449 : Nat := 4983230072969 + 3 ^ 40 * 2754449 * 2
def baseEnd_2754449 : Nat := 942904183530799292880017

theorem tailTrace_2754449 : CollatzResearch.WordTrace tailWord_2754449 prefixEnd_2754449 942904183530799292880017 := by
  unfold tailWord_2754449
  simp only [CollatzResearch.WordTrace]
  refine ⟨100463008398109170282066401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66975338932072780188044267 100463008398109170282066401)
  ·
    refine ⟨75347256298581877711549801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100463008398109170282066401 75347256298581877711549801)
    ·
      refine ⟨56510442223936408283662351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75347256298581877711549801 56510442223936408283662351)
      ·
        refine ⟨84765663335904612425493527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56510442223936408283662351 84765663335904612425493527)
        ·
          refine ⟨127148495003856918638240291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84765663335904612425493527 127148495003856918638240291)
          ·
            refine ⟨190722742505785377957360437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127148495003856918638240291 190722742505785377957360437)
            ·
              refine ⟨17880257109917379183502541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 190722742505785377957360437 17880257109917379183502541)
              ·
                refine ⟨6705096416219017193813453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17880257109917379183502541 6705096416219017193813453)
                ·
                  refine ⟨2514411156082131447680045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6705096416219017193813453 2514411156082131447680045)
                  ·
                    refine ⟨942904183530799292880017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2514411156082131447680045 942904183530799292880017)
                    ·
                      rfl

theorem cell22_2754449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_2754449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754449 prefixEnd_2754449 := by exact prefixLift 2754449
  have htrace : WordTrace (prefixWord ++ tailWord_2754449) baseStart_2754449 baseEnd_2754449 := by
    simpa [prefixWord, tailWord_2754449, baseEnd_2754449] using wordTrace_append hprefix tailTrace_2754449
  have hstable : (prefixWord ++ tailWord_2754449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754449).length < 2 ^ (prefixWord ++ tailWord_2754449).sum := by decide
  have hdescent : baseEnd_2754449 < baseStart_2754449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754539 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 6, 3]
def baseStart_2754539 : Nat := 118140960795 + 2754539 * 2 ^ 59
def prefixEnd_2754539 : Nat := 4983230072969 + 3 ^ 40 * 2754539 * 2
def baseEnd_2754539 : Nat := 942934992370069058129741

theorem tailTrace_2754539 : CollatzResearch.WordTrace tailWord_2754539 prefixEnd_2754539 942934992370069058129741 := by
  unfold tailWord_2754539
  simp only [CollatzResearch.WordTrace]
  refine ⟨100466290967783115652842671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66977527311855410435228447 100466290967783115652842671)
  ·
    refine ⟨150699436451674673479264007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100466290967783115652842671 150699436451674673479264007)
    ·
      refine ⟨226049154677512010218896011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150699436451674673479264007 226049154677512010218896011)
      ·
        refine ⟨339073732016268015328344017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226049154677512010218896011 339073732016268015328344017)
        ·
          refine ⟨254305299012201011496258013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339073732016268015328344017 254305299012201011496258013)
          ·
            refine ⟨95364487129575379311096755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254305299012201011496258013 95364487129575379311096755)
            ·
              refine ⟨143046730694363068966645133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95364487129575379311096755 143046730694363068966645133)
              ·
                refine ⟨53642524010386150862491925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143046730694363068966645133 53642524010386150862491925)
                ·
                  refine ⟨2514493312986850821679309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53642524010386150862491925 2514493312986850821679309)
                  ·
                    refine ⟨942934992370069058129741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2514493312986850821679309 942934992370069058129741)
                    ·
                      rfl

theorem cell22_2754539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 3].length) (baseStart_2754539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754539 prefixEnd_2754539 := by exact prefixLift 2754539
  have htrace : WordTrace (prefixWord ++ tailWord_2754539) baseStart_2754539 baseEnd_2754539 := by
    simpa [prefixWord, tailWord_2754539, baseEnd_2754539] using wordTrace_append hprefix tailTrace_2754539
  have hstable : (prefixWord ++ tailWord_2754539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754539).length < 2 ^ (prefixWord ++ tailWord_2754539).sum := by decide
  have hdescent : baseEnd_2754539 < baseStart_2754539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754586 : List Nat := [3, 1, 1, 3, 1, 4, 3, 6]
def baseStart_2754586 : Nat := 118140960795 + 2754586 * 2 ^ 59
def prefixEnd_2754586 : Nat := 4983230072969 + 3 ^ 40 * 2754586 * 2
def baseEnd_2754586 : Nat := 104772342381175178022733

theorem tailTrace_2754586 : CollatzResearch.WordTrace tailWord_2754586 prefixEnd_2754586 104772342381175178022733 := by
  unfold tailWord_2754586
  simp only [CollatzResearch.WordTrace]
  refine ⟨25117001299653210669950903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66978670132408561786535741 25117001299653210669950903)
  ·
    refine ⟨37675501949479816004926355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25117001299653210669950903 37675501949479816004926355)
    ·
      refine ⟨56513252924219724007389533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37675501949479816004926355 56513252924219724007389533)
      ·
        refine ⟨21192469846582396502771075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56513252924219724007389533 21192469846582396502771075)
        ·
          refine ⟨31788704769873594754156613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21192469846582396502771075 31788704769873594754156613)
          ·
            refine ⟨5960382144351299016404365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31788704769873594754156613 5960382144351299016404365)
            ·
              refine ⟨2235143304131737131151637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5960382144351299016404365 2235143304131737131151637)
              ·
                refine ⟨104772342381175178022733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2235143304131737131151637 104772342381175178022733)
                ·
                  rfl

theorem cell22_2754586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 6].length) (baseStart_2754586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754586 prefixEnd_2754586 := by exact prefixLift 2754586
  have htrace : WordTrace (prefixWord ++ tailWord_2754586) baseStart_2754586 baseEnd_2754586 := by
    simpa [prefixWord, tailWord_2754586, baseEnd_2754586] using wordTrace_append hprefix tailTrace_2754586
  have hstable : (prefixWord ++ tailWord_2754586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754586).length < 2 ^ (prefixWord ++ tailWord_2754586).sum := by decide
  have hdescent : baseEnd_2754586 < baseStart_2754586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754588 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 2, 4]
def baseStart_2754588 : Nat := 118140960795 + 2754588 * 2 ^ 59
def prefixEnd_2754588 : Nat := 4983230072969 + 3 ^ 40 * 2754588 * 2
def baseEnd_2754588 : Nat := 942951766071449263654591

theorem tailTrace_2754588 : CollatzResearch.WordTrace tailWord_2754588 prefixEnd_2754588 942951766071449263654591 := by
  unfold tailWord_2754588
  simp only [CollatzResearch.WordTrace]
  refine ⟨50234039072302798510688209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66978718763070398014250945 50234039072302798510688209)
  ·
    refine ⟨37675529304227098883016157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50234039072302798510688209 37675529304227098883016157)
    ·
      refine ⟨14128323489085162081131059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37675529304227098883016157 14128323489085162081131059)
      ·
        refine ⟨21192485233627743121696589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14128323489085162081131059 21192485233627743121696589)
        ·
          refine ⟨7947181962610403670636221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21192485233627743121696589 7947181962610403670636221)
          ·
            refine ⟨2980193235978901376488583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7947181962610403670636221 2980193235978901376488583)
            ·
              refine ⟨4470289853968352064732875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2980193235978901376488583 4470289853968352064732875)
              ·
                refine ⟨6705434780952528097099313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4470289853968352064732875 6705434780952528097099313)
                ·
                  refine ⟨5029076085714396072824485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6705434780952528097099313 5029076085714396072824485)
                  ·
                    refine ⟨942951766071449263654591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5029076085714396072824485 942951766071449263654591)
                    ·
                      rfl

theorem cell22_2754588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_2754588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754588 prefixEnd_2754588 := by exact prefixLift 2754588
  have htrace : WordTrace (prefixWord ++ tailWord_2754588) baseStart_2754588 baseEnd_2754588 := by
    simpa [prefixWord, tailWord_2754588, baseEnd_2754588] using wordTrace_append hprefix tailTrace_2754588
  have hstable : (prefixWord ++ tailWord_2754588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754588).length < 2 ^ (prefixWord ++ tailWord_2754588).sum := by decide
  have hdescent : baseEnd_2754588 < baseStart_2754588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754652 : List Nat := [2, 2, 4, 1, 1, 4, 1, 3, 1, 3]
def baseStart_2754652 : Nat := 118140960795 + 2754652 * 2 ^ 59
def prefixEnd_2754652 : Nat := 4983230072969 + 3 ^ 40 * 2754652 * 2
def baseEnd_2754652 : Nat := 942973674579374430054395

theorem tailTrace_2754652 : CollatzResearch.WordTrace tailWord_2754652 prefixEnd_2754652 942973674579374430054395 := by
  unfold tailWord_2754652
  simp only [CollatzResearch.WordTrace]
  refine ⟨50235206208186867975853105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66980274944249157301137473 50235206208186867975853105)
  ·
    refine ⟨37676404656140150981889829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50235206208186867975853105 37676404656140150981889829)
    ·
      refine ⟨7064325873026278309104343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37676404656140150981889829 7064325873026278309104343)
      ·
        refine ⟨10596488809539417463656515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7064325873026278309104343 10596488809539417463656515)
        ·
          refine ⟨15894733214309126195484773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10596488809539417463656515 15894733214309126195484773)
          ·
            refine ⟨2980262477682961161653395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15894733214309126195484773 2980262477682961161653395)
            ·
              refine ⟨4470393716524441742480093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2980262477682961161653395 4470393716524441742480093)
              ·
                refine ⟨1676397643696665653430035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4470393716524441742480093 1676397643696665653430035)
                ·
                  refine ⟨2514596465544998480145053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676397643696665653430035 2514596465544998480145053)
                  ·
                    refine ⟨942973674579374430054395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2514596465544998480145053 942973674579374430054395)
                    ·
                      rfl

theorem cell22_2754652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_2754652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754652 prefixEnd_2754652 := by exact prefixLift 2754652
  have htrace : WordTrace (prefixWord ++ tailWord_2754652) baseStart_2754652 baseEnd_2754652 := by
    simpa [prefixWord, tailWord_2754652, baseEnd_2754652] using wordTrace_append hprefix tailTrace_2754652
  have hstable : (prefixWord ++ tailWord_2754652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754652).length < 2 ^ (prefixWord ++ tailWord_2754652).sum := by decide
  have hdescent : baseEnd_2754652 < baseStart_2754652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754659 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 8]
def baseStart_2754659 : Nat := 118140960795 + 2754659 * 2 ^ 59
def prefixEnd_2754659 : Nat := 4983230072969 + 3 ^ 40 * 2754659 * 2
def baseEnd_2754659 : Nat := 314325356940809581709791

theorem tailTrace_2754659 : CollatzResearch.WordTrace tailWord_2754659 prefixEnd_2754659 314325356940809581709791 := by
  unfold tailWord_2754659
  simp only [CollatzResearch.WordTrace]
  refine ⟨100470667727348376147211031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66980445151565584098140687 100470667727348376147211031)
  ·
    refine ⟨150706001591022564220816547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100470667727348376147211031 150706001591022564220816547)
    ·
      refine ⟨226059002386533846331224821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150706001591022564220816547 226059002386533846331224821)
      ·
        refine ⟨21193031473737548093552327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226059002386533846331224821 21193031473737548093552327)
        ·
          refine ⟨31789547210606322140328491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21193031473737548093552327 31789547210606322140328491)
          ·
            refine ⟨47684320815909483210492737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31789547210606322140328491 47684320815909483210492737)
            ·
              refine ⟨35763240611932112407869553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47684320815909483210492737 35763240611932112407869553)
              ·
                refine ⟨26822430458949084305902165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35763240611932112407869553 26822430458949084305902165)
                ·
                  refine ⟨314325356940809581709791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26822430458949084305902165 314325356940809581709791)
                  ·
                    rfl

theorem cell22_2754659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 8].length) (baseStart_2754659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754659 prefixEnd_2754659 := by exact prefixLift 2754659
  have htrace : WordTrace (prefixWord ++ tailWord_2754659) baseStart_2754659 baseEnd_2754659 := by
    simpa [prefixWord, tailWord_2754659, baseEnd_2754659] using wordTrace_append hprefix tailTrace_2754659
  have hstable : (prefixWord ++ tailWord_2754659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754659).length < 2 ^ (prefixWord ++ tailWord_2754659).sum := by decide
  have hdescent : baseEnd_2754659 < baseStart_2754659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754704 : List Nat := [2, 1, 1, 1, 1, 1, 5, 10]
def baseStart_2754704 : Nat := 118140960795 + 2754704 * 2 ^ 59
def prefixEnd_2754704 : Nat := 4983230072969 + 3 ^ 40 * 2754704 * 2
def baseEnd_2754704 : Nat := 104776830582451514194915

theorem tailTrace_2754704 : CollatzResearch.WordTrace tailWord_2754704 prefixEnd_2754704 104776830582451514194915 := by
  unfold tailWord_2754704
  simp only [CollatzResearch.WordTrace]
  refine ⟨50236154506092674416299583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66981539341456899221732777 50236154506092674416299583)
  ·
    refine ⟨75354231759139011624449375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50236154506092674416299583 75354231759139011624449375)
    ·
      refine ⟨113031347638708517436674063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75354231759139011624449375 113031347638708517436674063)
      ·
        refine ⟨169547021458062776155011095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113031347638708517436674063 169547021458062776155011095)
        ·
          refine ⟨254320532187094164232516643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169547021458062776155011095 254320532187094164232516643)
          ·
            refine ⟨381480798280641246348774965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254320532187094164232516643 381480798280641246348774965)
            ·
              refine ⟨35763824838810116845197653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 381480798280641246348774965 35763824838810116845197653)
              ·
                refine ⟨104776830582451514194915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35763824838810116845197653 104776830582451514194915)
                ·
                  rfl

theorem cell22_2754704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 10].length) (baseStart_2754704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754704 prefixEnd_2754704 := by exact prefixLift 2754704
  have htrace : WordTrace (prefixWord ++ tailWord_2754704) baseStart_2754704 baseEnd_2754704 := by
    simpa [prefixWord, tailWord_2754704, baseEnd_2754704] using wordTrace_append hprefix tailTrace_2754704
  have hstable : (prefixWord ++ tailWord_2754704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754704).length < 2 ^ (prefixWord ++ tailWord_2754704).sum := by decide
  have hdescent : baseEnd_2754704 < baseStart_2754704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754787 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 3, 3]
def baseStart_2754787 : Nat := 118140960795 + 2754787 * 2 ^ 59
def prefixEnd_2754787 : Nat := 4983230072969 + 3 ^ 40 * 2754787 * 2
def baseEnd_2754787 : Nat := 943019887838279077928981

theorem tailTrace_2754787 : CollatzResearch.WordTrace tailWord_2754787 prefixEnd_2754787 943019887838279077928981 := by
  unfold tailWord_2754787
  simp only [CollatzResearch.WordTrace]
  refine ⟨100475336270884654007870615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66983557513923102671913743 100475336270884654007870615)
  ·
    refine ⟨150713004406326981011805923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100475336270884654007870615 150713004406326981011805923)
    ·
      refine ⟨226069506609490471517708885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150713004406326981011805923 226069506609490471517708885)
      ·
        refine ⟨2649252030579966463098151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 226069506609490471517708885 2649252030579966463098151)
        ·
          refine ⟨3973878045869949694647227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2649252030579966463098151 3973878045869949694647227)
          ·
            refine ⟨5960817068804924541970841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3973878045869949694647227 5960817068804924541970841)
            ·
              refine ⟨4470612801603693406478131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5960817068804924541970841 4470612801603693406478131)
              ·
                refine ⟨6705919202405540109717197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4470612801603693406478131 6705919202405540109717197)
                ·
                  refine ⟨2514719700902077541143949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6705919202405540109717197 2514719700902077541143949)
                  ·
                    refine ⟨943019887838279077928981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2514719700902077541143949 943019887838279077928981)
                    ·
                      rfl

theorem cell22_2754787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 3].length) (baseStart_2754787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754787 prefixEnd_2754787 := by exact prefixLift 2754787
  have htrace : WordTrace (prefixWord ++ tailWord_2754787) baseStart_2754787 baseEnd_2754787 := by
    simpa [prefixWord, tailWord_2754787, baseEnd_2754787] using wordTrace_append hprefix tailTrace_2754787
  have hstable : (prefixWord ++ tailWord_2754787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754787).length < 2 ^ (prefixWord ++ tailWord_2754787).sum := by decide
  have hdescent : baseEnd_2754787 < baseStart_2754787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754843 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 4, 3]
def baseStart_2754843 : Nat := 118140960795 + 2754843 * 2 ^ 59
def prefixEnd_2754843 : Nat := 4983230072969 + 3 ^ 40 * 2754843 * 2
def baseEnd_2754843 : Nat := 943039057782713598528809

theorem tailTrace_2754843 : CollatzResearch.WordTrace tailWord_2754843 prefixEnd_2754843 943039057782713598528809 := by
  unfold tailWord_2754843
  simp only [CollatzResearch.WordTrace]
  refine ⟨100477378758681775571909183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66984919172454517047939455 100477378758681775571909183)
  ·
    refine ⟨150716068138022663357863775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100477378758681775571909183 150716068138022663357863775)
    ·
      refine ⟨226074102207033995036795663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150716068138022663357863775 226074102207033995036795663)
      ·
        refine ⟨339111153310550992555193495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226074102207033995036795663 339111153310550992555193495)
        ·
          refine ⟨508666729965826488832790243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339111153310550992555193495 508666729965826488832790243)
          ·
            refine ⟨763000094948739733249185365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508666729965826488832790243 763000094948739733249185365)
            ·
              refine ⟨8941407362680543749013891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 763000094948739733249185365 8941407362680543749013891)
              ·
                refine ⟨13412111044020815623520837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8941407362680543749013891 13412111044020815623520837)
                ·
                  refine ⟨2514770820753902929410157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13412111044020815623520837 2514770820753902929410157)
                  ·
                    refine ⟨943039057782713598528809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2514770820753902929410157 943039057782713598528809)
                    ·
                      rfl

theorem cell22_2754843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 3].length) (baseStart_2754843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754843 prefixEnd_2754843 := by exact prefixLift 2754843
  have htrace : WordTrace (prefixWord ++ tailWord_2754843) baseStart_2754843 baseEnd_2754843 := by
    simpa [prefixWord, tailWord_2754843, baseEnd_2754843] using wordTrace_append hprefix tailTrace_2754843
  have hstable : (prefixWord ++ tailWord_2754843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754843).length < 2 ^ (prefixWord ++ tailWord_2754843).sum := by decide
  have hdescent : baseEnd_2754843 < baseStart_2754843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754871 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 2, 7]
def baseStart_2754871 : Nat := 118140960795 + 2754871 * 2 ^ 59
def prefixEnd_2754871 : Nat := 4983230072969 + 3 ^ 40 * 2754871 * 2
def baseEnd_2754871 : Nat := 943048642754930858828723

theorem tailTrace_2754871 : CollatzResearch.WordTrace tailWord_2754871 prefixEnd_2754871 943048642754930858828723 := by
  unfold tailWord_2754871
  simp only [CollatzResearch.WordTrace]
  refine ⟨100478400002580336353928467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66985600001720224235952311 100478400002580336353928467)
  ·
    refine ⟨150717600003870504530892701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100478400002580336353928467 150717600003870504530892701)
    ·
      refine ⟨56519100001451439199084763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150717600003870504530892701 56519100001451439199084763)
      ·
        refine ⟨84778650002177158798627145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56519100001451439199084763 84778650002177158798627145)
        ·
          refine ⟨63583987501632869098970359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84778650002177158798627145 63583987501632869098970359)
          ·
            refine ⟨95375981252449303648455539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63583987501632869098970359 95375981252449303648455539)
            ·
              refine ⟨143063971878673955472683309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95375981252449303648455539 143063971878673955472683309)
              ·
                refine ⟨53648989454502733302256241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143063971878673955472683309 53648989454502733302256241)
                ·
                  refine ⟨40236742090877049976692181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53648989454502733302256241 40236742090877049976692181)
                  ·
                    refine ⟨943048642754930858828723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40236742090877049976692181 943048642754930858828723)
                    ·
                      rfl

theorem cell22_2754871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_2754871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754871 prefixEnd_2754871 := by exact prefixLift 2754871
  have htrace : WordTrace (prefixWord ++ tailWord_2754871) baseStart_2754871 baseEnd_2754871 := by
    simpa [prefixWord, tailWord_2754871, baseEnd_2754871] using wordTrace_append hprefix tailTrace_2754871
  have hstable : (prefixWord ++ tailWord_2754871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754871).length < 2 ^ (prefixWord ++ tailWord_2754871).sum := by decide
  have hdescent : baseEnd_2754871 < baseStart_2754871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754873 : List Nat := [1, 2, 1, 6, 1, 1, 2, 8]
def baseStart_2754873 : Nat := 118140960795 + 2754873 * 2 ^ 59
def prefixEnd_2754873 : Nat := 4983230072969 + 3 ^ 40 * 2754873 * 2
def baseEnd_2754873 : Nat := 104783258599533724475413

theorem tailTrace_2754873 : CollatzResearch.WordTrace tailWord_2754873 prefixEnd_2754873 104783258599533724475413 := by
  unfold tailWord_2754873
  simp only [CollatzResearch.WordTrace]
  refine ⟨100478472948573090695501273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66985648632382060463667515 100478472948573090695501273)
  ·
    refine ⟨75358854711429818021625955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100478472948573090695501273 75358854711429818021625955)
    ·
      refine ⟨113038282067144727032438933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75358854711429818021625955 113038282067144727032438933)
      ·
        refine ⟨5298669471897409079645575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 113038282067144727032438933 5298669471897409079645575)
        ·
          refine ⟨7948004207846113619468363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5298669471897409079645575 7948004207846113619468363)
          ·
            refine ⟨11922006311769170429202545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7948004207846113619468363 11922006311769170429202545)
            ·
              refine ⟨8941504733826877821901909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11922006311769170429202545 8941504733826877821901909)
              ·
                refine ⟨104783258599533724475413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8941504733826877821901909 104783258599533724475413)
                ·
                  rfl

theorem cell22_2754873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 8].length) (baseStart_2754873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754873 prefixEnd_2754873 := by exact prefixLift 2754873
  have htrace : WordTrace (prefixWord ++ tailWord_2754873) baseStart_2754873 baseEnd_2754873 := by
    simpa [prefixWord, tailWord_2754873, baseEnd_2754873] using wordTrace_append hprefix tailTrace_2754873
  have hstable : (prefixWord ++ tailWord_2754873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754873).length < 2 ^ (prefixWord ++ tailWord_2754873).sum := by decide
  have hdescent : baseEnd_2754873 < baseStart_2754873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2754922 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 3, 3]
def baseStart_2754922 : Nat := 118140960795 + 2754922 * 2 ^ 59
def prefixEnd_2754922 : Nat := 4983230072969 + 3 ^ 40 * 2754922 * 2
def baseEnd_2754922 : Nat := 943066101097183725803567

theorem tailTrace_2754922 : CollatzResearch.WordTrace tailWord_2754922 prefixEnd_2754922 943066101097183725803567 := by
  unfold tailWord_2754922
  simp only [CollatzResearch.WordTrace]
  refine ⟨25120065031348893016008755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66986840083597048042690013 25120065031348893016008755)
  ·
    refine ⟨37680097547023339524013133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25120065031348893016008755 37680097547023339524013133)
    ·
      refine ⟨14130036580133752321504925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37680097547023339524013133 14130036580133752321504925)
      ·
        refine ⟨5298763717550157120564347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14130036580133752321504925 5298763717550157120564347)
        ·
          refine ⟨7948145576325235680846521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5298763717550157120564347 7948145576325235680846521)
          ·
            refine ⟨5961109182243926760634891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7948145576325235680846521 5961109182243926760634891)
            ·
              refine ⟨8941663773365890140952337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5961109182243926760634891 8941663773365890140952337)
              ·
                refine ⟨6706247830024417605714253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8941663773365890140952337 6706247830024417605714253)
                ·
                  refine ⟨2514842936259156602142845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6706247830024417605714253 2514842936259156602142845)
                  ·
                    refine ⟨943066101097183725803567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2514842936259156602142845 943066101097183725803567)
                    ·
                      rfl

theorem cell22_2754922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_2754922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2754922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2754922 prefixEnd_2754922 := by exact prefixLift 2754922
  have htrace : WordTrace (prefixWord ++ tailWord_2754922) baseStart_2754922 baseEnd_2754922 := by
    simpa [prefixWord, tailWord_2754922, baseEnd_2754922] using wordTrace_append hprefix tailTrace_2754922
  have hstable : (prefixWord ++ tailWord_2754922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2754922).length < 2 ^ (prefixWord ++ tailWord_2754922).sum := by decide
  have hdescent : baseEnd_2754922 < baseStart_2754922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2754922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755029 : List Nat := [1, 3, 2, 3, 1, 2, 4, 1, 2, 3]
def baseStart_2755029 : Nat := 118140960795 + 2755029 * 2 ^ 59
def prefixEnd_2755029 : Nat := 4983230072969 + 3 ^ 40 * 2755029 * 2
def baseEnd_2755029 : Nat := 943102729383871113378239

theorem tailTrace_2755029 : CollatzResearch.WordTrace tailWord_2755029 prefixEnd_2755029 943102729383871113378239 := by
  unfold tailWord_2755029
  simp only [CollatzResearch.WordTrace]
  refine ⟨100484162736007929338180141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66989441824005286225453427 100484162736007929338180141)
  ·
    refine ⟨37681561026002973501817553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100484162736007929338180141 37681561026002973501817553)
    ·
      refine ⟨28261170769502230126363165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37681561026002973501817553 28261170769502230126363165)
      ·
        refine ⟨10597939038563336297386187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28261170769502230126363165 10597939038563336297386187)
        ·
          refine ⟨15896908557845004446079281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10597939038563336297386187 15896908557845004446079281)
          ·
            refine ⟨11922681418383753334559461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15896908557845004446079281 11922681418383753334559461)
            ·
              refine ⟨2235502765946953750229899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11922681418383753334559461 2235502765946953750229899)
              ·
                refine ⟨3353254148920430625344849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2235502765946953750229899 3353254148920430625344849)
                ·
                  refine ⟨2514940611690322969008637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3353254148920430625344849 2514940611690322969008637)
                  ·
                    refine ⟨943102729383871113378239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2514940611690322969008637 943102729383871113378239)
                    ·
                      rfl

theorem cell22_2755029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_2755029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755029 prefixEnd_2755029 := by exact prefixLift 2755029
  have htrace : WordTrace (prefixWord ++ tailWord_2755029) baseStart_2755029 baseEnd_2755029 := by
    simpa [prefixWord, tailWord_2755029, baseEnd_2755029] using wordTrace_append hprefix tailTrace_2755029
  have hstable : (prefixWord ++ tailWord_2755029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755029).length < 2 ^ (prefixWord ++ tailWord_2755029).sum := by decide
  have hdescent : baseEnd_2755029 < baseStart_2755029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755040 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 5, 3]
def baseStart_2755040 : Nat := 118140960795 + 2755040 * 2 ^ 59
def prefixEnd_2755040 : Nat := 4983230072969 + 3 ^ 40 * 2755040 * 2
def baseEnd_2755040 : Nat := 943106494908670751353205

theorem tailTrace_2755040 : CollatzResearch.WordTrace tailWord_2755040 prefixEnd_2755040 943106494908670751353205 := by
  unfold tailWord_2755040
  simp only [CollatzResearch.WordTrace]
  refine ⟨50242281969484039108415287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66989709292645385477887049 50242281969484039108415287)
  ·
    refine ⟨75363422954226058662622931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50242281969484039108415287 75363422954226058662622931)
    ·
      refine ⟨113045134431339087993934397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75363422954226058662622931 113045134431339087993934397)
      ·
        refine ⟨42391925411752157997725399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113045134431339087993934397 42391925411752157997725399)
        ·
          refine ⟨63587888117628236996588099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42391925411752157997725399 63587888117628236996588099)
          ·
            refine ⟨95381832176442355494882149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63587888117628236996588099 95381832176442355494882149)
            ·
              refine ⟨17884093533082941655290403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95381832176442355494882149 17884093533082941655290403)
              ·
                refine ⟨26826140299624412482935605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17884093533082941655290403 26826140299624412482935605)
                ·
                  refine ⟨2514950653089788670275213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26826140299624412482935605 2514950653089788670275213)
                  ·
                    refine ⟨943106494908670751353205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2514950653089788670275213 943106494908670751353205)
                    ·
                      rfl

theorem cell22_2755040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 5, 3].length) (baseStart_2755040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755040 prefixEnd_2755040 := by exact prefixLift 2755040
  have htrace : WordTrace (prefixWord ++ tailWord_2755040) baseStart_2755040 baseEnd_2755040 := by
    simpa [prefixWord, tailWord_2755040, baseEnd_2755040] using wordTrace_append hprefix tailTrace_2755040
  have hstable : (prefixWord ++ tailWord_2755040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755040).length < 2 ^ (prefixWord ++ tailWord_2755040).sum := by decide
  have hdescent : baseEnd_2755040 < baseStart_2755040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755108 : List Nat := [2, 3, 1, 5, 1, 1, 2, 3, 1, 3]
def baseStart_2755108 : Nat := 118140960795 + 2755108 * 2 ^ 59
def prefixEnd_2755108 : Nat := 4983230072969 + 3 ^ 40 * 2755108 * 2
def baseEnd_2755108 : Nat := 943129772698341240652997

theorem tailTrace_2755108 : CollatzResearch.WordTrace tailWord_2755108 prefixEnd_2755108 943129772698341240652997 := by
  unfold tailWord_2755108
  simp only [CollatzResearch.WordTrace]
  refine ⟨50243522051360862915152989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66991362735147817220203985 50243522051360862915152989)
  ·
    refine ⟨18841320769260323593182371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50243522051360862915152989 18841320769260323593182371)
    ·
      refine ⟨28261981153890485389773557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18841320769260323593182371 28261981153890485389773557)
      ·
        refine ⟨2649560733177233005291271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28261981153890485389773557 2649560733177233005291271)
        ·
          refine ⟨3974341099765849507936907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2649560733177233005291271 3974341099765849507936907)
          ·
            refine ⟨5961511649648774261905361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3974341099765849507936907 5961511649648774261905361)
            ·
              refine ⟨4471133737236580696429021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5961511649648774261905361 4471133737236580696429021)
              ·
                refine ⟨1676675151463717761160883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4471133737236580696429021 1676675151463717761160883)
                ·
                  refine ⟨2515012727195576641741325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676675151463717761160883 2515012727195576641741325)
                  ·
                    refine ⟨943129772698341240652997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2515012727195576641741325 943129772698341240652997)
                    ·
                      rfl

theorem cell22_2755108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_2755108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755108 prefixEnd_2755108 := by exact prefixLift 2755108
  have htrace : WordTrace (prefixWord ++ tailWord_2755108) baseStart_2755108 baseEnd_2755108 := by
    simpa [prefixWord, tailWord_2755108, baseEnd_2755108] using wordTrace_append hprefix tailTrace_2755108
  have hstable : (prefixWord ++ tailWord_2755108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755108).length < 2 ^ (prefixWord ++ tailWord_2755108).sum := by decide
  have hdescent : baseEnd_2755108 < baseStart_2755108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755132 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 6]
def baseStart_2755132 : Nat := 118140960795 + 2755132 * 2 ^ 59
def prefixEnd_2755132 : Nat := 4983230072969 + 3 ^ 40 * 2755132 * 2
def baseEnd_2755132 : Nat := 314379329462937726017641

theorem tailTrace_2755132 : CollatzResearch.WordTrace tailWord_2755132 prefixEnd_2755132 314379329462937726017641 := by
  unfold tailWord_2755132
  simp only [CollatzResearch.WordTrace]
  refine ⟨50243959727317388964589825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66991946303089851952786433 50243959727317388964589825)
  ·
    refine ⟨37682969795488041723442369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50243959727317388964589825 37682969795488041723442369)
    ·
      refine ⟨28262227346616031292581777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37682969795488041723442369 28262227346616031292581777)
      ·
        refine ⟨21196670509962023469436333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28262227346616031292581777 21196670509962023469436333)
        ·
          refine ⟨7948751441235758801038625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21196670509962023469436333 7948751441235758801038625)
          ·
            refine ⟨5961563580926819100778969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7948751441235758801038625 5961563580926819100778969)
            ·
              refine ⟨4471172685695114325584227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5961563580926819100778969 4471172685695114325584227)
              ·
                refine ⟨6706759028542671488376341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4471172685695114325584227 6706759028542671488376341)
                ·
                  refine ⟨314379329462937726017641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6706759028542671488376341 314379329462937726017641)
                  ·
                    rfl

theorem cell22_2755132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_2755132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755132 prefixEnd_2755132 := by exact prefixLift 2755132
  have htrace : WordTrace (prefixWord ++ tailWord_2755132) baseStart_2755132 baseEnd_2755132 := by
    simpa [prefixWord, tailWord_2755132, baseEnd_2755132] using wordTrace_append hprefix tailTrace_2755132
  have hstable : (prefixWord ++ tailWord_2755132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755132).length < 2 ^ (prefixWord ++ tailWord_2755132).sum := by decide
  have hdescent : baseEnd_2755132 < baseStart_2755132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755147 : List Nat := [1, 1, 1, 1, 3, 1, 4, 5, 2, 3]
def baseStart_2755147 : Nat := 118140960795 + 2755147 * 2 ^ 59
def prefixEnd_2755147 : Nat := 4983230072969 + 3 ^ 40 * 2755147 * 2
def baseEnd_2755147 : Nat := 943143123195358138927877

theorem tailTrace_2755147 : CollatzResearch.WordTrace tailWord_2755147 prefixEnd_2755147 943143123195358138927877 := by
  unfold tailWord_2755147
  simp only [CollatzResearch.WordTrace]
  refine ⟨100488466549580435490975695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66992311033053623660650463 100488466549580435490975695)
  ·
    refine ⟨150732699824370653236463543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100488466549580435490975695 150732699824370653236463543)
    ·
      refine ⟨226099049736555979854695315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150732699824370653236463543 226099049736555979854695315)
      ·
        refine ⟨339148574604833969782042973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226099049736555979854695315 339148574604833969782042973)
        ·
          refine ⟨127180715476812738668266115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339148574604833969782042973 127180715476812738668266115)
          ·
            refine ⟨190771073215219108002399173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127180715476812738668266115 190771073215219108002399173)
            ·
              refine ⟨35769576227853582750449845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190771073215219108002399173 35769576227853582750449845)
              ·
                refine ⟨3353397771361273382854673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35769576227853582750449845 3353397771361273382854673)
                ·
                  refine ⟨2515048328520955037141005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3353397771361273382854673 2515048328520955037141005)
                  ·
                    refine ⟨943143123195358138927877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2515048328520955037141005 943143123195358138927877)
                    ·
                      rfl

theorem cell22_2755147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 3].length) (baseStart_2755147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755147 prefixEnd_2755147 := by exact prefixLift 2755147
  have htrace : WordTrace (prefixWord ++ tailWord_2755147) baseStart_2755147 baseEnd_2755147 := by
    simpa [prefixWord, tailWord_2755147, baseEnd_2755147] using wordTrace_append hprefix tailTrace_2755147
  have hstable : (prefixWord ++ tailWord_2755147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755147).length < 2 ^ (prefixWord ++ tailWord_2755147).sum := by decide
  have hdescent : baseEnd_2755147 < baseStart_2755147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755202 : List Nat := [3, 4, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2755202 : Nat := 118140960795 + 2755202 * 2 ^ 59
def prefixEnd_2755202 : Nat := 4983230072969 + 3 ^ 40 * 2755202 * 2
def baseEnd_2755202 : Nat := 943161950819356328802709

theorem tailTrace_2755202 : CollatzResearch.WordTrace tailWord_2755202 prefixEnd_2755202 943161950819356328802709 := by
  unfold tailWord_2755202
  simp only [CollatzResearch.WordTrace]
  refine ⟨25122618141095294971056965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66993648376254119922818573 25122618141095294971056965)
  ·
    refine ⟨4710490901455367807073181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25122618141095294971056965 4710490901455367807073181)
    ·
      refine ⟨1766434088045762927652443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4710490901455367807073181 1766434088045762927652443)
      ·
        refine ⟨2649651132068644391478665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1766434088045762927652443 2649651132068644391478665)
        ·
          refine ⟨1987238349051483293608999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2649651132068644391478665 1987238349051483293608999)
          ·
            refine ⟨2980857523577224940413499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1987238349051483293608999 2980857523577224940413499)
            ·
              refine ⟨4471286285365837410620249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2980857523577224940413499 4471286285365837410620249)
              ·
                refine ⟨3353464714024378057965187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4471286285365837410620249 3353464714024378057965187)
                ·
                  refine ⟨5030197071036567086947781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3353464714024378057965187 5030197071036567086947781)
                  ·
                    refine ⟨943161950819356328802709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5030197071036567086947781 943161950819356328802709)
                    ·
                      rfl

theorem cell22_2755202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2755202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755202 prefixEnd_2755202 := by exact prefixLift 2755202
  have htrace : WordTrace (prefixWord ++ tailWord_2755202) baseStart_2755202 baseEnd_2755202 := by
    simpa [prefixWord, tailWord_2755202, baseEnd_2755202] using wordTrace_append hprefix tailTrace_2755202
  have hstable : (prefixWord ++ tailWord_2755202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755202).length < 2 ^ (prefixWord ++ tailWord_2755202).sum := by decide
  have hdescent : baseEnd_2755202 < baseStart_2755202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755342 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_2755342 : Nat := 118140960795 + 2755342 * 2 ^ 59
def prefixEnd_2755342 : Nat := 4983230072969 + 3 ^ 40 * 2755342 * 2
def baseEnd_2755342 : Nat := 943209875680442630302279

theorem tailTrace_2755342 : CollatzResearch.WordTrace tailWord_2755342 prefixEnd_2755342 943209875680442630302279 := by
  unfold tailWord_2755342
  simp only [CollatzResearch.WordTrace]
  refine ⟨12561947347984247974290535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66997052522582655862882853 12561947347984247974290535)
  ·
    refine ⟨18842921021976371961435803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12561947347984247974290535 18842921021976371961435803)
    ·
      refine ⟨28264381532964557942153705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18842921021976371961435803 28264381532964557942153705)
      ·
        refine ⟨21198286149723418456615279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28264381532964557942153705 21198286149723418456615279)
        ·
          refine ⟨31797429224585127684922919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21198286149723418456615279 31797429224585127684922919)
          ·
            refine ⟨47696143836877691527384379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31797429224585127684922919 47696143836877691527384379)
            ·
              refine ⟨71544215755316537291076569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47696143836877691527384379 71544215755316537291076569)
              ·
                refine ⟨53658161816487402968307427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71544215755316537291076569 53658161816487402968307427)
                ·
                  refine ⟨80487242724731104452461141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53658161816487402968307427 80487242724731104452461141)
                  ·
                    refine ⟨943209875680442630302279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80487242724731104452461141 943209875680442630302279)
                    ·
                      rfl

theorem cell22_2755342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_2755342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755342 prefixEnd_2755342 := by exact prefixLift 2755342
  have htrace : WordTrace (prefixWord ++ tailWord_2755342) baseStart_2755342 baseEnd_2755342 := by
    simpa [prefixWord, tailWord_2755342, baseEnd_2755342] using wordTrace_append hprefix tailTrace_2755342
  have hstable : (prefixWord ++ tailWord_2755342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755342).length < 2 ^ (prefixWord ++ tailWord_2755342).sum := by decide
  have hdescent : baseEnd_2755342 < baseStart_2755342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755346 : List Nat := [3, 2, 4, 1, 2, 2, 8]
def baseStart_2755346 : Nat := 118140960795 + 2755346 * 2 ^ 59
def prefixEnd_2755346 : Nat := 4983230072969 + 3 ^ 40 * 2755346 * 2
def baseEnd_2755346 : Nat := 34933749813414368637121

theorem tailTrace_2755346 : CollatzResearch.WordTrace tailWord_2755346 prefixEnd_2755346 34933749813414368637121 := by
  unfold tailWord_2755346
  simp only [CollatzResearch.WordTrace]
  refine ⟨25123931168964873119367473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66997149783906328318313261 25123931168964873119367473)
  ·
    refine ⟨18842948376723654839525605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25123931168964873119367473 18842948376723654839525605)
    ·
      refine ⟨3533052820635685282411051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18842948376723654839525605 3533052820635685282411051)
      ·
        refine ⟨5299579230953527923616577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3533052820635685282411051 5299579230953527923616577)
        ·
          refine ⟨3974684423215145942712433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5299579230953527923616577 3974684423215145942712433)
          ·
            refine ⟨2981013317411359457034325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3974684423215145942712433 2981013317411359457034325)
            ·
              refine ⟨34933749813414368637121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2981013317411359457034325 34933749813414368637121)
              ·
                rfl

theorem cell22_2755346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 8].length) (baseStart_2755346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755346 prefixEnd_2755346 := by exact prefixLift 2755346
  have htrace : WordTrace (prefixWord ++ tailWord_2755346) baseStart_2755346 baseEnd_2755346 := by
    simpa [prefixWord, tailWord_2755346, baseEnd_2755346] using wordTrace_append hprefix tailTrace_2755346
  have hstable : (prefixWord ++ tailWord_2755346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755346).length < 2 ^ (prefixWord ++ tailWord_2755346).sum := by decide
  have hdescent : baseEnd_2755346 < baseStart_2755346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755372 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_2755372 : Nat := 118140960795 + 2755372 * 2 ^ 59
def prefixEnd_2755372 : Nat := 4983230072969 + 3 ^ 40 * 2755372 * 2
def baseEnd_2755372 : Nat := 943220145293532552052187

theorem tailTrace_2755372 : CollatzResearch.WordTrace tailWord_2755372 prefixEnd_2755372 943220145293532552052187 := by
  unfold tailWord_2755372
  simp only [CollatzResearch.WordTrace]
  refine ⟨50248336486882649458958185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66997781982510199278610913 50248336486882649458958185)
  ·
    refine ⟨37686252365161987094218639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50248336486882649458958185 37686252365161987094218639)
    ·
      refine ⟨56529378547742980641327959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37686252365161987094218639 56529378547742980641327959)
      ·
        refine ⟨84794067821614470961991939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56529378547742980641327959 84794067821614470961991939)
        ·
          refine ⟨127191101732421706442987909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84794067821614470961991939 127191101732421706442987909)
          ·
            refine ⟨23848331574829069958060233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127191101732421706442987909 23848331574829069958060233)
            ·
              refine ⟨17886248681121802468545175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23848331574829069958060233 17886248681121802468545175)
              ·
                refine ⟨26829373021682703702817763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17886248681121802468545175 26829373021682703702817763)
                ·
                  refine ⟨40244059532524055554226645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26829373021682703702817763 40244059532524055554226645)
                  ·
                    refine ⟨943220145293532552052187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40244059532524055554226645 943220145293532552052187)
                    ·
                      rfl

theorem cell22_2755372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_2755372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755372 prefixEnd_2755372 := by exact prefixLift 2755372
  have htrace : WordTrace (prefixWord ++ tailWord_2755372) baseStart_2755372 baseEnd_2755372 := by
    simpa [prefixWord, tailWord_2755372, baseEnd_2755372] using wordTrace_append hprefix tailTrace_2755372
  have hstable : (prefixWord ++ tailWord_2755372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755372).length < 2 ^ (prefixWord ++ tailWord_2755372).sum := by decide
  have hdescent : baseEnd_2755372 < baseStart_2755372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755402 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 10]
def baseStart_2755402 : Nat := 118140960795 + 2755402 * 2 ^ 59
def prefixEnd_2755402 : Nat := 4983230072969 + 3 ^ 40 * 2755402 * 2
def baseEnd_2755402 : Nat := 314410138302207491267365

theorem tailTrace_2755402 : CollatzResearch.WordTrace tailWord_2755402 prefixEnd_2755402 314410138302207491267365 := by
  unfold tailWord_2755402
  simp only [CollatzResearch.WordTrace]
  refine ⟨25124441790914153510377115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66998511442437742694338973 25124441790914153510377115)
  ·
    refine ⟨37686662686371230265565673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25124441790914153510377115 37686662686371230265565673)
    ·
      refine ⟨28264997014778422699174255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37686662686371230265565673 28264997014778422699174255)
      ·
        refine ⟨42397495522167634048761383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28264997014778422699174255 42397495522167634048761383)
        ·
          refine ⟨63596243283251451073142075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42397495522167634048761383 63596243283251451073142075)
          ·
            refine ⟨95394364924877176609713113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63596243283251451073142075 95394364924877176609713113)
            ·
              refine ⟨71545773693657882457284835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95394364924877176609713113 71545773693657882457284835)
              ·
                refine ⟨107318660540486823685927253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71545773693657882457284835 107318660540486823685927253)
                ·
                  refine ⟨314410138302207491267365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 107318660540486823685927253 314410138302207491267365)
                  ·
                    rfl

theorem cell22_2755402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_2755402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755402 prefixEnd_2755402 := by exact prefixLift 2755402
  have htrace : WordTrace (prefixWord ++ tailWord_2755402) baseStart_2755402 baseEnd_2755402 := by
    simpa [prefixWord, tailWord_2755402, baseEnd_2755402] using wordTrace_append hprefix tailTrace_2755402
  have hstable : (prefixWord ++ tailWord_2755402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755402).length < 2 ^ (prefixWord ++ tailWord_2755402).sum := by decide
  have hdescent : baseEnd_2755402 < baseStart_2755402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755412 : List Nat := [2, 4, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_2755412 : Nat := 118140960795 + 2755412 * 2 ^ 59
def prefixEnd_2755412 : Nat := 4983230072969 + 3 ^ 40 * 2755412 * 2
def baseEnd_2755412 : Nat := 943233838110985781052065

theorem tailTrace_2755412 : CollatzResearch.WordTrace tailWord_2755412 prefixEnd_2755412 943233838110985781052065 := by
  unfold tailWord_2755412
  simp only [CollatzResearch.WordTrace]
  refine ⟨50249065946810192874686245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66998754595746923832914993 50249065946810192874686245)
  ·
    refine ⟨9421699865026911164003671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50249065946810192874686245 9421699865026911164003671)
    ·
      refine ⟨14132549797540366746005507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9421699865026911164003671 14132549797540366746005507)
      ·
        refine ⟨21198824696310550119008261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14132549797540366746005507 21198824696310550119008261)
        ·
          refine ⟨3974779630558228147314049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21198824696310550119008261 3974779630558228147314049)
          ·
            refine ⟨2981084722918671110485537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3974779630558228147314049 2981084722918671110485537)
            ·
              refine ⟨2235813542189003332864153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2981084722918671110485537 2235813542189003332864153)
              ·
                refine ⟨1676860156641752499648115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2235813542189003332864153 1676860156641752499648115)
                ·
                  refine ⟨2515290234962628749472173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676860156641752499648115 2515290234962628749472173)
                  ·
                    refine ⟨943233838110985781052065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2515290234962628749472173 943233838110985781052065)
                    ·
                      rfl

theorem cell22_2755412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_2755412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755412 prefixEnd_2755412 := by exact prefixLift 2755412
  have htrace : WordTrace (prefixWord ++ tailWord_2755412) baseStart_2755412 baseEnd_2755412 := by
    simpa [prefixWord, tailWord_2755412, baseEnd_2755412] using wordTrace_append hprefix tailTrace_2755412
  have hstable : (prefixWord ++ tailWord_2755412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755412).length < 2 ^ (prefixWord ++ tailWord_2755412).sum := by decide
  have hdescent : baseEnd_2755412 < baseStart_2755412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755447 : List Nat := [1, 1, 3, 1, 1, 2, 1, 12]
def baseStart_2755447 : Nat := 118140960795 + 2755447 * 2 ^ 59
def prefixEnd_2755447 : Nat := 4983230072969 + 3 ^ 40 * 2755447 * 2
def baseEnd_2755447 : Nat := 104805091036250817380773

theorem tailTrace_2755447 : CollatzResearch.WordTrace tailWord_2755447 prefixEnd_2755447 104805091036250817380773 := by
  unfold tailWord_2755447
  simp only [CollatzResearch.WordTrace]
  refine ⟨100499408448493586726896595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66999605632329057817931063 100499408448493586726896595)
  ·
    refine ⟨150749112672740380090344893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100499408448493586726896595 150749112672740380090344893)
    ·
      refine ⟨56530917252277642533879335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150749112672740380090344893 56530917252277642533879335)
      ·
        refine ⟨84796375878416463800819003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56530917252277642533879335 84796375878416463800819003)
        ·
          refine ⟨127194563817624695701228505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84796375878416463800819003 127194563817624695701228505)
          ·
            refine ⟨95395922863218521775921379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127194563817624695701228505 95395922863218521775921379)
            ·
              refine ⟨143093884294827782663882069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95395922863218521775921379 143093884294827782663882069)
              ·
                refine ⟨104805091036250817380773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 143093884294827782663882069 104805091036250817380773)
                ·
                  rfl

theorem cell22_2755447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 12].length) (baseStart_2755447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755447 prefixEnd_2755447 := by exact prefixLift 2755447
  have htrace : WordTrace (prefixWord ++ tailWord_2755447) baseStart_2755447 baseEnd_2755447 := by
    simpa [prefixWord, tailWord_2755447, baseEnd_2755447] using wordTrace_append hprefix tailTrace_2755447
  have hstable : (prefixWord ++ tailWord_2755447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755447).length < 2 ^ (prefixWord ++ tailWord_2755447).sum := by decide
  have hdescent : baseEnd_2755447 < baseStart_2755447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755449 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 1, 6]
def baseStart_2755449 : Nat := 118140960795 + 2755449 * 2 ^ 59
def prefixEnd_2755449 : Nat := 4983230072969 + 3 ^ 40 * 2755449 * 2
def baseEnd_2755449 : Nat := 943246503967130017876951

theorem tailTrace_2755449 : CollatzResearch.WordTrace tailWord_2755449 prefixEnd_2755449 943246503967130017876951 := by
  unfold tailWord_2755449
  simp only [CollatzResearch.WordTrace]
  refine ⟨100499481394486341068469401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66999654262990894045646267 100499481394486341068469401)
  ·
    refine ⟨75374611045864755801352051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100499481394486341068469401 75374611045864755801352051)
    ·
      refine ⟨113061916568797133702028077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75374611045864755801352051 113061916568797133702028077)
      ·
        refine ⟨42398218713298925138260529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113061916568797133702028077 42398218713298925138260529)
        ·
          refine ⟨31798664034974193853695397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42398218713298925138260529 31798664034974193853695397)
          ·
            refine ⟨5962249506557661347567887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31798664034974193853695397 5962249506557661347567887)
            ·
              refine ⟨8943374259836492021351831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5962249506557661347567887 8943374259836492021351831)
              ·
                refine ⟨13415061389754738032027747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8943374259836492021351831 13415061389754738032027747)
                ·
                  refine ⟨20122592084632107048041621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13415061389754738032027747 20122592084632107048041621)
                  ·
                    refine ⟨943246503967130017876951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20122592084632107048041621 943246503967130017876951)
                    ·
                      rfl

theorem cell22_2755449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_2755449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755449 prefixEnd_2755449 := by exact prefixLift 2755449
  have htrace : WordTrace (prefixWord ++ tailWord_2755449) baseStart_2755449 baseEnd_2755449 := by
    simpa [prefixWord, tailWord_2755449, baseEnd_2755449] using wordTrace_append hprefix tailTrace_2755449
  have hstable : (prefixWord ++ tailWord_2755449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755449).length < 2 ^ (prefixWord ++ tailWord_2755449).sum := by decide
  have hdescent : baseEnd_2755449 < baseStart_2755449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755464 : List Nat := [2, 1, 3, 3, 2, 2, 9]
def baseStart_2755464 : Nat := 118140960795 + 2755464 * 2 ^ 59
def prefixEnd_2755464 : Nat := 4983230072969 + 3 ^ 40 * 2755464 * 2
def baseEnd_2755464 : Nat := 34935245880506480694515

theorem tailTrace_2755464 : CollatzResearch.WordTrace tailWord_2755464 prefixEnd_2755464 34935245880506480694515 := by
  unfold tailWord_2755464
  simp only [CollatzResearch.WordTrace]
  refine ⟨50250014244715999315132723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67000018992954665753510297 50250014244715999315132723)
  ·
    refine ⟨75375021367073998972699085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50250014244715999315132723 75375021367073998972699085)
    ·
      refine ⟨28265633012652749614762157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75375021367073998972699085 28265633012652749614762157)
      ·
        refine ⟨10599612379744781105535809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28265633012652749614762157 10599612379744781105535809)
        ·
          refine ⟨7949709284808585829151857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10599612379744781105535809 7949709284808585829151857)
          ·
            refine ⟨5962281963606439371863893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7949709284808585829151857 5962281963606439371863893)
            ·
              refine ⟨34935245880506480694515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5962281963606439371863893 34935245880506480694515)
              ·
                rfl

theorem cell22_2755464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 9].length) (baseStart_2755464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755464 prefixEnd_2755464 := by exact prefixLift 2755464
  have htrace : WordTrace (prefixWord ++ tailWord_2755464) baseStart_2755464 baseEnd_2755464 := by
    simpa [prefixWord, tailWord_2755464, baseEnd_2755464] using wordTrace_append hprefix tailTrace_2755464
  have hstable : (prefixWord ++ tailWord_2755464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755464).length < 2 ^ (prefixWord ++ tailWord_2755464).sum := by decide
  have hdescent : baseEnd_2755464 < baseStart_2755464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755509 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 9]
def baseStart_2755509 : Nat := 118140960795 + 2755509 * 2 ^ 59
def prefixEnd_2755509 : Nat := 4983230072969 + 3 ^ 40 * 2755509 * 2
def baseEnd_2755509 : Nat := 314422347731103287125589

theorem tailTrace_2755509 : CollatzResearch.WordTrace tailWord_2755509 prefixEnd_2755509 314422347731103287125589 := by
  unfold tailWord_2755509
  simp only [CollatzResearch.WordTrace]
  refine ⟨100501669774268971315653581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67001113182845980877102387 100501669774268971315653581)
  ·
    refine ⟨37688126165350864243370093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100501669774268971315653581 37688126165350864243370093)
    ·
      refine ⟨14133047312006574091263785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37688126165350864243370093 14133047312006574091263785)
      ·
        refine ⟨10599785484004930568447839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14133047312006574091263785 10599785484004930568447839)
        ·
          refine ⟨15899678226007395852671759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10599785484004930568447839 15899678226007395852671759)
          ·
            refine ⟨23849517339011093779007639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15899678226007395852671759 23849517339011093779007639)
            ·
              refine ⟨35774276008516640668511459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23849517339011093779007639 35774276008516640668511459)
              ·
                refine ⟨53661414012774961002767189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35774276008516640668511459 53661414012774961002767189)
                ·
                  refine ⟨314422347731103287125589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53661414012774961002767189 314422347731103287125589)
                  ·
                    rfl

theorem cell22_2755509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_2755509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755509 prefixEnd_2755509 := by exact prefixLift 2755509
  have htrace : WordTrace (prefixWord ++ tailWord_2755509) baseStart_2755509 baseEnd_2755509 := by
    simpa [prefixWord, tailWord_2755509, baseEnd_2755509] using wordTrace_append hprefix tailTrace_2755509
  have hstable : (prefixWord ++ tailWord_2755509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755509).length < 2 ^ (prefixWord ++ tailWord_2755509).sum := by decide
  have hdescent : baseEnd_2755509 < baseStart_2755509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755556 : List Nat := [2, 3, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_2755556 : Nat := 118140960795 + 2755556 * 2 ^ 59
def prefixEnd_2755556 : Nat := 4983230072969 + 3 ^ 40 * 2755556 * 2
def baseEnd_2755556 : Nat := 943283132253817405451623

theorem tailTrace_2755556 : CollatzResearch.WordTrace tailWord_2755556 prefixEnd_2755556 943283132253817405451623 := by
  unfold tailWord_2755556
  simp only [CollatzResearch.WordTrace]
  refine ⟨50251692002549349171307261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67002256003399132228409681 50251692002549349171307261)
  ·
    refine ⟨18844384500956005939240223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50251692002549349171307261 18844384500956005939240223)
    ·
      refine ⟨28266576751434008908860335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18844384500956005939240223 28266576751434008908860335)
      ·
        refine ⟨42399865127151013363290503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28266576751434008908860335 42399865127151013363290503)
        ·
          refine ⟨63599797690726520044935755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42399865127151013363290503 63599797690726520044935755)
          ·
            refine ⟨95399696536089780067403633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63599797690726520044935755 95399696536089780067403633)
            ·
              refine ⟨71549772402067335050552725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95399696536089780067403633 71549772402067335050552725)
              ·
                refine ⟨3353895581346906330494659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71549772402067335050552725 3353895581346906330494659)
                ·
                  refine ⟨5030843372020359495741989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3353895581346906330494659 5030843372020359495741989)
                  ·
                    refine ⟨943283132253817405451623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5030843372020359495741989 943283132253817405451623)
                    ·
                      rfl

theorem cell22_2755556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_2755556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755556 prefixEnd_2755556 := by exact prefixLift 2755556
  have htrace : WordTrace (prefixWord ++ tailWord_2755556) baseStart_2755556 baseEnd_2755556 := by
    simpa [prefixWord, tailWord_2755556, baseEnd_2755556] using wordTrace_append hprefix tailTrace_2755556
  have hstable : (prefixWord ++ tailWord_2755556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755556).length < 2 ^ (prefixWord ++ tailWord_2755556).sum := by decide
  have hdescent : baseEnd_2755556 < baseStart_2755556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755618 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_2755618 : Nat := 118140960795 + 2755618 * 2 ^ 59
def prefixEnd_2755618 : Nat := 4983230072969 + 3 ^ 40 * 2755618 * 2
def baseEnd_2755618 : Nat := 943304356120869910401433

theorem tailTrace_2755618 : CollatzResearch.WordTrace tailWord_2755618 prefixEnd_2755618 943304356120869910401433 := by
  unfold tailWord_2755618
  simp only [CollatzResearch.WordTrace]
  refine ⟨25126411332718520732842877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67003763553916055287581005 25126411332718520732842877)
  ·
    refine ⟨9422404249769445274816079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25126411332718520732842877 9422404249769445274816079)
    ·
      refine ⟨14133606374654167912224119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9422404249769445274816079 14133606374654167912224119)
      ·
        refine ⟨21200409561981251868336179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14133606374654167912224119 21200409561981251868336179)
        ·
          refine ⟨31800614342971877802504269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21200409561981251868336179 31800614342971877802504269)
          ·
            refine ⟨11925230378614454175939101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31800614342971877802504269 11925230378614454175939101)
            ·
              refine ⟨4471961391980420315977163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11925230378614454175939101 4471961391980420315977163)
              ·
                refine ⟨6707942087970630473965745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4471961391980420315977163 6707942087970630473965745)
                ·
                  refine ⟨5030956565977972855474309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6707942087970630473965745 5030956565977972855474309)
                  ·
                    refine ⟨943304356120869910401433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5030956565977972855474309 943304356120869910401433)
                    ·
                      rfl

theorem cell22_2755618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_2755618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755618 prefixEnd_2755618 := by exact prefixLift 2755618
  have htrace : WordTrace (prefixWord ++ tailWord_2755618) baseStart_2755618 baseEnd_2755618 := by
    simpa [prefixWord, tailWord_2755618, baseEnd_2755618] using wordTrace_append hprefix tailTrace_2755618
  have hstable : (prefixWord ++ tailWord_2755618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755618).length < 2 ^ (prefixWord ++ tailWord_2755618).sum := by decide
  have hdescent : baseEnd_2755618 < baseStart_2755618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755648 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 3, 3]
def baseStart_2755648 : Nat := 118140960795 + 2755648 * 2 ^ 59
def prefixEnd_2755648 : Nat := 4983230072969 + 3 ^ 40 * 2755648 * 2
def baseEnd_2755648 : Nat := 943314625733959832151341

theorem tailTrace_2755648 : CollatzResearch.WordTrace tailWord_2755648 prefixEnd_2755648 943314625733959832151341 := by
  unfold tailWord_2755648
  simp only [CollatzResearch.WordTrace]
  refine ⟨50253369760382699027481799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67004493013843598703309065 50253369760382699027481799)
  ·
    refine ⟨75380054640574048541222699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50253369760382699027481799 75380054640574048541222699)
    ·
      refine ⟨113070081960861072811834049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75380054640574048541222699 113070081960861072811834049)
      ·
        refine ⟨84802561470645804608875537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113070081960861072811834049 84802561470645804608875537)
        ·
          refine ⟨63601921102984353456656653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84802561470645804608875537 63601921102984353456656653)
          ·
            refine ⟨23850720413619132546246245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63601921102984353456656653 23850720413619132546246245)
            ·
              refine ⟨4472010077553587352421171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23850720413619132546246245 4472010077553587352421171)
              ·
                refine ⟨6708015116330381028631757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4472010077553587352421171 6708015116330381028631757)
                ·
                  refine ⟨2515505668623892885736909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6708015116330381028631757 2515505668623892885736909)
                  ·
                    refine ⟨943314625733959832151341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2515505668623892885736909 943314625733959832151341)
                    ·
                      rfl

theorem cell22_2755648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 3, 3].length) (baseStart_2755648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755648 prefixEnd_2755648 := by exact prefixLift 2755648
  have htrace : WordTrace (prefixWord ++ tailWord_2755648) baseStart_2755648 baseEnd_2755648 := by
    simpa [prefixWord, tailWord_2755648, baseEnd_2755648] using wordTrace_append hprefix tailTrace_2755648
  have hstable : (prefixWord ++ tailWord_2755648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755648).length < 2 ^ (prefixWord ++ tailWord_2755648).sum := by decide
  have hdescent : baseEnd_2755648 < baseStart_2755648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755654 : List Nat := [6, 1, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_2755654 : Nat := 118140960795 + 2755654 * 2 ^ 59
def prefixEnd_2755654 : Nat := 4983230072969 + 3 ^ 40 * 2755654 * 2
def baseEnd_2755654 : Nat := 943316679656577816501323

theorem tailTrace_2755654 : CollatzResearch.WordTrace tailWord_2755654 prefixEnd_2755654 943316679656577816501323 := by
  unfold tailWord_2755654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3140842448710739408740063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67004638905829107386454677 3140842448710739408740063)
  ·
    refine ⟨4711263673066109113110095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3140842448710739408740063 4711263673066109113110095)
    ·
      refine ⟨7066895509599163669665143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4711263673066109113110095 7066895509599163669665143)
      ·
        refine ⟨10600343264398745504497715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7066895509599163669665143 10600343264398745504497715)
        ·
          refine ⟨15900514896598118256746573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10600343264398745504497715 15900514896598118256746573)
          ·
            refine ⟨5962693086224294346279965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15900514896598118256746573 5962693086224294346279965)
            ·
              refine ⟨2236009907334110379854987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5962693086224294346279965 2236009907334110379854987)
              ·
                refine ⟨3354014861001165569782481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236009907334110379854987 3354014861001165569782481)
                ·
                  refine ⟨2515511145750874177336861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3354014861001165569782481 2515511145750874177336861)
                  ·
                    refine ⟨943316679656577816501323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2515511145750874177336861 943316679656577816501323)
                    ·
                      rfl

theorem cell22_2755654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_2755654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755654 prefixEnd_2755654 := by exact prefixLift 2755654
  have htrace : WordTrace (prefixWord ++ tailWord_2755654) baseStart_2755654 baseEnd_2755654 := by
    simpa [prefixWord, tailWord_2755654, baseEnd_2755654] using wordTrace_append hprefix tailTrace_2755654
  have hstable : (prefixWord ++ tailWord_2755654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755654).length < 2 ^ (prefixWord ++ tailWord_2755654).sum := by decide
  have hdescent : baseEnd_2755654 < baseStart_2755654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755738 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 3, 5]
def baseStart_2755738 : Nat := 118140960795 + 2755738 * 2 ^ 59
def prefixEnd_2755738 : Nat := 4983230072969 + 3 ^ 40 * 2755738 * 2
def baseEnd_2755738 : Nat := 943345434573229597401065

theorem tailTrace_2755738 : CollatzResearch.WordTrace tailWord_2755738 prefixEnd_2755738 943345434573229597401065 := by
  unfold tailWord_2755738
  simp only [CollatzResearch.WordTrace]
  refine ⟨25127505522609835856434967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67006681393626228950493245 25127505522609835856434967)
  ·
    refine ⟨37691258283914753784652451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25127505522609835856434967 37691258283914753784652451)
    ·
      refine ⟨56536887425872130676978677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37691258283914753784652451 56536887425872130676978677)
      ·
        refine ⟨5300333196175512250966751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56536887425872130676978677 5300333196175512250966751)
        ·
          refine ⟨7950499794263268376450127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5300333196175512250966751 7950499794263268376450127)
          ·
            refine ⟨11925749691394902564675191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7950499794263268376450127 11925749691394902564675191)
            ·
              refine ⟨17888624537092353847012787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11925749691394902564675191 17888624537092353847012787)
              ·
                refine ⟨26832936805638530770519181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17888624537092353847012787 26832936805638530770519181)
                ·
                  refine ⟨10062351302114449038944693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26832936805638530770519181 10062351302114449038944693)
                  ·
                    refine ⟨943345434573229597401065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10062351302114449038944693 943345434573229597401065)
                    ·
                      rfl

theorem cell22_2755738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_2755738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755738 prefixEnd_2755738 := by exact prefixLift 2755738
  have htrace : WordTrace (prefixWord ++ tailWord_2755738) baseStart_2755738 baseEnd_2755738 := by
    simpa [prefixWord, tailWord_2755738, baseEnd_2755738] using wordTrace_append hprefix tailTrace_2755738
  have hstable : (prefixWord ++ tailWord_2755738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755738).length < 2 ^ (prefixWord ++ tailWord_2755738).sum := by decide
  have hdescent : baseEnd_2755738 < baseStart_2755738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755757 : List Nat := [1, 5, 2, 1, 3, 1, 1, 4, 4]
def baseStart_2755757 : Nat := 118140960795 + 2755757 * 2 ^ 59
def prefixEnd_2755757 : Nat := 4983230072969 + 3 ^ 40 * 2755757 * 2
def baseEnd_2755757 : Nat := 314450646220506627058669

theorem tailTrace_2755757 : CollatzResearch.WordTrace tailWord_2755757 prefixEnd_2755757 314450646220506627058669 := by
  unfold tailWord_2755757
  simp only [CollatzResearch.WordTrace]
  refine ⟨100510715077370509670681525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67007143384913673113787683 100510715077370509670681525)
  ·
    refine ⟨9422879538503485281626393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100510715077370509670681525 9422879538503485281626393)
    ·
      refine ⟨7067159653877613961219795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9422879538503485281626393 7067159653877613961219795)
      ·
        refine ⟨10600739480816420941829693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7067159653877613961219795 10600739480816420941829693)
        ·
          refine ⟨3975277305306157853186135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10600739480816420941829693 3975277305306157853186135)
          ·
            refine ⟨5962915957959236779779203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3975277305306157853186135 5962915957959236779779203)
            ·
              refine ⟨8944373936938855169668805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5962915957959236779779203 8944373936938855169668805)
              ·
                refine ⟨1677070113176035344312901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8944373936938855169668805 1677070113176035344312901)
                ·
                  refine ⟨314450646220506627058669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1677070113176035344312901 314450646220506627058669)
                  ·
                    rfl

theorem cell22_2755757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_2755757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755757 prefixEnd_2755757 := by exact prefixLift 2755757
  have htrace : WordTrace (prefixWord ++ tailWord_2755757) baseStart_2755757 baseEnd_2755757 := by
    simpa [prefixWord, tailWord_2755757, baseEnd_2755757] using wordTrace_append hprefix tailTrace_2755757
  have hstable : (prefixWord ++ tailWord_2755757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755757).length < 2 ^ (prefixWord ++ tailWord_2755757).sum := by decide
  have hdescent : baseEnd_2755757 < baseStart_2755757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755781 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_2755781 : Nat := 118140960795 + 2755781 * 2 ^ 59
def prefixEnd_2755781 : Nat := 4983230072969 + 3 ^ 40 * 2755781 * 2
def baseEnd_2755781 : Nat := 943360154351991818575933

theorem tailTrace_2755781 : CollatzResearch.WordTrace tailWord_2755781 prefixEnd_2755781 943360154351991818575933 := by
  unfold tailWord_2755781
  simp only [CollatzResearch.WordTrace]
  refine ⟨100511590429283561769555197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67007726952855707846370131 100511590429283561769555197)
  ·
    refine ⟨37691846410981335663583199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100511590429283561769555197 37691846410981335663583199)
    ·
      refine ⟨56537769616472003495374799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37691846410981335663583199 56537769616472003495374799)
      ·
        refine ⟨84806654424708005243062199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56537769616472003495374799 84806654424708005243062199)
        ·
          refine ⟨127209981637062007864593299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84806654424708005243062199 127209981637062007864593299)
          ·
            refine ⟨190814972455593011796889949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127209981637062007864593299 190814972455593011796889949)
            ·
              refine ⟨71555614670847379423833731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190814972455593011796889949 71555614670847379423833731)
              ·
                refine ⟨107333422006271069135750597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71555614670847379423833731 107333422006271069135750597)
                ·
                  refine ⟨20125016626175825462953237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107333422006271069135750597 20125016626175825462953237)
                  ·
                    refine ⟨943360154351991818575933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20125016626175825462953237 943360154351991818575933)
                    ·
                      rfl

theorem cell22_2755781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_2755781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755781 prefixEnd_2755781 := by exact prefixLift 2755781
  have htrace : WordTrace (prefixWord ++ tailWord_2755781) baseStart_2755781 baseEnd_2755781 := by
    simpa [prefixWord, tailWord_2755781, baseEnd_2755781] using wordTrace_append hprefix tailTrace_2755781
  have hstable : (prefixWord ++ tailWord_2755781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755781).length < 2 ^ (prefixWord ++ tailWord_2755781).sum := by decide
  have hdescent : baseEnd_2755781 < baseStart_2755781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755875 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 6]
def baseStart_2755875 : Nat := 118140960795 + 2755875 * 2 ^ 59
def prefixEnd_2755875 : Nat := 4983230072969 + 3 ^ 40 * 2755875 * 2
def baseEnd_2755875 : Nat := 314464110824335635575215

theorem tailTrace_2755875 : CollatzResearch.WordTrace tailWord_2755875 prefixEnd_2755875 314464110824335635575215 := by
  unfold tailWord_2755875
  simp only [CollatzResearch.WordTrace]
  refine ⟨100515018890943015823477079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67010012593962010548984719 100515018890943015823477079)
  ·
    refine ⟨150772528336414523735215619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100515018890943015823477079 150772528336414523735215619)
    ·
      refine ⟨226158792504621785602823429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150772528336414523735215619 226158792504621785602823429)
      ·
        refine ⟨42404773594616584800529393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226158792504621785602823429 42404773594616584800529393)
        ·
          refine ⟨31803580195962438600397045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42404773594616584800529393 31803580195962438600397045)
          ·
            refine ⟨2981585643371478618787223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31803580195962438600397045 2981585643371478618787223)
            ·
              refine ⟨4472378465057217928180835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2981585643371478618787223 4472378465057217928180835)
              ·
                refine ⟨6708567697585826892271253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4472378465057217928180835 6708567697585826892271253)
                ·
                  refine ⟨314464110824335635575215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6708567697585826892271253 314464110824335635575215)
                  ·
                    rfl

theorem cell22_2755875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 6].length) (baseStart_2755875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755875 prefixEnd_2755875 := by exact prefixLift 2755875
  have htrace : WordTrace (prefixWord ++ tailWord_2755875) baseStart_2755875 baseEnd_2755875 := by
    simpa [prefixWord, tailWord_2755875, baseEnd_2755875] using wordTrace_append hprefix tailTrace_2755875
  have hstable : (prefixWord ++ tailWord_2755875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755875).length < 2 ^ (prefixWord ++ tailWord_2755875).sum := by decide
  have hdescent : baseEnd_2755875 < baseStart_2755875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755888 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 4, 4]
def baseStart_2755888 : Nat := 118140960795 + 2755888 * 2 ^ 59
def prefixEnd_2755888 : Nat := 4983230072969 + 3 ^ 40 * 2755888 * 2
def baseEnd_2755888 : Nat := 943396782638679206150605

theorem tailTrace_2755888 : CollatzResearch.WordTrace tailWord_2755888 prefixEnd_2755888 943396782638679206150605 := by
  unfold tailWord_2755888
  simp only [CollatzResearch.WordTrace]
  refine ⟨50257746519947959521850159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67010328693263946029133545 50257746519947959521850159)
  ·
    refine ⟨75386619779921939282775239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50257746519947959521850159 75386619779921939282775239)
    ·
      refine ⟨113079929669882908924162859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75386619779921939282775239 113079929669882908924162859)
      ·
        refine ⟨169619894504824363386244289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113079929669882908924162859 169619894504824363386244289)
        ·
          refine ⟨127214920878618272539683217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169619894504824363386244289 127214920878618272539683217)
          ·
            refine ⟨95411190658963704404762413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127214920878618272539683217 95411190658963704404762413)
            ·
              refine ⟨35779196497111389151785905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95411190658963704404762413 35779196497111389151785905)
              ·
                refine ⟨26834397372833541863839429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35779196497111389151785905 26834397372833541863839429)
                ·
                  refine ⟨5031449507406289099469893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26834397372833541863839429 5031449507406289099469893)
                  ·
                    refine ⟨943396782638679206150605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5031449507406289099469893 943396782638679206150605)
                    ·
                      rfl

theorem cell22_2755888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_2755888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755888 prefixEnd_2755888 := by exact prefixLift 2755888
  have htrace : WordTrace (prefixWord ++ tailWord_2755888) baseStart_2755888 baseEnd_2755888 := by
    simpa [prefixWord, tailWord_2755888, baseEnd_2755888] using wordTrace_append hprefix tailTrace_2755888
  have hstable : (prefixWord ++ tailWord_2755888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755888).length < 2 ^ (prefixWord ++ tailWord_2755888).sum := by decide
  have hdescent : baseEnd_2755888 < baseStart_2755888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755894 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_2755894 : Nat := 118140960795 + 2755894 * 2 ^ 59
def prefixEnd_2755894 : Nat := 4983230072969 + 3 ^ 40 * 2755894 * 2
def baseEnd_2755894 : Nat := 943398836561297190500587

theorem tailTrace_2755894 : CollatzResearch.WordTrace tailWord_2755894 prefixEnd_2755894 943398836561297190500587 := by
  unfold tailWord_2755894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6282231992367136379276171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67010474585249454712279157 6282231992367136379276171)
  ·
    refine ⟨9423347988550704568914257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6282231992367136379276171 9423347988550704568914257)
    ·
      refine ⟨7067510991413028426685693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9423347988550704568914257 7067510991413028426685693)
      ·
        refine ⟨2650316621779885660007135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7067510991413028426685693 2650316621779885660007135)
        ·
          refine ⟨3975474932669828490010703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2650316621779885660007135 3975474932669828490010703)
          ·
            refine ⟨5963212399004742735016055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3975474932669828490010703 5963212399004742735016055)
            ·
              refine ⟨8944818598507114102524083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5963212399004742735016055 8944818598507114102524083)
              ·
                refine ⟨13417227897760671153786125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8944818598507114102524083 13417227897760671153786125)
                ·
                  refine ⟨5031460461660251682669797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13417227897760671153786125 5031460461660251682669797)
                  ·
                    refine ⟨943398836561297190500587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5031460461660251682669797 943398836561297190500587)
                    ·
                      rfl

theorem cell22_2755894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_2755894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755894 prefixEnd_2755894 := by exact prefixLift 2755894
  have htrace : WordTrace (prefixWord ++ tailWord_2755894) baseStart_2755894 baseEnd_2755894 := by
    simpa [prefixWord, tailWord_2755894, baseEnd_2755894] using wordTrace_append hprefix tailTrace_2755894
  have hstable : (prefixWord ++ tailWord_2755894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755894).length < 2 ^ (prefixWord ++ tailWord_2755894).sum := by decide
  have hdescent : baseEnd_2755894 < baseStart_2755894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755903 : List Nat := [1, 1, 2, 2, 4, 2, 2, 8]
def baseStart_2755903 : Nat := 118140960795 + 2755903 * 2 ^ 59
def prefixEnd_2755903 : Nat := 4983230072969 + 3 ^ 40 * 2755903 * 2
def baseEnd_2755903 : Nat := 104822435271691574113951

theorem tailTrace_2755903 : CollatzResearch.WordTrace tailWord_2755903 prefixEnd_2755903 104822435271691574113951 := by
  unfold tailWord_2755903
  simp only [CollatzResearch.WordTrace]
  refine ⟨100516040134841576605496363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67010693423227717736997575 100516040134841576605496363)
  ·
    refine ⟨150774060202262364908244545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100516040134841576605496363 150774060202262364908244545)
    ·
      refine ⟨113080545151696773681183409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150774060202262364908244545 113080545151696773681183409)
      ·
        refine ⟨84810408863772580260887557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113080545151696773681183409 84810408863772580260887557)
        ·
          refine ⟨15901951661957358798916417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84810408863772580260887557 15901951661957358798916417)
          ·
            refine ⟨11926463746468019099187313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15901951661957358798916417 11926463746468019099187313)
            ·
              refine ⟨8944847809851014324390485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11926463746468019099187313 8944847809851014324390485)
              ·
                refine ⟨104822435271691574113951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8944847809851014324390485 104822435271691574113951)
                ·
                  rfl

theorem cell22_2755903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 8].length) (baseStart_2755903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755903 prefixEnd_2755903 := by exact prefixLift 2755903
  have htrace : WordTrace (prefixWord ++ tailWord_2755903) baseStart_2755903 baseEnd_2755903 := by
    simpa [prefixWord, tailWord_2755903, baseEnd_2755903] using wordTrace_append hprefix tailTrace_2755903
  have hstable : (prefixWord ++ tailWord_2755903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755903).length < 2 ^ (prefixWord ++ tailWord_2755903).sum := by decide
  have hdescent : baseEnd_2755903 < baseStart_2755903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755935 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 3, 3]
def baseStart_2755935 : Nat := 118140960795 + 2755935 * 2 ^ 59
def prefixEnd_2755935 : Nat := 4983230072969 + 3 ^ 40 * 2755935 * 2
def baseEnd_2755935 : Nat := 943412871699186750225461

theorem tailTrace_2755935 : CollatzResearch.WordTrace tailWord_2755935 prefixEnd_2755935 943412871699186750225461 := by
  unfold tailWord_2755935
  simp only [CollatzResearch.WordTrace]
  refine ⟨100517207270725646070661259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67011471513817097380440839 100517207270725646070661259)
  ·
    refine ⟨150775810906088469105991889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100517207270725646070661259 150775810906088469105991889)
    ·
      refine ⟨113081858179566351829493917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150775810906088469105991889 113081858179566351829493917)
      ·
        refine ⟨42405696817337381936060219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113081858179566351829493917 42405696817337381936060219)
        ·
          refine ⟨63608545226006072904090329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42405696817337381936060219 63608545226006072904090329)
          ·
            refine ⟨47706408919504554678067747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63608545226006072904090329 47706408919504554678067747)
            ·
              refine ⟨71559613379256832017101621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47706408919504554678067747 71559613379256832017101621)
              ·
                refine ⟨6708713754305328001603277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71559613379256832017101621 6708713754305328001603277)
                ·
                  refine ⟨2515767657864498000601229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6708713754305328001603277 2515767657864498000601229)
                  ·
                    refine ⟨943412871699186750225461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2515767657864498000601229 943412871699186750225461)
                    ·
                      rfl

theorem cell22_2755935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 3].length) (baseStart_2755935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755935 prefixEnd_2755935 := by exact prefixLift 2755935
  have htrace : WordTrace (prefixWord ++ tailWord_2755935) baseStart_2755935 baseEnd_2755935 := by
    simpa [prefixWord, tailWord_2755935, baseEnd_2755935] using wordTrace_append hprefix tailTrace_2755935
  have hstable : (prefixWord ++ tailWord_2755935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755935).length < 2 ^ (prefixWord ++ tailWord_2755935).sum := by decide
  have hdescent : baseEnd_2755935 < baseStart_2755935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755963 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 1, 7]
def baseStart_2755963 : Nat := 118140960795 + 2755963 * 2 ^ 59
def prefixEnd_2755963 : Nat := 4983230072969 + 3 ^ 40 * 2755963 * 2
def baseEnd_2755963 : Nat := 943422456671404010525375

theorem tailTrace_2755963 : CollatzResearch.WordTrace tailWord_2755963 prefixEnd_2755963 943422456671404010525375 := by
  unfold tailWord_2755963
  simp only [CollatzResearch.WordTrace]
  refine ⟨100518228514624206852680543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67012152343082804568453695 100518228514624206852680543)
  ·
    refine ⟨150777342771936310279020815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100518228514624206852680543 150777342771936310279020815)
    ·
      refine ⟨226166014157904465418531223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150777342771936310279020815 226166014157904465418531223)
      ·
        refine ⟨339249021236856698127796835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226166014157904465418531223 339249021236856698127796835)
        ·
          refine ⟨508873531855285047191695253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339249021236856698127796835 508873531855285047191695253)
          ·
            refine ⟨23853446805716486587110715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 508873531855285047191695253 23853446805716486587110715)
            ·
              refine ⟨35780170208574729880666073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23853446805716486587110715 35780170208574729880666073)
              ·
                refine ⟨26835127656431047410499555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35780170208574729880666073 26835127656431047410499555)
                ·
                  refine ⟨40252691484646571115749333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26835127656431047410499555 40252691484646571115749333)
                  ·
                    refine ⟨943422456671404010525375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40252691484646571115749333 943422456671404010525375)
                    ·
                      rfl

theorem cell22_2755963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 7].length) (baseStart_2755963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755963 prefixEnd_2755963 := by exact prefixLift 2755963
  have htrace : WordTrace (prefixWord ++ tailWord_2755963) baseStart_2755963 baseEnd_2755963 := by
    simpa [prefixWord, tailWord_2755963, baseEnd_2755963] using wordTrace_append hprefix tailTrace_2755963
  have hstable : (prefixWord ++ tailWord_2755963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755963).length < 2 ^ (prefixWord ++ tailWord_2755963).sum := by decide
  have hdescent : baseEnd_2755963 < baseStart_2755963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755982 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_2755982 : Nat := 118140960795 + 2755982 * 2 ^ 59
def prefixEnd_2755982 : Nat := 4983230072969 + 3 ^ 40 * 2755982 * 2
def baseEnd_2755982 : Nat := 314476320253231431433439

theorem tailTrace_2755982 : CollatzResearch.WordTrace tailWord_2755982 prefixEnd_2755982 314476320253231431433439 := by
  unfold tailWord_2755982
  simp only [CollatzResearch.WordTrace]
  refine ⟨12564865187694421637202775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67012614334370248731748133 12564865187694421637202775)
  ·
    refine ⟨18847297781541632455804163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12564865187694421637202775 18847297781541632455804163)
    ·
      refine ⟨28270946672312448683706245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18847297781541632455804163 28270946672312448683706245)
      ·
        refine ⟨5300802501058584128194921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28270946672312448683706245 5300802501058584128194921)
        ·
          refine ⟨3975601875793938096146191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5300802501058584128194921 3975601875793938096146191)
          ·
            refine ⟨5963402813690907144219287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3975601875793938096146191 5963402813690907144219287)
            ·
              refine ⟨8945104220536360716328931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5963402813690907144219287 8945104220536360716328931)
              ·
                refine ⟨13417656330804541074493397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8945104220536360716328931 13417656330804541074493397)
                ·
                  refine ⟨314476320253231431433439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13417656330804541074493397 314476320253231431433439)
                  ·
                    rfl

theorem cell22_2755982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_2755982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755982 prefixEnd_2755982 := by exact prefixLift 2755982
  have htrace : WordTrace (prefixWord ++ tailWord_2755982) baseStart_2755982 baseEnd_2755982 := by
    simpa [prefixWord, tailWord_2755982, baseEnd_2755982] using wordTrace_append hprefix tailTrace_2755982
  have hstable : (prefixWord ++ tailWord_2755982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755982).length < 2 ^ (prefixWord ++ tailWord_2755982).sum := by decide
  have hdescent : baseEnd_2755982 < baseStart_2755982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2755986 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 3, 3]
def baseStart_2755986 : Nat := 118140960795 + 2755986 * 2 ^ 59
def prefixEnd_2755986 : Nat := 4983230072969 + 3 ^ 40 * 2755986 * 2
def baseEnd_2755986 : Nat := 943430330041439617200305

theorem tailTrace_2755986 : CollatzResearch.WordTrace tailWord_2755986 prefixEnd_2755986 943430330041439617200305 := by
  unfold tailWord_2755986
  simp only [CollatzResearch.WordTrace]
  refine ⟨25129766848385220445191953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67012711595693921187178541 25129766848385220445191953)
  ·
    refine ⟨18847325136288915333893965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25129766848385220445191953 18847325136288915333893965)
    ·
      refine ⟨7067746926108343250210237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18847325136288915333893965 7067746926108343250210237)
      ·
        refine ⟨2650405097290628718828839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7067746926108343250210237 2650405097290628718828839)
        ·
          refine ⟨3975607645935943078243259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2650405097290628718828839 3975607645935943078243259)
          ·
            refine ⟨5963411468903914617364889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3975607645935943078243259 5963411468903914617364889)
            ·
              refine ⟨4472558601677935963023667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5963411468903914617364889 4472558601677935963023667)
              ·
                refine ⟨6708837902516903944535501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4472558601677935963023667 6708837902516903944535501)
                ·
                  refine ⟨2515814213443838979200813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6708837902516903944535501 2515814213443838979200813)
                  ·
                    refine ⟨943430330041439617200305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2515814213443838979200813 943430330041439617200305)
                    ·
                      rfl

theorem cell22_2755986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_2755986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2755986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2755986 prefixEnd_2755986 := by exact prefixLift 2755986
  have htrace : WordTrace (prefixWord ++ tailWord_2755986) baseStart_2755986 baseEnd_2755986 := by
    simpa [prefixWord, tailWord_2755986, baseEnd_2755986] using wordTrace_append hprefix tailTrace_2755986
  have hstable : (prefixWord ++ tailWord_2755986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2755986).length < 2 ^ (prefixWord ++ tailWord_2755986).sum := by decide
  have hdescent : baseEnd_2755986 < baseStart_2755986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2755986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756042 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 4, 3]
def baseStart_2756042 : Nat := 118140960795 + 2756042 * 2 ^ 59
def prefixEnd_2756042 : Nat := 4983230072969 + 3 ^ 40 * 2756042 * 2
def baseEnd_2756042 : Nat := 943449499985874137800133

theorem tailTrace_2756042 : CollatzResearch.WordTrace tailWord_2756042 prefixEnd_2756042 943449499985874137800133 := by
  unfold tailWord_2756042
  simp only [CollatzResearch.WordTrace]
  refine ⟨25130277470334500836201595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67014073254225335563204253 25130277470334500836201595)
  ·
    refine ⟨37695416205501751254302393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25130277470334500836201595 37695416205501751254302393)
    ·
      refine ⟨28271562154126313440726795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37695416205501751254302393 28271562154126313440726795)
      ·
        refine ⟨42407343231189470161090193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28271562154126313440726795 42407343231189470161090193)
        ·
          refine ⟨31805507423392102620817645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42407343231189470161090193 31805507423392102620817645)
          ·
            refine ⟨11927065283772038482806617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31805507423392102620817645 11927065283772038482806617)
            ·
              refine ⟨8945298962829028862104963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11927065283772038482806617 8945298962829028862104963)
              ·
                refine ⟨13417948444243543293157445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8945298962829028862104963 13417948444243543293157445)
                ·
                  refine ⟨2515865333295664367467021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13417948444243543293157445 2515865333295664367467021)
                  ·
                    refine ⟨943449499985874137800133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2515865333295664367467021 943449499985874137800133)
                    ·
                      rfl

theorem cell22_2756042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_2756042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756042 prefixEnd_2756042 := by exact prefixLift 2756042
  have htrace : WordTrace (prefixWord ++ tailWord_2756042) baseStart_2756042 baseEnd_2756042 := by
    simpa [prefixWord, tailWord_2756042, baseEnd_2756042] using wordTrace_append hprefix tailTrace_2756042
  have hstable : (prefixWord ++ tailWord_2756042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756042).length < 2 ^ (prefixWord ++ tailWord_2756042).sum := by decide
  have hdescent : baseEnd_2756042 < baseStart_2756042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756074 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 2, 4]
def baseStart_2756074 : Nat := 118140960795 + 2756074 * 2 ^ 59
def prefixEnd_2756074 : Nat := 4983230072969 + 3 ^ 40 * 2756074 * 2
def baseEnd_2756074 : Nat := 943460454239836721000035

theorem tailTrace_2756074 : CollatzResearch.WordTrace tailWord_2756074 prefixEnd_2756074 943460454239836721000035 := by
  unfold tailWord_2756074
  simp only [CollatzResearch.WordTrace]
  refine ⟨25130569254305518202492819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67014851344814715206647517 25130569254305518202492819)
  ·
    refine ⟨37695853881458277303739229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25130569254305518202492819 37695853881458277303739229)
    ·
      refine ⟨14135945205546853988902211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37695853881458277303739229 14135945205546853988902211)
      ·
        refine ⟨21203917808320280983353317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14135945205546853988902211 21203917808320280983353317)
        ·
          refine ⟨3975734589060052684378747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21203917808320280983353317 3975734589060052684378747)
          ·
            refine ⟨5963601883590079026568121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3975734589060052684378747 5963601883590079026568121)
            ·
              refine ⟨4472701412692559269926091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5963601883590079026568121 4472701412692559269926091)
              ·
                refine ⟨6709052119038838904889137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4472701412692559269926091 6709052119038838904889137)
                ·
                  refine ⟨5031789089279129178666853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6709052119038838904889137 5031789089279129178666853)
                  ·
                    refine ⟨943460454239836721000035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5031789089279129178666853 943460454239836721000035)
                    ·
                      rfl

theorem cell22_2756074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_2756074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756074 prefixEnd_2756074 := by exact prefixLift 2756074
  have htrace : WordTrace (prefixWord ++ tailWord_2756074) baseStart_2756074 baseEnd_2756074 := by
    simpa [prefixWord, tailWord_2756074, baseEnd_2756074] using wordTrace_append hprefix tailTrace_2756074
  have hstable : (prefixWord ++ tailWord_2756074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756074).length < 2 ^ (prefixWord ++ tailWord_2756074).sum := by decide
  have hdescent : baseEnd_2756074 < baseStart_2756074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756115 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 1, 7]
def baseStart_2756115 : Nat := 118140960795 + 2756115 * 2 ^ 59
def prefixEnd_2756115 : Nat := 4983230072969 + 3 ^ 40 * 2756115 * 2
def baseEnd_2756115 : Nat := 943474489377726280724909

theorem tailTrace_2756115 : CollatzResearch.WordTrace tailWord_2756115 prefixEnd_2756115 943474489377726280724909 := by
  unfold tailWord_2756115
  simp only [CollatzResearch.WordTrace]
  refine ⟨100523772410073536812213799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67015848273382357874809199 100523772410073536812213799)
  ·
    refine ⟨150785658615110305218320699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100523772410073536812213799 150785658615110305218320699)
    ·
      refine ⟨226178487922665457827481049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150785658615110305218320699 226178487922665457827481049)
      ·
        refine ⟨169633865941999093370610787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226178487922665457827481049 169633865941999093370610787)
        ·
          refine ⟨254450798912998640055916181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169633865941999093370610787 254450798912998640055916181)
          ·
            refine ⟨11927381199046811252621071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 254450798912998640055916181 11927381199046811252621071)
            ·
              refine ⟨17891071798570216878931607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11927381199046811252621071 17891071798570216878931607)
              ·
                refine ⟨26836607697855325318397411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17891071798570216878931607 26836607697855325318397411)
                ·
                  refine ⟨40254911546782987977596117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26836607697855325318397411 40254911546782987977596117)
                  ·
                    refine ⟨943474489377726280724909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40254911546782987977596117 943474489377726280724909)
                    ·
                      rfl

theorem cell22_2756115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 7].length) (baseStart_2756115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756115 prefixEnd_2756115 := by exact prefixLift 2756115
  have htrace : WordTrace (prefixWord ++ tailWord_2756115) baseStart_2756115 baseEnd_2756115 := by
    simpa [prefixWord, tailWord_2756115, baseEnd_2756115] using wordTrace_append hprefix tailTrace_2756115
  have hstable : (prefixWord ++ tailWord_2756115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756115).length < 2 ^ (prefixWord ++ tailWord_2756115).sum := by decide
  have hdescent : baseEnd_2756115 < baseStart_2756115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756117 : List Nat := [1, 3, 2, 1, 3, 2, 2, 3, 5]
def baseStart_2756117 : Nat := 118140960795 + 2756117 * 2 ^ 59
def prefixEnd_2756117 : Nat := 4983230072969 + 3 ^ 40 * 2756117 * 2
def baseEnd_2756117 : Nat := 314491724672866314058301

theorem tailTrace_2756117 : CollatzResearch.WordTrace tailWord_2756117 prefixEnd_2756117 314491724672866314058301 := by
  unfold tailWord_2756117
  simp only [CollatzResearch.WordTrace]
  refine ⟨100523845356066291153786605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67015896904044194102524403 100523845356066291153786605)
  ·
    refine ⟨37696442008524859182669977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100523845356066291153786605 37696442008524859182669977)
    ·
      refine ⟨28272331506393644387002483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37696442008524859182669977 28272331506393644387002483)
      ·
        refine ⟨42408497259590466580503725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28272331506393644387002483 42408497259590466580503725)
        ·
          refine ⟨15903186472346424967688897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42408497259590466580503725 15903186472346424967688897)
          ·
            refine ⟨11927389854259818725766673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15903186472346424967688897 11927389854259818725766673)
            ·
              refine ⟨8945542390694864044325005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11927389854259818725766673 8945542390694864044325005)
              ·
                refine ⟨3354578396510574016621877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8945542390694864044325005 3354578396510574016621877)
                ·
                  refine ⟨314491724672866314058301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3354578396510574016621877 314491724672866314058301)
                  ·
                    rfl

theorem cell22_2756117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_2756117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756117 prefixEnd_2756117 := by exact prefixLift 2756117
  have htrace : WordTrace (prefixWord ++ tailWord_2756117) baseStart_2756117 baseEnd_2756117 := by
    simpa [prefixWord, tailWord_2756117, baseEnd_2756117] using wordTrace_append hprefix tailTrace_2756117
  have hstable : (prefixWord ++ tailWord_2756117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756117).length < 2 ^ (prefixWord ++ tailWord_2756117).sum := by decide
  have hdescent : baseEnd_2756117 < baseStart_2756117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756145 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 10]
def baseStart_2756145 : Nat := 118140960795 + 2756145 * 2 ^ 59
def prefixEnd_2756145 : Nat := 4983230072969 + 3 ^ 40 * 2756145 * 2
def baseEnd_2756145 : Nat := 314494919663605400824939

theorem tailTrace_2756145 : CollatzResearch.WordTrace tailWord_2756145 prefixEnd_2756145 314494919663605400824939 := by
  unfold tailWord_2756145
  simp only [CollatzResearch.WordTrace]
  refine ⟨100524866599964851935805889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67016577733309901290537259 100524866599964851935805889)
  ·
    refine ⟨75393649949973638951854417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100524866599964851935805889 75393649949973638951854417)
    ·
      refine ⟨56545237462480229213890813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75393649949973638951854417 56545237462480229213890813)
      ·
        refine ⟨21204464048430085955209055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56545237462480229213890813 21204464048430085955209055)
        ·
          refine ⟨31806696072645128932813583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21204464048430085955209055 31806696072645128932813583)
          ·
            refine ⟨47710044108967693399220375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31806696072645128932813583 47710044108967693399220375)
            ·
              refine ⟨71565066163451540098830563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47710044108967693399220375 71565066163451540098830563)
              ·
                refine ⟨107347599245177310148245845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71565066163451540098830563 107347599245177310148245845)
                ·
                  refine ⟨314494919663605400824939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 107347599245177310148245845 314494919663605400824939)
                  ·
                    rfl

theorem cell22_2756145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 10].length) (baseStart_2756145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756145 prefixEnd_2756145 := by exact prefixLift 2756145
  have htrace : WordTrace (prefixWord ++ tailWord_2756145) baseStart_2756145 baseEnd_2756145 := by
    simpa [prefixWord, tailWord_2756145, baseEnd_2756145] using wordTrace_append hprefix tailTrace_2756145
  have hstable : (prefixWord ++ tailWord_2756145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756145).length < 2 ^ (prefixWord ++ tailWord_2756145).sum := by decide
  have hdescent : baseEnd_2756145 < baseStart_2756145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756192 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 2, 4]
def baseStart_2756192 : Nat := 118140960795 + 2756192 * 2 ^ 59
def prefixEnd_2756192 : Nat := 4983230072969 + 3 ^ 40 * 2756192 * 2
def baseEnd_2756192 : Nat := 943500848051323746549673

theorem tailTrace_2756192 : CollatzResearch.WordTrace tailWord_2756192 prefixEnd_2756192 943500848051323746549673 := by
  unfold tailWord_2756192
  simp only [CollatzResearch.WordTrace]
  refine ⟨50263290415397289481383415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67017720553863052641844553 50263290415397289481383415)
  ·
    refine ⟨75394935623095934222075123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50263290415397289481383415 75394935623095934222075123)
    ·
      refine ⟨113092403434643901333112685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75394935623095934222075123 113092403434643901333112685)
      ·
        refine ⟨42409651287991462999917257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113092403434643901333112685 42409651287991462999917257)
        ·
          refine ⟨31807238465993597249937943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42409651287991462999917257 31807238465993597249937943)
          ·
            refine ⟨47710857698990395874906915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31807238465993597249937943 47710857698990395874906915)
            ·
              refine ⟨71566286548485593812360373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47710857698990395874906915 71566286548485593812360373)
              ·
                refine ⟨6709339363920524419908785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71566286548485593812360373 6709339363920524419908785)
                ·
                  refine ⟨5032004522940393314931589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6709339363920524419908785 5032004522940393314931589)
                  ·
                    refine ⟨943500848051323746549673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5032004522940393314931589 943500848051323746549673)
                    ·
                      rfl

theorem cell22_2756192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_2756192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756192 prefixEnd_2756192 := by exact prefixLift 2756192
  have htrace : WordTrace (prefixWord ++ tailWord_2756192) baseStart_2756192 baseEnd_2756192 := by
    simpa [prefixWord, tailWord_2756192, baseEnd_2756192] using wordTrace_append hprefix tailTrace_2756192
  have hstable : (prefixWord ++ tailWord_2756192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756192).length < 2 ^ (prefixWord ++ tailWord_2756192).sum := by decide
  have hdescent : baseEnd_2756192 < baseStart_2756192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756196 : List Nat := [2, 3, 1, 1, 2, 5, 1, 3, 4]
def baseStart_2756196 : Nat := 118140960795 + 2756196 * 2 ^ 59
def prefixEnd_2756196 : Nat := 4983230072969 + 3 ^ 40 * 2756196 * 2
def baseEnd_2756196 : Nat := 314500739111023023149887

theorem tailTrace_2756196 : CollatzResearch.WordTrace tailWord_2756196 prefixEnd_2756196 314500739111023023149887 := by
  unfold tailWord_2756196
  simp only [CollatzResearch.WordTrace]
  refine ⟨50263363361390043822956221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67017817815186725097274961 50263363361390043822956221)
  ·
    refine ⟨18848761260521266433608583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50263363361390043822956221 18848761260521266433608583)
    ·
      refine ⟨28273141890781899650412875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18848761260521266433608583 28273141890781899650412875)
      ·
        refine ⟨42409712836172849475619313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28273141890781899650412875 42409712836172849475619313)
        ·
          refine ⟨31807284627129637106714485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42409712836172849475619313 31807284627129637106714485)
          ·
            refine ⟨2981932933793403478754483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31807284627129637106714485 2981932933793403478754483)
            ·
              refine ⟨4472899400690105218131725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2981932933793403478754483 4472899400690105218131725)
              ·
                refine ⟨1677337275258789456799397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4472899400690105218131725 1677337275258789456799397)
                ·
                  refine ⟨314500739111023023149887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1677337275258789456799397 314500739111023023149887)
                  ·
                    rfl

theorem cell22_2756196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_2756196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756196 prefixEnd_2756196 := by exact prefixLift 2756196
  have htrace : WordTrace (prefixWord ++ tailWord_2756196) baseStart_2756196 baseEnd_2756196 := by
    simpa [prefixWord, tailWord_2756196, baseEnd_2756196] using wordTrace_append hprefix tailTrace_2756196
  have hstable : (prefixWord ++ tailWord_2756196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756196).length < 2 ^ (prefixWord ++ tailWord_2756196).sum := by decide
  have hdescent : baseEnd_2756196 < baseStart_2756196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756213 : List Nat := [1, 3, 4, 2, 1, 2, 3, 2, 4]
def baseStart_2756213 : Nat := 118140960795 + 2756213 * 2 ^ 59
def prefixEnd_2756213 : Nat := 4983230072969 + 3 ^ 40 * 2756213 * 2
def baseEnd_2756213 : Nat := 314502678926828897258203

theorem tailTrace_2756213 : CollatzResearch.WordTrace tailWord_2756213 prefixEnd_2756213 314502678926828897258203 := by
  unfold tailWord_2756213
  simp only [CollatzResearch.WordTrace]
  refine ⟨100527346763718499549281293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67018231175812333032854195 100527346763718499549281293)
  ·
    refine ⟨37697755036394437330980485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100527346763718499549281293 37697755036394437330980485)
    ·
      refine ⟨7068329069323956999558841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37697755036394437330980485 7068329069323956999558841)
      ·
        refine ⟨5301246801992967749669131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7068329069323956999558841 5301246801992967749669131)
        ·
          refine ⟨7951870202989451624503697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5301246801992967749669131 7951870202989451624503697)
          ·
            refine ⟨5963902652242088718377773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7951870202989451624503697 5963902652242088718377773)
            ·
              refine ⟨2236463494590783269391665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5963902652242088718377773 2236463494590783269391665)
              ·
                refine ⟨1677347620943087452043749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2236463494590783269391665 1677347620943087452043749)
                ·
                  refine ⟨314502678926828897258203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1677347620943087452043749 314502678926828897258203)
                  ·
                    rfl

theorem cell22_2756213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_2756213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756213 prefixEnd_2756213 := by exact prefixLift 2756213
  have htrace : WordTrace (prefixWord ++ tailWord_2756213) baseStart_2756213 baseEnd_2756213 := by
    simpa [prefixWord, tailWord_2756213, baseEnd_2756213] using wordTrace_append hprefix tailTrace_2756213
  have hstable : (prefixWord ++ tailWord_2756213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756213).length < 2 ^ (prefixWord ++ tailWord_2756213).sum := by decide
  have hdescent : baseEnd_2756213 < baseStart_2756213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756264 : List Nat := [2, 1, 7, 1, 2, 1, 2, 2, 4]
def baseStart_2756264 : Nat := 118140960795 + 2756264 * 2 ^ 59
def prefixEnd_2756264 : Nat := 4983230072969 + 3 ^ 40 * 2756264 * 2
def baseEnd_2756264 : Nat := 314508498374246519583151

theorem tailTrace_2756264 : CollatzResearch.WordTrace tailWord_2756264 prefixEnd_2756264 314508498374246519583151 := by
  unfold tailWord_2756264
  simp only [CollatzResearch.WordTrace]
  refine ⟨50264603443266867629693923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67019471257689156839591897 50264603443266867629693923)
  ·
    refine ⟨75396905164900301444540885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50264603443266867629693923 75396905164900301444540885)
    ·
      refine ⟨1767114964802350815106427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 75396905164900301444540885 1767114964802350815106427)
      ·
        refine ⟨2650672447203526222659641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767114964802350815106427 2650672447203526222659641)
        ·
          refine ⟨1988004335402644666994731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2650672447203526222659641 1988004335402644666994731)
          ·
            refine ⟨2982006503103967000492097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988004335402644666994731 2982006503103967000492097)
            ·
              refine ⟨2236504877327975250369073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2982006503103967000492097 2236504877327975250369073)
              ·
                refine ⟨1677378657995981437776805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2236504877327975250369073 1677378657995981437776805)
                ·
                  refine ⟨314508498374246519583151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1677378657995981437776805 314508498374246519583151)
                  ·
                    rfl

theorem cell22_2756264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 4].length) (baseStart_2756264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756264 prefixEnd_2756264 := by exact prefixLift 2756264
  have htrace : WordTrace (prefixWord ++ tailWord_2756264) baseStart_2756264 baseEnd_2756264 := by
    simpa [prefixWord, tailWord_2756264, baseEnd_2756264] using wordTrace_append hprefix tailTrace_2756264
  have hstable : (prefixWord ++ tailWord_2756264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756264).length < 2 ^ (prefixWord ++ tailWord_2756264).sum := by decide
  have hdescent : baseEnd_2756264 < baseStart_2756264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756284 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 2, 5]
def baseStart_2756284 : Nat := 118140960795 + 2756284 * 2 ^ 59
def prefixEnd_2756284 : Nat := 4983230072969 + 3 ^ 40 * 2756284 * 2
def baseEnd_2756284 : Nat := 943532341531466173249391

theorem tailTrace_2756284 : CollatzResearch.WordTrace tailWord_2756284 prefixEnd_2756284 943532341531466173249391 := by
  unfold tailWord_2756284
  simp only [CollatzResearch.WordTrace]
  refine ⟨50264968173230639337557953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67019957564307519116743937 50264968173230639337557953)
  ·
    refine ⟨37698726129922979503168465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50264968173230639337557953 37698726129922979503168465)
    ·
      refine ⟨28274044597442234627376349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37698726129922979503168465 28274044597442234627376349)
      ·
        refine ⟨10602766724040837985266131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28274044597442234627376349 10602766724040837985266131)
        ·
          refine ⟨15904150086061256977899197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10602766724040837985266131 15904150086061256977899197)
          ·
            refine ⟨5964056282272971366712199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15904150086061256977899197 5964056282272971366712199)
            ·
              refine ⟨8946084423409457050068299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5964056282272971366712199 8946084423409457050068299)
              ·
                refine ⟨13419126635114185575102449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8946084423409457050068299 13419126635114185575102449)
                ·
                  refine ⟨10064344976335639181326837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13419126635114185575102449 10064344976335639181326837)
                  ·
                    refine ⟨943532341531466173249391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10064344976335639181326837 943532341531466173249391)
                    ·
                      rfl

theorem cell22_2756284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_2756284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756284 prefixEnd_2756284 := by exact prefixLift 2756284
  have htrace : WordTrace (prefixWord ++ tailWord_2756284) baseStart_2756284 baseEnd_2756284 := by
    simpa [prefixWord, tailWord_2756284, baseEnd_2756284] using wordTrace_append hprefix tailTrace_2756284
  have hstable : (prefixWord ++ tailWord_2756284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756284).length < 2 ^ (prefixWord ++ tailWord_2756284).sum := by decide
  have hdescent : baseEnd_2756284 < baseStart_2756284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756358 : List Nat := [6, 2, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2756358 : Nat := 118140960795 + 2756358 * 2 ^ 59
def prefixEnd_2756358 : Nat := 4983230072969 + 3 ^ 40 * 2756358 * 2
def baseEnd_2756358 : Nat := 943557673243754646899165

theorem tailTrace_2756358 : CollatzResearch.WordTrace tailWord_2756358 prefixEnd_2756358 943557673243754646899165 := by
  unfold tailWord_2756358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3141644854631037166040929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67021756898795459542206485 3141644854631037166040929)
  ·
    refine ⟨2356233640973277874530697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3141644854631037166040929 2356233640973277874530697)
    ·
      refine ⟨1767175230729958405898023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2356233640973277874530697 1767175230729958405898023)
      ·
        refine ⟨2650762846094937608847035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767175230729958405898023 2650762846094937608847035)
        ·
          refine ⟨3976144269142406413270553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2650762846094937608847035 3976144269142406413270553)
          ·
            refine ⟨2982108201856804809952915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3976144269142406413270553 2982108201856804809952915)
            ·
              refine ⟨4473162302785207214929373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2982108201856804809952915 4473162302785207214929373)
              ·
                refine ⟨1677435863544452705598515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4473162302785207214929373 1677435863544452705598515)
                ·
                  refine ⟨2516153795316679058397773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677435863544452705598515 2516153795316679058397773)
                  ·
                    refine ⟨943557673243754646899165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2516153795316679058397773 943557673243754646899165)
                    ·
                      rfl

theorem cell22_2756358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2756358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756358 prefixEnd_2756358 := by exact prefixLift 2756358
  have htrace : WordTrace (prefixWord ++ tailWord_2756358) baseStart_2756358 baseEnd_2756358 := by
    simpa [prefixWord, tailWord_2756358, baseEnd_2756358] using wordTrace_append hprefix tailTrace_2756358
  have hstable : (prefixWord ++ tailWord_2756358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756358).length < 2 ^ (prefixWord ++ tailWord_2756358).sum := by decide
  have hdescent : baseEnd_2756358 < baseStart_2756358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756382 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 6]
def baseStart_2756382 : Nat := 118140960795 + 2756382 * 2 ^ 59
def prefixEnd_2756382 : Nat := 4983230072969 + 3 ^ 40 * 2756382 * 2
def baseEnd_2756382 : Nat := 314521962978075528099697

theorem tailTrace_2756382 : CollatzResearch.WordTrace tailWord_2756382 prefixEnd_2756382 314521962978075528099697 := by
  unfold tailWord_2756382
  simp only [CollatzResearch.WordTrace]
  refine ⟨12566688837513280176522925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67022340466737494274788933 12566688837513280176522925)
  ·
    refine ⟨4712508314067480066196097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12566688837513280176522925 4712508314067480066196097)
    ·
      refine ⟨3534381235550610049647073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4712508314067480066196097 3534381235550610049647073)
      ·
        refine ⟨2650785926662957537235305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3534381235550610049647073 2650785926662957537235305)
        ·
          refine ⟨1988089444997218152926479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2650785926662957537235305 1988089444997218152926479)
          ·
            refine ⟨2982134167495827229389719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988089444997218152926479 2982134167495827229389719)
            ·
              refine ⟨4473201251243740844084579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2982134167495827229389719 4473201251243740844084579)
              ·
                refine ⟨6709801876865611266126869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4473201251243740844084579 6709801876865611266126869)
                ·
                  refine ⟨314521962978075528099697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6709801876865611266126869 314521962978075528099697)
                  ·
                    rfl

theorem cell22_2756382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_2756382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756382 prefixEnd_2756382 := by exact prefixLift 2756382
  have htrace : WordTrace (prefixWord ++ tailWord_2756382) baseStart_2756382 baseEnd_2756382 := by
    simpa [prefixWord, tailWord_2756382, baseEnd_2756382] using wordTrace_append hprefix tailTrace_2756382
  have hstable : (prefixWord ++ tailWord_2756382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756382).length < 2 ^ (prefixWord ++ tailWord_2756382).sum := by decide
  have hdescent : baseEnd_2756382 < baseStart_2756382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756449 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 6]
def baseStart_2756449 : Nat := 118140960795 + 2756449 * 2 ^ 59
def prefixEnd_2756449 : Nat := 4983230072969 + 3 ^ 40 * 2756449 * 2
def baseEnd_2756449 : Nat := 314529608134486914291295

theorem tailTrace_2756449 : CollatzResearch.WordTrace tailWord_2756449 prefixEnd_2756449 314529608134486914291295 := by
  unfold tailWord_2756449
  simp only [CollatzResearch.WordTrace]
  refine ⟨100535954390863511854872401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67023969593909007903248267 100535954390863511854872401)
  ·
    refine ⟨75401965793147633891154301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100535954390863511854872401 75401965793147633891154301)
    ·
      refine ⟨28275737172430362709182863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75401965793147633891154301 28275737172430362709182863)
      ·
        refine ⟨42413605758645544063774295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28275737172430362709182863 42413605758645544063774295)
        ·
          refine ⟨63620408637968316095661443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42413605758645544063774295 63620408637968316095661443)
          ·
            refine ⟨95430612956952474143492165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63620408637968316095661443 95430612956952474143492165)
            ·
              refine ⟨17893239929428588901904781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95430612956952474143492165 17893239929428588901904781)
              ·
                refine ⟨6709964973535720838214293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17893239929428588901904781 6709964973535720838214293)
                ·
                  refine ⟨314529608134486914291295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6709964973535720838214293 314529608134486914291295)
                  ·
                    rfl

theorem cell22_2756449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 6].length) (baseStart_2756449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756449 prefixEnd_2756449 := by exact prefixLift 2756449
  have htrace : WordTrace (prefixWord ++ tailWord_2756449) baseStart_2756449 baseEnd_2756449 := by
    simpa [prefixWord, tailWord_2756449, baseEnd_2756449] using wordTrace_append hprefix tailTrace_2756449
  have hstable : (prefixWord ++ tailWord_2756449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756449).length < 2 ^ (prefixWord ++ tailWord_2756449).sum := by decide
  have hdescent : baseEnd_2756449 < baseStart_2756449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756483 : List Nat := [1, 1, 1, 3, 4, 3, 2, 3, 4]
def baseStart_2756483 : Nat := 118140960795 + 2756483 * 2 ^ 59
def prefixEnd_2756483 : Nat := 4983230072969 + 3 ^ 40 * 2756483 * 2
def baseEnd_2756483 : Nat := 314533487766098662507927

theorem tailTrace_2756483 : CollatzResearch.WordTrace tailWord_2756483 prefixEnd_2756483 314533487766098662507927 := by
  unfold tailWord_2756483
  simp only [CollatzResearch.WordTrace]
  refine ⟨100537194472740335661610103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67024796315160223774406735 100537194472740335661610103)
  ·
    refine ⟨150805791709110503492415155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100537194472740335661610103 150805791709110503492415155)
    ·
      refine ⟨226208687563665755238622733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150805791709110503492415155 226208687563665755238622733)
      ·
        refine ⟨84828257836374658214483525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226208687563665755238622733 84828257836374658214483525)
        ·
          refine ⟨15905298344320248415215661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84828257836374658214483525 15905298344320248415215661)
          ·
            refine ⟨5964486879120093155705873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15905298344320248415215661 5964486879120093155705873)
            ·
              refine ⟨4473365159340069866779405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5964486879120093155705873 4473365159340069866779405)
              ·
                refine ⟨1677511934752526200042277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4473365159340069866779405 1677511934752526200042277)
                ·
                  refine ⟨314533487766098662507927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1677511934752526200042277 314533487766098662507927)
                  ·
                    rfl

theorem cell22_2756483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 4].length) (baseStart_2756483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756483 prefixEnd_2756483 := by exact prefixLift 2756483
  have htrace : WordTrace (prefixWord ++ tailWord_2756483) baseStart_2756483 baseEnd_2756483 := by
    simpa [prefixWord, tailWord_2756483, baseEnd_2756483] using wordTrace_append hprefix tailTrace_2756483
  have hstable : (prefixWord ++ tailWord_2756483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756483).length < 2 ^ (prefixWord ++ tailWord_2756483).sum := by decide
  have hdescent : baseEnd_2756483 < baseStart_2756483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756539 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 7]
def baseStart_2756539 : Nat := 118140960795 + 2756539 * 2 ^ 59
def prefixEnd_2756539 : Nat := 4983230072969 + 3 ^ 40 * 2756539 * 2
def baseEnd_2756539 : Nat := 314539877747576836041203

theorem tailTrace_2756539 : CollatzResearch.WordTrace tailWord_2756539 prefixEnd_2756539 314539877747576836041203 := by
  unfold tailWord_2756539
  simp only [CollatzResearch.WordTrace]
  refine ⟨100539236960537457225648671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67026157973691638150432447 100539236960537457225648671)
  ·
    refine ⟨150808855440806185838473007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100539236960537457225648671 150808855440806185838473007)
    ·
      refine ⟨226213283161209278757709511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150808855440806185838473007 226213283161209278757709511)
      ·
        refine ⟨339319924741813918136564267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226213283161209278757709511 339319924741813918136564267)
        ·
          refine ⟨508979887112720877204846401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339319924741813918136564267 508979887112720877204846401)
          ·
            refine ⟨381734915334540657903634801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508979887112720877204846401 381734915334540657903634801)
            ·
              refine ⟨286301186500905493427726101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381734915334540657903634801 286301186500905493427726101)
              ·
                refine ⟨13420368117229945004424661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 286301186500905493427726101 13420368117229945004424661)
                ·
                  refine ⟨314539877747576836041203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13420368117229945004424661 314539877747576836041203)
                  ·
                    rfl

theorem cell22_2756539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 7].length) (baseStart_2756539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756539 prefixEnd_2756539 := by exact prefixLift 2756539
  have htrace : WordTrace (prefixWord ++ tailWord_2756539) baseStart_2756539 baseEnd_2756539 := by
    simpa [prefixWord, tailWord_2756539, baseEnd_2756539] using wordTrace_append hprefix tailTrace_2756539
  have hstable : (prefixWord ++ tailWord_2756539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756539).length < 2 ^ (prefixWord ++ tailWord_2756539).sum := by decide
  have hdescent : baseEnd_2756539 < baseStart_2756539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756556 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 7]
def baseStart_2756556 : Nat := 118140960795 + 2756556 * 2 ^ 59
def prefixEnd_2756556 : Nat := 4983230072969 + 3 ^ 40 * 2756556 * 2
def baseEnd_2756556 : Nat := 314541817563382710149519

theorem tailTrace_2756556 : CollatzResearch.WordTrace tailWord_2756556 prefixEnd_2756556 314541817563382710149519 := by
  unfold tailWord_2756556
  simp only [CollatzResearch.WordTrace]
  refine ⟨50269928500737934564508761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67026571334317246086011681 50269928500737934564508761)
  ·
    refine ⟨37702446375553450923381571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50269928500737934564508761 37702446375553450923381571)
    ·
      refine ⟨56553669563330176385072357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37702446375553450923381571 56553669563330176385072357)
      ·
        refine ⟨10603813043124408072201067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56553669563330176385072357 10603813043124408072201067)
        ·
          refine ⟨15905719564686612108301601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10603813043124408072201067 15905719564686612108301601)
          ·
            refine ⟨11929289673514959081226201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15905719564686612108301601 11929289673514959081226201)
            ·
              refine ⟨8946967255136219310919651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11929289673514959081226201 8946967255136219310919651)
              ·
                refine ⟨13420450882704328966379477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8946967255136219310919651 13420450882704328966379477)
                ·
                  refine ⟨314541817563382710149519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13420450882704328966379477 314541817563382710149519)
                  ·
                    rfl

theorem cell22_2756556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_2756556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756556 prefixEnd_2756556 := by exact prefixLift 2756556
  have htrace : WordTrace (prefixWord ++ tailWord_2756556) baseStart_2756556 baseEnd_2756556 := by
    simpa [prefixWord, tailWord_2756556, baseEnd_2756556] using wordTrace_append hprefix tailTrace_2756556
  have hstable : (prefixWord ++ tailWord_2756556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756556).length < 2 ^ (prefixWord ++ tailWord_2756556).sum := by decide
  have hdescent : baseEnd_2756556 < baseStart_2756556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756566 : List Nat := [5, 2, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_2756566 : Nat := 118140960795 + 2756566 * 2 ^ 59
def prefixEnd_2756566 : Nat := 4983230072969 + 3 ^ 40 * 2756566 * 2
def baseEnd_2756566 : Nat := 943628875894511437698527

theorem tailTrace_2756566 : CollatzResearch.WordTrace tailWord_2756566 prefixEnd_2756566 943628875894511437698527 := by
  unfold tailWord_2756566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6283763858214977552305097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67026814487626427224587701 6283763858214977552305097)
  ·
    refine ⟨4712822893661233164228823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6283763858214977552305097 4712822893661233164228823)
    ·
      refine ⟨7069234340491849746343235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4712822893661233164228823 7069234340491849746343235)
      ·
        refine ⟨10603851510737774619514853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7069234340491849746343235 10603851510737774619514853)
        ·
          refine ⟨1988222158263332741159035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10603851510737774619514853 1988222158263332741159035)
          ·
            refine ⟨2982333237394999111738553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988222158263332741159035 2982333237394999111738553)
            ·
              refine ⟨2236749928046249333803915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2982333237394999111738553 2236749928046249333803915)
              ·
                refine ⟨3355124892069374000705873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236749928046249333803915 3355124892069374000705873)
                ·
                  refine ⟨2516343669052030500529405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3355124892069374000705873 2516343669052030500529405)
                  ·
                    refine ⟨943628875894511437698527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2516343669052030500529405 943628875894511437698527)
                    ·
                      rfl

theorem cell22_2756566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_2756566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756566 prefixEnd_2756566 := by exact prefixLift 2756566
  have htrace : WordTrace (prefixWord ++ tailWord_2756566) baseStart_2756566 baseEnd_2756566 := by
    simpa [prefixWord, tailWord_2756566, baseEnd_2756566] using wordTrace_append hprefix tailTrace_2756566
  have hstable : (prefixWord ++ tailWord_2756566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756566).length < 2 ^ (prefixWord ++ tailWord_2756566).sum := by decide
  have hdescent : baseEnd_2756566 < baseStart_2756566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756616 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 3, 5]
def baseStart_2756616 : Nat := 118140960795 + 2756616 * 2 ^ 59
def prefixEnd_2756616 : Nat := 4983230072969 + 3 ^ 40 * 2756616 * 2
def baseEnd_2756616 : Nat := 943645991916327973948373

theorem tailTrace_2756616 : CollatzResearch.WordTrace tailWord_2756616 prefixEnd_2756616 943645991916327973948373 := by
  unfold tailWord_2756616
  simp only [CollatzResearch.WordTrace]
  refine ⟨50271022690629249688100851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67028030254172332917467801 50271022690629249688100851)
  ·
    refine ⟨75406534035943874532151277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50271022690629249688100851 75406534035943874532151277)
    ·
      refine ⟨28277450263478952949556729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75406534035943874532151277 28277450263478952949556729)
      ·
        refine ⟨21208087697609214712167547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28277450263478952949556729 21208087697609214712167547)
        ·
          refine ⟨31812131546413822068251321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21208087697609214712167547 31812131546413822068251321)
          ·
            refine ⟨23859098659810366551188491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31812131546413822068251321 23859098659810366551188491)
            ·
              refine ⟨35788647989715549826782737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23859098659810366551188491 35788647989715549826782737)
              ·
                refine ⟨26841485992286662370087053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35788647989715549826782737 26841485992286662370087053)
                ·
                  refine ⟨10065557247107498388782645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26841485992286662370087053 10065557247107498388782645)
                  ·
                    refine ⟨943645991916327973948373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10065557247107498388782645 943645991916327973948373)
                    ·
                      rfl

theorem cell22_2756616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_2756616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756616 prefixEnd_2756616 := by exact prefixLift 2756616
  have htrace : WordTrace (prefixWord ++ tailWord_2756616) baseStart_2756616 baseEnd_2756616 := by
    simpa [prefixWord, tailWord_2756616, baseEnd_2756616] using wordTrace_append hprefix tailTrace_2756616
  have hstable : (prefixWord ++ tailWord_2756616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756616).length < 2 ^ (prefixWord ++ tailWord_2756616).sum := by decide
  have hdescent : baseEnd_2756616 < baseStart_2756616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756729 : List Nat := [1, 2, 1, 3, 4, 2, 3, 2, 1, 3]
def baseStart_2756729 : Nat := 118140960795 + 2756729 * 2 ^ 59
def prefixEnd_2756729 : Nat := 4983230072969 + 3 ^ 40 * 2756729 * 2
def baseEnd_2756729 : Nat := 943684674125633345873027

theorem tailTrace_2756729 : CollatzResearch.WordTrace tailWord_2756729 prefixEnd_2756729 943684674125633345873027 := by
  unfold tailWord_2756729
  simp only [CollatzResearch.WordTrace]
  refine ⟨100546166829849119675065241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67030777886566079783376827 100546166829849119675065241)
  ·
    refine ⟨75409625122386839756298931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100546166829849119675065241 75409625122386839756298931)
    ·
      refine ⟨113114437683580259634448397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75409625122386839756298931 113114437683580259634448397)
      ·
        refine ⟨42417914131342597362918149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113114437683580259634448397 42417914131342597362918149)
        ·
          refine ⟨7953358899626737005547153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42417914131342597362918149 7953358899626737005547153)
          ·
            refine ⟨5965019174720052754160365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7953358899626737005547153 5965019174720052754160365)
            ·
              refine ⟨2236882190520019782810137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5965019174720052754160365 2236882190520019782810137)
              ·
                refine ⟨1677661642890014837107603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2236882190520019782810137 1677661642890014837107603)
                ·
                  refine ⟨2516492464335022255661405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677661642890014837107603 2516492464335022255661405)
                  ·
                    refine ⟨943684674125633345873027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2516492464335022255661405 943684674125633345873027)
                    ·
                      rfl

theorem cell22_2756729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 1, 3].length) (baseStart_2756729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756729 prefixEnd_2756729 := by exact prefixLift 2756729
  have htrace : WordTrace (prefixWord ++ tailWord_2756729) baseStart_2756729 baseEnd_2756729 := by
    simpa [prefixWord, tailWord_2756729, baseEnd_2756729] using wordTrace_append hprefix tailTrace_2756729
  have hstable : (prefixWord ++ tailWord_2756729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756729).length < 2 ^ (prefixWord ++ tailWord_2756729).sum := by decide
  have hdescent : baseEnd_2756729 < baseStart_2756729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756751 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 1, 11]
def baseStart_2756751 : Nat := 118140960795 + 2756751 * 2 ^ 59
def prefixEnd_2756751 : Nat := 4983230072969 + 3 ^ 40 * 2756751 * 2
def baseEnd_2756751 : Nat := 943692205175232621822959

theorem tailTrace_2756751 : CollatzResearch.WordTrace tailWord_2756751 prefixEnd_2756751 943692205175232621822959 := by
  unfold tailWord_2756751
  simp only [CollatzResearch.WordTrace]
  refine ⟨100546969235769417432366107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67031312823846278288244071 100546969235769417432366107)
  ·
    refine ⟨150820453853654126148549161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100546969235769417432366107 150820453853654126148549161)
    ·
      refine ⟨113115340390240594611411871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150820453853654126148549161 113115340390240594611411871)
      ·
        refine ⟨169673010585360891917117807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113115340390240594611411871 169673010585360891917117807)
        ·
          refine ⟨254509515878041337875676711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169673010585360891917117807 254509515878041337875676711)
          ·
            refine ⟨381764273817062006813515067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254509515878041337875676711 381764273817062006813515067)
            ·
              refine ⟨572646410725593010220272601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381764273817062006813515067 572646410725593010220272601)
              ·
                refine ⟨429484808044194757665204451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572646410725593010220272601 429484808044194757665204451)
                ·
                  refine ⟨644227212066292136497806677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429484808044194757665204451 644227212066292136497806677)
                  ·
                    refine ⟨943692205175232621822959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 644227212066292136497806677 943692205175232621822959)
                    ·
                      rfl

theorem cell22_2756751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_2756751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756751 prefixEnd_2756751 := by exact prefixLift 2756751
  have htrace : WordTrace (prefixWord ++ tailWord_2756751) baseStart_2756751 baseEnd_2756751 := by
    simpa [prefixWord, tailWord_2756751, baseEnd_2756751] using wordTrace_append hprefix tailTrace_2756751
  have hstable : (prefixWord ++ tailWord_2756751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756751).length < 2 ^ (prefixWord ++ tailWord_2756751).sum := by decide
  have hdescent : baseEnd_2756751 < baseStart_2756751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756768 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 3, 5]
def baseStart_2756768 : Nat := 118140960795 + 2756768 * 2 ^ 59
def prefixEnd_2756768 : Nat := 4983230072969 + 3 ^ 40 * 2756768 * 2
def baseEnd_2756768 : Nat := 943698024622650244147907

theorem tailTrace_2756768 : CollatzResearch.WordTrace tailWord_2756768 prefixEnd_2756768 943698024622650244147907 := by
  unfold tailWord_2756768
  simp only [CollatzResearch.WordTrace]
  refine ⟨50273794638353914667867479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67031726184471886223823305 50273794638353914667867479)
  ·
    refine ⟨75410691957530872001801219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50273794638353914667867479 75410691957530872001801219)
    ·
      refine ⟨113116037936296308002701829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75410691957530872001801219 113116037936296308002701829)
      ·
        refine ⟨21209257113055557750506593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113116037936296308002701829 21209257113055557750506593)
        ·
          refine ⟨15906942834791668312879945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21209257113055557750506593 15906942834791668312879945)
          ·
            refine ⟨11930207126093751234659959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15906942834791668312879945 11930207126093751234659959)
            ·
              refine ⟨17895310689140626851989939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11930207126093751234659959 17895310689140626851989939)
              ·
                refine ⟨26842966033710940277984909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17895310689140626851989939 26842966033710940277984909)
                ·
                  refine ⟨10066112262641602604244341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26842966033710940277984909 10066112262641602604244341)
                  ·
                    refine ⟨943698024622650244147907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10066112262641602604244341 943698024622650244147907)
                    ·
                      rfl

theorem cell22_2756768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_2756768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756768 prefixEnd_2756768 := by exact prefixLift 2756768
  have htrace : WordTrace (prefixWord ++ tailWord_2756768) baseStart_2756768 baseEnd_2756768 := by
    simpa [prefixWord, tailWord_2756768, baseEnd_2756768] using wordTrace_append hprefix tailTrace_2756768
  have hstable : (prefixWord ++ tailWord_2756768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756768).length < 2 ^ (prefixWord ++ tailWord_2756768).sum := by decide
  have hdescent : baseEnd_2756768 < baseStart_2756768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756843 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 7]
def baseStart_2756843 : Nat := 118140960795 + 2756843 * 2 ^ 59
def prefixEnd_2756843 : Nat := 4983230072969 + 3 ^ 40 * 2756843 * 2
def baseEnd_2756843 : Nat := 314574566218458349507559

theorem tailTrace_2756843 : CollatzResearch.WordTrace tailWord_2756843 prefixEnd_2756843 314574566218458349507559 := by
  unfold tailWord_2756843
  simp only [CollatzResearch.WordTrace]
  refine ⟨100550324751436117144715183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67033549834290744763143455 100550324751436117144715183)
  ·
    refine ⟨150825487127154175717072775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100550324751436117144715183 150825487127154175717072775)
    ·
      refine ⟨226238230690731263575609163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150825487127154175717072775 226238230690731263575609163)
      ·
        refine ⟨339357346036096895363413745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226238230690731263575609163 339357346036096895363413745)
        ·
          refine ⟨254518009527072671522560309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339357346036096895363413745 254518009527072671522560309)
          ·
            refine ⟨23861063393163062955240029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 254518009527072671522560309 23861063393163062955240029)
            ·
              refine ⟨8947898772436148608215011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23861063393163062955240029 8947898772436148608215011)
              ·
                refine ⟨13421848158654222912322517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8947898772436148608215011 13421848158654222912322517)
                ·
                  refine ⟨314574566218458349507559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13421848158654222912322517 314574566218458349507559)
                  ·
                    rfl

theorem cell22_2756843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 7].length) (baseStart_2756843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756843 prefixEnd_2756843 := by exact prefixLift 2756843
  have htrace : WordTrace (prefixWord ++ tailWord_2756843) baseStart_2756843 baseEnd_2756843 := by
    simpa [prefixWord, tailWord_2756843, baseEnd_2756843] using wordTrace_append hprefix tailTrace_2756843
  have hstable : (prefixWord ++ tailWord_2756843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756843).length < 2 ^ (prefixWord ++ tailWord_2756843).sum := by decide
  have hdescent : baseEnd_2756843 < baseStart_2756843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756847 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 3, 3]
def baseStart_2756847 : Nat := 118140960795 + 2756847 * 2 ^ 59
def prefixEnd_2756847 : Nat := 4983230072969 + 3 ^ 40 * 2756847 * 2
def baseEnd_2756847 : Nat := 943725067937120371422665

theorem tailTrace_2756847 : CollatzResearch.WordTrace tailWord_2756847 prefixEnd_2756847 943725067937120371422665 := by
  unfold tailWord_2756847
  simp only [CollatzResearch.WordTrace]
  refine ⟨100550470643421625827860795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67033647095614417218573863 100550470643421625827860795)
  ·
    refine ⟨150825705965132438741791193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100550470643421625827860795 150825705965132438741791193)
    ·
      refine ⟨113119279473849329056343395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150825705965132438741791193 113119279473849329056343395)
      ·
        refine ⟨169678919210773993584515093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113119279473849329056343395 169678919210773993584515093)
        ·
          refine ⟨7953699338005030949274145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 169678919210773993584515093 7953699338005030949274145)
          ·
            refine ⟨5965274503503773211955609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7953699338005030949274145 5965274503503773211955609)
            ·
              refine ⟨4473955877627829908966707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5965274503503773211955609 4473955877627829908966707)
              ·
                refine ⟨6710933816441744863450061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4473955877627829908966707 6710933816441744863450061)
                ·
                  refine ⟨2516600181165654323793773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6710933816441744863450061 2516600181165654323793773)
                  ·
                    refine ⟨943725067937120371422665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2516600181165654323793773 943725067937120371422665)
                    ·
                      rfl

theorem cell22_2756847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 3].length) (baseStart_2756847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756847 prefixEnd_2756847 := by exact prefixLift 2756847
  have htrace : WordTrace (prefixWord ++ tailWord_2756847) baseStart_2756847 baseEnd_2756847 := by
    simpa [prefixWord, tailWord_2756847, baseEnd_2756847] using wordTrace_append hprefix tailTrace_2756847
  have hstable : (prefixWord ++ tailWord_2756847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756847).length < 2 ^ (prefixWord ++ tailWord_2756847).sum := by decide
  have hdescent : baseEnd_2756847 < baseStart_2756847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756956 : List Nat := [2, 2, 4, 3, 1, 1, 1, 4, 4]
def baseStart_2756956 : Nat := 118140960795 + 2756956 * 2 ^ 59
def prefixEnd_2756956 : Nat := 4983230072969 + 3 ^ 40 * 2756956 * 2
def baseEnd_2756956 : Nat := 314587460288226806815777

theorem tailTrace_2756956 : CollatzResearch.WordTrace tailWord_2756956 prefixEnd_2756956 314587460288226806815777 := by
  unfold tailWord_2756956
  simp only [CollatzResearch.WordTrace]
  refine ⟨50277223100013368721789361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67036297466684491629052481 50277223100013368721789361)
  ·
    refine ⟨37707917325010026541342021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50277223100013368721789361 37707917325010026541342021)
    ·
      refine ⟨7070234498439379976501629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37707917325010026541342021 7070234498439379976501629)
      ·
        refine ⟨2651337936914767491188111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7070234498439379976501629 2651337936914767491188111)
        ·
          refine ⟨3977006905372151236782167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2651337936914767491188111 3977006905372151236782167)
          ·
            refine ⟨5965510358058226855173251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977006905372151236782167 5965510358058226855173251)
            ·
              refine ⟨8948265537087340282759877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5965510358058226855173251 8948265537087340282759877)
              ·
                refine ⟨1677799788203876303017477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8948265537087340282759877 1677799788203876303017477)
                ·
                  refine ⟨314587460288226806815777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1677799788203876303017477 314587460288226806815777)
                  ·
                    rfl

theorem cell22_2756956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_2756956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756956 prefixEnd_2756956 := by exact prefixLift 2756956
  have htrace : WordTrace (prefixWord ++ tailWord_2756956) baseStart_2756956 baseEnd_2756956 := by
    simpa [prefixWord, tailWord_2756956, baseEnd_2756956] using wordTrace_append hprefix tailTrace_2756956
  have hstable : (prefixWord ++ tailWord_2756956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756956).length < 2 ^ (prefixWord ++ tailWord_2756956).sum := by decide
  have hdescent : baseEnd_2756956 < baseStart_2756956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756967 : List Nat := [1, 1, 5, 1, 3, 3, 1, 7]
def baseStart_2756967 : Nat := 118140960795 + 2756967 * 2 ^ 59
def prefixEnd_2756967 : Nat := 4983230072969 + 3 ^ 40 * 2756967 * 2
def baseEnd_2756967 : Nat := 104862905154386673158033

theorem tailTrace_2756967 : CollatzResearch.WordTrace tailWord_2756967 prefixEnd_2756967 104862905154386673158033 := by
  unfold tailWord_2756967
  simp only [CollatzResearch.WordTrace]
  refine ⟨100554847402986886322229155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67036564935324590881486103 100554847402986886322229155)
  ·
    refine ⟨150832271104480329483343733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100554847402986886322229155 150832271104480329483343733)
    ·
      refine ⟨14140525416045030889063475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150832271104480329483343733 14140525416045030889063475)
      ·
        refine ⟨21210788124067546333595213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14140525416045030889063475 21210788124067546333595213)
        ·
          refine ⟨7954045546525329875098205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21210788124067546333595213 7954045546525329875098205)
          ·
            refine ⟨2982767079946998703161827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7954045546525329875098205 2982767079946998703161827)
            ·
              refine ⟨4474150619920498054742741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2982767079946998703161827 4474150619920498054742741)
              ·
                refine ⟨104862905154386673158033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4474150619920498054742741 104862905154386673158033)
                ·
                  rfl

theorem cell22_2756967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 7].length) (baseStart_2756967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2756967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2756967 prefixEnd_2756967 := by exact prefixLift 2756967
  have htrace : WordTrace (prefixWord ++ tailWord_2756967) baseStart_2756967 baseEnd_2756967 := by
    simpa [prefixWord, tailWord_2756967, baseEnd_2756967] using wordTrace_append hprefix tailTrace_2756967
  have hstable : (prefixWord ++ tailWord_2756967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756967).length < 2 ^ (prefixWord ++ tailWord_2756967).sum := by decide
  have hdescent : baseEnd_2756967 < baseStart_2756967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757016 : List Nat := [2, 1, 2, 5, 1, 1, 2, 4, 1, 3]
def baseStart_2757016 : Nat := 118140960795 + 2757016 * 2 ^ 59
def prefixEnd_2757016 : Nat := 4983230072969 + 3 ^ 40 * 2757016 * 2
def baseEnd_2757016 : Nat := 943782920090860263947147

theorem tailTrace_2757016 : CollatzResearch.WordTrace tailWord_2757016 prefixEnd_2757016 943782920090860263947147 := by
  unfold tailWord_2757016
  simp only [CollatzResearch.WordTrace]
  refine ⟨50278317289904683845381451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67037756386539578460508601 50278317289904683845381451)
  ·
    refine ⟨75417475934857025768072177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50278317289904683845381451 75417475934857025768072177)
    ·
      refine ⟨56563106951142769326054133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75417475934857025768072177 56563106951142769326054133)
      ·
        refine ⟨5302791276669634624317575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56563106951142769326054133 5302791276669634624317575)
        ·
          refine ⟨7954186915004451936476363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5302791276669634624317575 7954186915004451936476363)
          ·
            refine ⟨11931280372506677904714545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7954186915004451936476363 11931280372506677904714545)
            ·
              refine ⟨8948460279380008428535909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11931280372506677904714545 8948460279380008428535909)
              ·
                refine ⟨1677836302383751580350483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8948460279380008428535909 1677836302383751580350483)
                ·
                  refine ⟨2516754453575627370525725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677836302383751580350483 2516754453575627370525725)
                  ·
                    refine ⟨943782920090860263947147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2516754453575627370525725 943782920090860263947147)
                    ·
                      rfl

theorem cell22_2757016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_2757016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757016 prefixEnd_2757016 := by exact prefixLift 2757016
  have htrace : WordTrace (prefixWord ++ tailWord_2757016) baseStart_2757016 baseEnd_2757016 := by
    simpa [prefixWord, tailWord_2757016, baseEnd_2757016] using wordTrace_append hprefix tailTrace_2757016
  have hstable : (prefixWord ++ tailWord_2757016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757016).length < 2 ^ (prefixWord ++ tailWord_2757016).sum := by decide
  have hdescent : baseEnd_2757016 < baseStart_2757016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757089 : List Nat := [1, 2, 3, 1, 2, 2, 3, 3, 2, 3]
def baseStart_2757089 : Nat := 118140960795 + 2757089 * 2 ^ 59
def prefixEnd_2757089 : Nat := 4983230072969 + 3 ^ 40 * 2757089 * 2
def baseEnd_2757089 : Nat := 943807909482712406871923

theorem tailTrace_2757089 : CollatzResearch.WordTrace tailWord_2757089 prefixEnd_2757089 943807909482712406871923 := by
  unfold tailWord_2757089
  simp only [CollatzResearch.WordTrace]
  refine ⟨100559297108544901158170321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67039531405696600772113547 100559297108544901158170321)
  ·
    refine ⟨75419472831408675868627741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100559297108544901158170321 75419472831408675868627741)
    ·
      refine ⟨28282302311778253450735403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75419472831408675868627741 28282302311778253450735403)
      ·
        refine ⟨42423453467667380176103105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28282302311778253450735403 42423453467667380176103105)
        ·
          refine ⟨31817590100750535132077329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42423453467667380176103105 31817590100750535132077329)
          ·
            refine ⟨23863192575562901349057997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31817590100750535132077329 23863192575562901349057997)
            ·
              refine ⟨8948697215836088005896749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23863192575562901349057997 8948697215836088005896749)
              ·
                refine ⟨3355761455938533002211281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8948697215836088005896749 3355761455938533002211281)
                ·
                  refine ⟨2516821091953899751658461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3355761455938533002211281 2516821091953899751658461)
                  ·
                    refine ⟨943807909482712406871923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2516821091953899751658461 943807909482712406871923)
                    ·
                      rfl

theorem cell22_2757089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_2757089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757089 prefixEnd_2757089 := by exact prefixLift 2757089
  have htrace : WordTrace (prefixWord ++ tailWord_2757089) baseStart_2757089 baseEnd_2757089 := by
    simpa [prefixWord, tailWord_2757089, baseEnd_2757089] using wordTrace_append hprefix tailTrace_2757089
  have hstable : (prefixWord ++ tailWord_2757089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757089).length < 2 ^ (prefixWord ++ tailWord_2757089).sum := by decide
  have hdescent : baseEnd_2757089 < baseStart_2757089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757093 : List Nat := [1, 3, 1, 5, 3, 1, 1, 2, 1, 4]
def baseStart_2757093 : Nat := 118140960795 + 2757093 * 2 ^ 59
def prefixEnd_2757093 : Nat := 4983230072969 + 3 ^ 40 * 2757093 * 2
def baseEnd_2757093 : Nat := 943809278764457729771911

theorem tailTrace_2757093 : CollatzResearch.WordTrace tailWord_2757093 prefixEnd_2757093 943809278764457729771911 := by
  unfold tailWord_2757093
  simp only [CollatzResearch.WordTrace]
  refine ⟨100559443000530409841315933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67039628667020273227543955 100559443000530409841315933)
  ·
    refine ⟨37709791125198903690493475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100559443000530409841315933 37709791125198903690493475)
    ·
      refine ⟨56564686687798355535740213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37709791125198903690493475 56564686687798355535740213)
      ·
        refine ⟨5302939376981095831475645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56564686687798355535740213 5302939376981095831475645)
        ·
          refine ⟨1988602266367910936803367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5302939376981095831475645 1988602266367910936803367)
          ·
            refine ⟨2982903399551866405205051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988602266367910936803367 2982903399551866405205051)
            ·
              refine ⟨4474355099327799607807577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2982903399551866405205051 4474355099327799607807577)
              ·
                refine ⟨3355766324495849705855683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4474355099327799607807577 3355766324495849705855683)
                ·
                  refine ⟨5033649486743774558783525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355766324495849705855683 5033649486743774558783525)
                  ·
                    refine ⟨943809278764457729771911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5033649486743774558783525 943809278764457729771911)
                    ·
                      rfl

theorem cell22_2757093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_2757093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757093 prefixEnd_2757093 := by exact prefixLift 2757093
  have htrace : WordTrace (prefixWord ++ tailWord_2757093) baseStart_2757093 baseEnd_2757093 := by
    simpa [prefixWord, tailWord_2757093, baseEnd_2757093] using wordTrace_append hprefix tailTrace_2757093
  have hstable : (prefixWord ++ tailWord_2757093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757093).length < 2 ^ (prefixWord ++ tailWord_2757093).sum := by decide
  have hdescent : baseEnd_2757093 < baseStart_2757093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757102 : List Nat := [4, 1, 2, 1, 2, 2, 2, 8]
def baseStart_2757102 : Nat := 118140960795 + 2757102 * 2 ^ 59
def prefixEnd_2757102 : Nat := 4983230072969 + 3 ^ 40 * 2757102 * 2
def baseEnd_2757102 : Nat := 104868039960931634032987

theorem tailTrace_2757102 : CollatzResearch.WordTrace tailWord_2757102 prefixEnd_2757102 104868039960931634032987 := by
  unfold tailWord_2757102
  simp only [CollatzResearch.WordTrace]
  refine ⟨12569971407187225547299195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67039847504998536252262373 12569971407187225547299195)
  ·
    refine ⟨18854957110780838320948793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12569971407187225547299195 18854957110780838320948793)
    ·
      refine ⟨14141217833085628740711595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18854957110780838320948793 14141217833085628740711595)
      ·
        refine ⟨21211826749628443111067393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14141217833085628740711595 21211826749628443111067393)
        ·
          refine ⟨15908870062221332333300545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21211826749628443111067393 15908870062221332333300545)
          ·
            refine ⟨11931652546665999249975409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15908870062221332333300545 11931652546665999249975409)
            ·
              refine ⟨8948739409999499437481557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11931652546665999249975409 8948739409999499437481557)
              ·
                refine ⟨104868039960931634032987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8948739409999499437481557 104868039960931634032987)
                ·
                  rfl

theorem cell22_2757102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_2757102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757102 prefixEnd_2757102 := by exact prefixLift 2757102
  have htrace : WordTrace (prefixWord ++ tailWord_2757102) baseStart_2757102 baseEnd_2757102 := by
    simpa [prefixWord, tailWord_2757102, baseEnd_2757102] using wordTrace_append hprefix tailTrace_2757102
  have hstable : (prefixWord ++ tailWord_2757102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757102).length < 2 ^ (prefixWord ++ tailWord_2757102).sum := by decide
  have hdescent : baseEnd_2757102 < baseStart_2757102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757115 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 3, 8]
def baseStart_2757115 : Nat := 118140960795 + 2757115 * 2 ^ 59
def prefixEnd_2757115 : Nat := 4983230072969 + 3 ^ 40 * 2757115 * 2
def baseEnd_2757115 : Nat := 943816809814057005721843

theorem tailTrace_2757115 : CollatzResearch.WordTrace tailWord_2757115 prefixEnd_2757115 943816809814057005721843 := by
  unfold tailWord_2757115
  simp only [CollatzResearch.WordTrace]
  refine ⟨100560245406450707598616799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67040163604300471732411199 100560245406450707598616799)
  ·
    refine ⟨150840368109676061397925199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100560245406450707598616799 150840368109676061397925199)
    ·
      refine ⟨226260552164514092096887799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150840368109676061397925199 226260552164514092096887799)
      ·
        refine ⟨339390828246771138145331699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226260552164514092096887799 339390828246771138145331699)
        ·
          refine ⟨509086242370156707217997549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339390828246771138145331699 509086242370156707217997549)
          ·
            refine ⟨190907340888808765206749081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 509086242370156707217997549 190907340888808765206749081)
            ·
              refine ⟨143180505666606573905061811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190907340888808765206749081 143180505666606573905061811)
              ·
                refine ⟨214770758499909860857592717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143180505666606573905061811 214770758499909860857592717)
                ·
                  refine ⟨80539034437466197821597269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214770758499909860857592717 80539034437466197821597269)
                  ·
                    refine ⟨943816809814057005721843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80539034437466197821597269 943816809814057005721843)
                    ·
                      rfl

theorem cell22_2757115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 8].length) (baseStart_2757115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757115 prefixEnd_2757115 := by exact prefixLift 2757115
  have htrace : WordTrace (prefixWord ++ tailWord_2757115) baseStart_2757115 baseEnd_2757115 := by
    simpa [prefixWord, tailWord_2757115, baseEnd_2757115] using wordTrace_append hprefix tailTrace_2757115
  have hstable : (prefixWord ++ tailWord_2757115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757115).length < 2 ^ (prefixWord ++ tailWord_2757115).sum := by decide
  have hdescent : baseEnd_2757115 < baseStart_2757115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757132 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 2, 6]
def baseStart_2757132 : Nat := 118140960795 + 2757132 * 2 ^ 59
def prefixEnd_2757132 : Nat := 4983230072969 + 3 ^ 40 * 2757132 * 2
def baseEnd_2757132 : Nat := 943822629261474628046791

theorem tailTrace_2757132 : CollatzResearch.WordTrace tailWord_2757132 prefixEnd_2757132 943822629261474628046791 := by
  unfold tailWord_2757132
  simp only [CollatzResearch.WordTrace]
  refine ⟨50280432723694559750992825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67040576964926079667990433 50280432723694559750992825)
  ·
    refine ⟨37710324542770919813244619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50280432723694559750992825 37710324542770919813244619)
    ·
      refine ⟨56565486814156379719866929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37710324542770919813244619 56565486814156379719866929)
      ·
        refine ⟨42424115110617284789900197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56565486814156379719866929 42424115110617284789900197)
        ·
          refine ⟨7954521583240740898106287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42424115110617284789900197 7954521583240740898106287)
          ·
            refine ⟨11931782374861111347159431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7954521583240740898106287 11931782374861111347159431)
            ·
              refine ⟨17897673562291667020739147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11931782374861111347159431 17897673562291667020739147)
              ·
                refine ⟨26846510343437500531108721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17897673562291667020739147 26846510343437500531108721)
                ·
                  refine ⟨20134882757578125398331541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26846510343437500531108721 20134882757578125398331541)
                  ·
                    refine ⟨943822629261474628046791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20134882757578125398331541 943822629261474628046791)
                    ·
                      rfl

theorem cell22_2757132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_2757132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757132 prefixEnd_2757132 := by exact prefixLift 2757132
  have htrace : WordTrace (prefixWord ++ tailWord_2757132) baseStart_2757132 baseEnd_2757132 := by
    simpa [prefixWord, tailWord_2757132, baseEnd_2757132] using wordTrace_append hprefix tailTrace_2757132
  have hstable : (prefixWord ++ tailWord_2757132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757132).length < 2 ^ (prefixWord ++ tailWord_2757132).sum := by decide
  have hdescent : baseEnd_2757132 < baseStart_2757132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757181 : List Nat := [1, 4, 1, 3, 2, 3, 1, 2, 5]
def baseStart_2757181 : Nat := 118140960795 + 2757181 * 2 ^ 59
def prefixEnd_2757181 : Nat := 4983230072969 + 3 ^ 40 * 2757181 * 2
def baseEnd_2757181 : Nat := 314613134320951611190547

theorem tailTrace_2757181 : CollatzResearch.WordTrace tailWord_2757181 prefixEnd_2757181 314613134320951611190547 := by
  unfold tailWord_2757181
  simp only [CollatzResearch.WordTrace]
  refine ⟨100562652624211600870519397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67041768416141067247012931 100562652624211600870519397)
  ·
    refine ⟨18855497367039675163222387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100562652624211600870519397 18855497367039675163222387)
    ·
      refine ⟨28283246050559512744833581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18855497367039675163222387 28283246050559512744833581)
      ·
        refine ⟨10606217268959817279312593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28283246050559512744833581 10606217268959817279312593)
        ·
          refine ⟨7954662951719862959484445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10606217268959817279312593 7954662951719862959484445)
          ·
            refine ⟨2982998606894948609806667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7954662951719862959484445 2982998606894948609806667)
            ·
              refine ⟨4474497910342422914710001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2982998606894948609806667 4474497910342422914710001)
              ·
                refine ⟨3355873432756817186032501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4474497910342422914710001 3355873432756817186032501)
                ·
                  refine ⟨314613134320951611190547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3355873432756817186032501 314613134320951611190547)
                  ·
                    rfl

theorem cell22_2757181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_2757181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757181 prefixEnd_2757181 := by exact prefixLift 2757181
  have htrace : WordTrace (prefixWord ++ tailWord_2757181) baseStart_2757181 baseEnd_2757181 := by
    simpa [prefixWord, tailWord_2757181, baseEnd_2757181] using wordTrace_append hprefix tailTrace_2757181
  have hstable : (prefixWord ++ tailWord_2757181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757181).length < 2 ^ (prefixWord ++ tailWord_2757181).sum := by decide
  have hdescent : baseEnd_2757181 < baseStart_2757181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757258 : List Nat := [3, 1, 2, 3, 3, 1, 1, 3, 2, 3]
def baseStart_2757258 : Nat := 118140960795 + 2757258 * 2 ^ 59
def prefixEnd_2757258 : Nat := 4983230072969 + 3 ^ 40 * 2757258 * 2
def baseEnd_2757258 : Nat := 943865761636452299396405

theorem tailTrace_2757258 : CollatzResearch.WordTrace tailWord_2757258 prefixEnd_2757258 943865761636452299396405 := by
  unfold tailWord_2757258
  simp only [CollatzResearch.WordTrace]
  refine ⟨25141365261233160755268107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67043640696621762014048285 25141365261233160755268107)
  ·
    refine ⟨37712047891849741132902161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25141365261233160755268107 37712047891849741132902161)
    ·
      refine ⟨28284035918887305849676621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37712047891849741132902161 28284035918887305849676621)
      ·
        refine ⟨10606513469582739693628733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28284035918887305849676621 10606513469582739693628733)
        ·
          refine ⟨3977442551093527385110775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10606513469582739693628733 3977442551093527385110775)
          ·
            refine ⟨5966163826640291077666163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977442551093527385110775 5966163826640291077666163)
            ·
              refine ⟨8949245739960436616499245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5966163826640291077666163 8949245739960436616499245)
              ·
                refine ⟨3355967152485163731187217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8949245739960436616499245 3355967152485163731187217)
                ·
                  refine ⟨2516975364363872798390413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3355967152485163731187217 2516975364363872798390413)
                  ·
                    refine ⟨943865761636452299396405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2516975364363872798390413 943865761636452299396405)
                    ·
                      rfl

theorem cell22_2757258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_2757258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757258 prefixEnd_2757258 := by exact prefixLift 2757258
  have htrace : WordTrace (prefixWord ++ tailWord_2757258) baseStart_2757258 baseEnd_2757258 := by
    simpa [prefixWord, tailWord_2757258, baseEnd_2757258] using wordTrace_append hprefix tailTrace_2757258
  have hstable : (prefixWord ++ tailWord_2757258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757258).length < 2 ^ (prefixWord ++ tailWord_2757258).sum := by decide
  have hdescent : baseEnd_2757258 < baseStart_2757258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757267 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 2, 6]
def baseStart_2757267 : Nat := 118140960795 + 2757267 * 2 ^ 59
def prefixEnd_2757267 : Nat := 4983230072969 + 3 ^ 40 * 2757267 * 2
def baseEnd_2757267 : Nat := 943868842520379275921377

theorem tailTrace_2757267 : CollatzResearch.WordTrace tailWord_2757267 prefixEnd_2757267 943868842520379275921377 := by
  unfold tailWord_2757267
  simp only [CollatzResearch.WordTrace]
  refine ⟨100565789301900037558150055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67043859534600025038766703 100565789301900037558150055)
  ·
    refine ⟨150848683952850056337225083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100565789301900037558150055 150848683952850056337225083)
    ·
      refine ⟨226273025929275084505837625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150848683952850056337225083 226273025929275084505837625)
      ·
        refine ⟨169704769446956313379378219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226273025929275084505837625 169704769446956313379378219)
        ·
          refine ⟨254557154170434470069067329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169704769446956313379378219 254557154170434470069067329)
          ·
            refine ⟨190917865627825852551800497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254557154170434470069067329 190917865627825852551800497)
            ·
              refine ⟨143188399220869389413850373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190917865627825852551800497 143188399220869389413850373)
              ·
                refine ⟨26847824853913010515096945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143188399220869389413850373 26847824853913010515096945)
                ·
                  refine ⟨20135868640434757886322709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26847824853913010515096945 20135868640434757886322709)
                  ·
                    refine ⟨943868842520379275921377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20135868640434757886322709 943868842520379275921377)
                    ·
                      rfl

theorem cell22_2757267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 6].length) (baseStart_2757267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757267 prefixEnd_2757267 := by exact prefixLift 2757267
  have htrace : WordTrace (prefixWord ++ tailWord_2757267) baseStart_2757267 baseEnd_2757267 := by
    simpa [prefixWord, tailWord_2757267, baseEnd_2757267] using wordTrace_append hprefix tailTrace_2757267
  have hstable : (prefixWord ++ tailWord_2757267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757267).length < 2 ^ (prefixWord ++ tailWord_2757267).sum := by decide
  have hdescent : baseEnd_2757267 < baseStart_2757267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757299 : List Nat := [1, 1, 1, 2, 3, 4, 1, 4, 5]
def baseStart_2757299 : Nat := 118140960795 + 2757299 * 2 ^ 59
def prefixEnd_2757299 : Nat := 4983230072969 + 3 ^ 40 * 2757299 * 2
def baseEnd_2757299 : Nat := 314626598924780619707093

theorem tailTrace_2757299 : CollatzResearch.WordTrace tailWord_2757299 prefixEnd_2757299 314626598924780619707093 := by
  unfold tailWord_2757299
  simp only [CollatzResearch.WordTrace]
  refine ⟨100566956437784107023314951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67044637625189404682209967 100566956437784107023314951)
  ·
    refine ⟨150850434656676160534972427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100566956437784107023314951 150850434656676160534972427)
    ·
      refine ⟨226275651985014240802458641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150850434656676160534972427 226275651985014240802458641)
      ·
        refine ⟨169706738988760680601843981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226275651985014240802458641 169706738988760680601843981)
        ·
          refine ⟨63640027120785255225691493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169706738988760680601843981 63640027120785255225691493)
          ·
            refine ⟨11932505085147235354817155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63640027120785255225691493 11932505085147235354817155)
            ·
              refine ⟨17898757627720853032225733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11932505085147235354817155 17898757627720853032225733)
              ·
                refine ⟨3356017055197659943542325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17898757627720853032225733 3356017055197659943542325)
                ·
                  refine ⟨314626598924780619707093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3356017055197659943542325 314626598924780619707093)
                  ·
                    rfl

theorem cell22_2757299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 5].length) (baseStart_2757299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757299 prefixEnd_2757299 := by exact prefixLift 2757299
  have htrace : WordTrace (prefixWord ++ tailWord_2757299) baseStart_2757299 baseEnd_2757299 := by
    simpa [prefixWord, tailWord_2757299, baseEnd_2757299] using wordTrace_append hprefix tailTrace_2757299
  have hstable : (prefixWord ++ tailWord_2757299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757299).length < 2 ^ (prefixWord ++ tailWord_2757299).sum := by decide
  have hdescent : baseEnd_2757299 < baseStart_2757299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757316 : List Nat := [2, 3, 3, 1, 1, 2, 2, 3, 5]
def baseStart_2757316 : Nat := 118140960795 + 2757316 * 2 ^ 59
def prefixEnd_2757316 : Nat := 4983230072969 + 3 ^ 40 * 2757316 * 2
def baseEnd_2757316 : Nat := 314628538740586493815409

theorem tailTrace_2757316 : CollatzResearch.WordTrace tailWord_2757316 prefixEnd_2757316 314628538740586493815409 := by
  unfold tailWord_2757316
  simp only [CollatzResearch.WordTrace]
  refine ⟨50283788239361259463341901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67045050985815012617789201 50283788239361259463341901)
  ·
    refine ⟨18856420589760472298753213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50283788239361259463341901 18856420589760472298753213)
    ·
      refine ⟨7071157721160177112032455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18856420589760472298753213 7071157721160177112032455)
      ·
        refine ⟨10606736581740265668048683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7071157721160177112032455 10606736581740265668048683)
        ·
          refine ⟨15910104872610398502073025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10606736581740265668048683 15910104872610398502073025)
          ·
            refine ⟨11932578654457798876554769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15910104872610398502073025 11932578654457798876554769)
            ·
              refine ⟨8949433990843349157416077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11932578654457798876554769 8949433990843349157416077)
              ·
                refine ⟨3356037746566255934031029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8949433990843349157416077 3356037746566255934031029)
                ·
                  refine ⟨314628538740586493815409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3356037746566255934031029 314628538740586493815409)
                  ·
                    rfl

theorem cell22_2757316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_2757316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757316 prefixEnd_2757316 := by exact prefixLift 2757316
  have htrace : WordTrace (prefixWord ++ tailWord_2757316) baseStart_2757316 baseEnd_2757316 := by
    simpa [prefixWord, tailWord_2757316, baseEnd_2757316] using wordTrace_append hprefix tailTrace_2757316
  have hstable : (prefixWord ++ tailWord_2757316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757316).length < 2 ^ (prefixWord ++ tailWord_2757316).sum := by decide
  have hdescent : baseEnd_2757316 < baseStart_2757316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757329 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 3, 4]
def baseStart_2757329 : Nat := 118140960795 + 2757329 * 2 ^ 59
def prefixEnd_2757329 : Nat := 4983230072969 + 3 ^ 40 * 2757329 * 2
def baseEnd_2757329 : Nat := 943890066387431780871187

theorem tailTrace_2757329 : CollatzResearch.WordTrace tailWord_2757329 prefixEnd_2757329 943890066387431780871187 := by
  unfold tailWord_2757329
  simp only [CollatzResearch.WordTrace]
  refine ⟨100568050627675422146907041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67045367085116948097938027 100568050627675422146907041)
  ·
    refine ⟨75426037970756566610180281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100568050627675422146907041 75426037970756566610180281)
    ·
      refine ⟨56569528478067424957635211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75426037970756566610180281 56569528478067424957635211)
      ·
        refine ⟨84854292717101137436452817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56569528478067424957635211 84854292717101137436452817)
        ·
          refine ⟨63640719537825853077339613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84854292717101137436452817 63640719537825853077339613)
          ·
            refine ⟨23865269826684694904002355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63640719537825853077339613 23865269826684694904002355)
            ·
              refine ⟨35797904740027042356003533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23865269826684694904002355 35797904740027042356003533)
              ·
                refine ⟨13424214277510140883501325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35797904740027042356003533 13424214277510140883501325)
                ·
                  refine ⟨5034080354066302831312997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13424214277510140883501325 5034080354066302831312997)
                  ·
                    refine ⟨943890066387431780871187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5034080354066302831312997 943890066387431780871187)
                    ·
                      rfl

theorem cell22_2757329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_2757329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757329 prefixEnd_2757329 := by exact prefixLift 2757329
  have htrace : WordTrace (prefixWord ++ tailWord_2757329) baseStart_2757329 baseEnd_2757329 := by
    simpa [prefixWord, tailWord_2757329, baseEnd_2757329] using wordTrace_append hprefix tailTrace_2757329
  have hstable : (prefixWord ++ tailWord_2757329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757329).length < 2 ^ (prefixWord ++ tailWord_2757329).sum := by decide
  have hdescent : baseEnd_2757329 < baseStart_2757329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757361 : List Nat := [1, 2, 2, 2, 2, 2, 1, 6, 4]
def baseStart_2757361 : Nat := 118140960795 + 2757361 * 2 ^ 59
def prefixEnd_2757361 : Nat := 4983230072969 + 3 ^ 40 * 2757361 * 2
def baseEnd_2757361 : Nat := 314633673547131454690363

theorem tailTrace_2757361 : CollatzResearch.WordTrace tailWord_2757361 prefixEnd_2757361 314633673547131454690363 := by
  unfold tailWord_2757361
  simp only [CollatzResearch.WordTrace]
  refine ⟨100569217763559491612071937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67046145175706327741381291 100569217763559491612071937)
  ·
    refine ⟨75426913322669618709053953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100569217763559491612071937 75426913322669618709053953)
    ·
      refine ⟨56570184992002214031790465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75426913322669618709053953 56570184992002214031790465)
      ·
        refine ⟨42427638744001660523842849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56570184992002214031790465 42427638744001660523842849)
        ·
          refine ⟨31820729058001245392882137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42427638744001660523842849 31820729058001245392882137)
          ·
            refine ⟨23865546793500934044661603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31820729058001245392882137 23865546793500934044661603)
            ·
              refine ⟨35798320190251401066992405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23865546793500934044661603 35798320190251401066992405)
              ·
                refine ⟨1678046258918034425015269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35798320190251401066992405 1678046258918034425015269)
                ·
                  refine ⟨314633673547131454690363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1678046258918034425015269 314633673547131454690363)
                  ·
                    rfl

theorem cell22_2757361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 4].length) (baseStart_2757361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757361 prefixEnd_2757361 := by exact prefixLift 2757361
  have htrace : WordTrace (prefixWord ++ tailWord_2757361) baseStart_2757361 baseEnd_2757361 := by
    simpa [prefixWord, tailWord_2757361, baseEnd_2757361] using wordTrace_append hprefix tailTrace_2757361
  have hstable : (prefixWord ++ tailWord_2757361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757361).length < 2 ^ (prefixWord ++ tailWord_2757361).sum := by decide
  have hdescent : baseEnd_2757361 < baseStart_2757361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757468 : List Nat := [2, 2, 4, 2, 1, 1, 1, 4, 5]
def baseStart_2757468 : Nat := 118140960795 + 2757468 * 2 ^ 59
def prefixEnd_2757468 : Nat := 4983230072969 + 3 ^ 40 * 2757468 * 2
def baseEnd_2757468 : Nat := 314645882976027250548587

theorem tailTrace_2757468 : CollatzResearch.WordTrace tailWord_2757468 prefixEnd_2757468 314645882976027250548587 := by
  unfold tailWord_2757468
  simp only [CollatzResearch.WordTrace]
  refine ⟨50286560187085924443108529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67048746916114565924144705 50286560187085924443108529)
  ·
    refine ⟨37714920140314443332331397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50286560187085924443108529 37714920140314443332331397)
    ·
      refine ⟨7071547526308958124812137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37714920140314443332331397 7071547526308958124812137)
      ·
        refine ⟨5303660644731718593609103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7071547526308958124812137 5303660644731718593609103)
        ·
          refine ⟨7955490967097577890413655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5303660644731718593609103 7955490967097577890413655)
          ·
            refine ⟨11933236450646366835620483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7955490967097577890413655 11933236450646366835620483)
            ·
              refine ⟨17899854675969550253430725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11933236450646366835620483 17899854675969550253430725)
              ·
                refine ⟨3356222751744290672518261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17899854675969550253430725 3356222751744290672518261)
                ·
                  refine ⟨314645882976027250548587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3356222751744290672518261 314645882976027250548587)
                  ·
                    rfl

theorem cell22_2757468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_2757468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757468 prefixEnd_2757468 := by exact prefixLift 2757468
  have htrace : WordTrace (prefixWord ++ tailWord_2757468) baseStart_2757468 baseEnd_2757468 := by
    simpa [prefixWord, tailWord_2757468, baseEnd_2757468] using wordTrace_append hprefix tailTrace_2757468
  have hstable : (prefixWord ++ tailWord_2757468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757468).length < 2 ^ (prefixWord ++ tailWord_2757468).sum := by decide
  have hdescent : baseEnd_2757468 < baseStart_2757468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
