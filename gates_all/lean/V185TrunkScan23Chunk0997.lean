import V185TrunkScan23Chunk0996

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5904232 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 1, 9]
def baseStart_5904232 : Nat := 118140960795 + 5904232 * 2 ^ 59
def prefixEnd_5904232 : Nat := 4983230072969 + 3 ^ 40 * 5904232 * 2
def baseEnd_5904232 : Nat := 1010569637218949632948979

theorem tailTrace_5904232 : CollatzResearch.WordTrace tailWord_5904232 prefixEnd_5904232 1010569637218949632948979 := by
  unfold tailWord_5904232
  simp only [CollatzResearch.WordTrace]
  refine ⟨107672516172991650695433475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143563354897322200927244633 107672516172991650695433475)
  ·
    refine ⟨161508774259487476043150213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107672516172991650695433475 161508774259487476043150213)
    ·
      refine ⟨30282895173653901758090665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161508774259487476043150213 30282895173653901758090665)
      ·
        refine ⟨22712171380240426318567999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30282895173653901758090665 22712171380240426318567999)
        ·
          refine ⟨34068257070360639477851999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22712171380240426318567999 34068257070360639477851999)
          ·
            refine ⟨51102385605540959216777999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34068257070360639477851999 51102385605540959216777999)
            ·
              refine ⟨76653578408311438825166999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51102385605540959216777999 76653578408311438825166999)
              ·
                refine ⟨114980367612467158237750499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76653578408311438825166999 114980367612467158237750499)
                ·
                  refine ⟨172470551418700737356625749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114980367612467158237750499 172470551418700737356625749)
                  ·
                    refine ⟨1010569637218949632948979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 172470551418700737356625749 1010569637218949632948979)
                    ·
                      rfl

theorem cell23_5904232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_5904232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904232 prefixEnd_5904232 := by exact prefixLift 5904232
  have htrace : WordTrace (prefixWord ++ tailWord_5904232) baseStart_5904232 baseEnd_5904232 := by
    simpa [prefixWord, tailWord_5904232, baseEnd_5904232] using wordTrace_append hprefix tailTrace_5904232
  have hstable : (prefixWord ++ tailWord_5904232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904232).length < 2 ^ (prefixWord ++ tailWord_5904232).sum := by decide
  have hdescent : baseEnd_5904232 < baseStart_5904232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904242 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_5904242 : Nat := 118140960795 + 5904242 * 2 ^ 59
def prefixEnd_5904242 : Nat := 4983230072969 + 3 ^ 40 * 5904242 * 2
def baseEnd_5904242 : Nat := 3031714046463393859721891

theorem tailTrace_5904242 : CollatzResearch.WordTrace tailWord_5904242 prefixEnd_5904242 3031714046463393859721891 := by
  unfold tailWord_5904242
  simp only [CollatzResearch.WordTrace]
  refine ⟨53836349268986768274682745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143563598050631382065820653 53836349268986768274682745)
  ·
    refine ⟨40377261951740076206012059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53836349268986768274682745 40377261951740076206012059)
    ·
      refine ⟨60565892927610114309018089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40377261951740076206012059 60565892927610114309018089)
      ·
        refine ⟨45424419695707585731763567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60565892927610114309018089 45424419695707585731763567)
        ·
          refine ⟨68136629543561378597645351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45424419695707585731763567 68136629543561378597645351)
          ·
            refine ⟨102204944315342067896468027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68136629543561378597645351 102204944315342067896468027)
            ·
              refine ⟨153307416473013101844702041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102204944315342067896468027 153307416473013101844702041)
              ·
                refine ⟨114980562354759826383526531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153307416473013101844702041 114980562354759826383526531)
                ·
                  refine ⟨172470843532139739575289797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114980562354759826383526531 172470843532139739575289797)
                  ·
                    refine ⟨32338283162276201170366837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 172470843532139739575289797 32338283162276201170366837)
                    ·
                      refine ⟨3031714046463393859721891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32338283162276201170366837 3031714046463393859721891)
                      ·
                        rfl

theorem cell23_5904242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_5904242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904242 prefixEnd_5904242 := by exact prefixLift 5904242
  have htrace : WordTrace (prefixWord ++ tailWord_5904242) baseStart_5904242 baseEnd_5904242 := by
    simpa [prefixWord, tailWord_5904242, baseEnd_5904242] using wordTrace_append hprefix tailTrace_5904242
  have hstable : (prefixWord ++ tailWord_5904242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904242).length < 2 ^ (prefixWord ++ tailWord_5904242).sum := by decide
  have hdescent : baseEnd_5904242 < baseStart_5904242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904256 : List Nat := [2, 1, 1, 2, 1, 2, 4, 4, 1, 3, 2]
def baseStart_5904256 : Nat := 118140960795 + 5904256 * 2 ^ 59
def prefixEnd_5904256 : Nat := 4983230072969 + 3 ^ 40 * 5904256 * 2
def baseEnd_5904256 : Nat := 3031721235192556804946827

theorem tailTrace_5904256 : CollatzResearch.WordTrace tailWord_5904256 prefixEnd_5904256 3031721235192556804946827 := by
  unfold tailWord_5904256
  simp only [CollatzResearch.WordTrace]
  refine ⟨107672953848948176744870311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143563938465264235659827081 107672953848948176744870311)
  ·
    refine ⟨161509430773422265117305467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107672953848948176744870311 161509430773422265117305467)
    ·
      refine ⟨242264146160133397675958201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161509430773422265117305467 242264146160133397675958201)
      ·
        refine ⟨181698109620100048256968651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242264146160133397675958201 181698109620100048256968651)
        ·
          refine ⟨272547164430150072385452977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181698109620100048256968651 272547164430150072385452977)
          ·
            refine ⟨204410373322612554289089733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272547164430150072385452977 204410373322612554289089733)
            ·
              refine ⟨38326944997989853929204325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204410373322612554289089733 38326944997989853929204325)
              ·
                refine ⟨7186302187123097611725811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38326944997989853929204325 7186302187123097611725811)
                ·
                  refine ⟨10779453280684646417588717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7186302187123097611725811 10779453280684646417588717)
                  ·
                    refine ⟨4042294980256742406595769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10779453280684646417588717 4042294980256742406595769)
                    ·
                      refine ⟨3031721235192556804946827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4042294980256742406595769 3031721235192556804946827)
                      ·
                        rfl

theorem cell23_5904256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 1, 3, 2].length) (baseStart_5904256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904256 prefixEnd_5904256 := by exact prefixLift 5904256
  have htrace : WordTrace (prefixWord ++ tailWord_5904256) baseStart_5904256 baseEnd_5904256 := by
    simpa [prefixWord, tailWord_5904256, baseEnd_5904256] using wordTrace_append hprefix tailTrace_5904256
  have hstable : (prefixWord ++ tailWord_5904256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904256).length < 2 ^ (prefixWord ++ tailWord_5904256).sum := by decide
  have hdescent : baseEnd_5904256 < baseStart_5904256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904273 : List Nat := [1, 2, 2, 1, 1, 1, 8, 1, 1, 3, 2]
def baseStart_5904273 : Nat := 118140960795 + 5904273 * 2 ^ 59
def prefixEnd_5904273 : Nat := 4983230072969 + 3 ^ 40 * 5904273 * 2
def baseEnd_5904273 : Nat := 3031729964363683238434249

theorem tailTrace_5904273 : CollatzResearch.WordTrace tailWord_5904273 prefixEnd_5904273 3031729964363683238434249 := by
  unfold tailWord_5904273
  simp only [CollatzResearch.WordTrace]
  refine ⟨215346527738834765393109473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143564351825889843595406315 215346527738834765393109473)
  ·
    refine ⟨161509895804126074044832105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215346527738834765393109473 161509895804126074044832105)
    ·
      refine ⟨121132421853094555533624079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161509895804126074044832105 121132421853094555533624079)
      ·
        refine ⟨181698632779641833300436119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121132421853094555533624079 181698632779641833300436119)
        ·
          refine ⟨272547949169462749950654179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181698632779641833300436119 272547949169462749950654179)
          ·
            refine ⟨408821923754194124925981269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272547949169462749950654179 408821923754194124925981269)
            ·
              refine ⟨4790881918994462401476343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 408821923754194124925981269 4790881918994462401476343)
              ·
                refine ⟨7186322878491693602214515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4790881918994462401476343 7186322878491693602214515)
                ·
                  refine ⟨10779484317737540403321773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7186322878491693602214515 10779484317737540403321773)
                  ·
                    refine ⟨4042306619151577651245665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10779484317737540403321773 4042306619151577651245665)
                    ·
                      refine ⟨3031729964363683238434249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4042306619151577651245665 3031729964363683238434249)
                      ·
                        rfl

theorem cell23_5904273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 1, 3, 2].length) (baseStart_5904273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904273 prefixEnd_5904273 := by exact prefixLift 5904273
  have htrace : WordTrace (prefixWord ++ tailWord_5904273) baseStart_5904273 baseEnd_5904273 := by
    simpa [prefixWord, tailWord_5904273, baseEnd_5904273] using wordTrace_append hprefix tailTrace_5904273
  have hstable : (prefixWord ++ tailWord_5904273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904273).length < 2 ^ (prefixWord ++ tailWord_5904273).sum := by decide
  have hdescent : baseEnd_5904273 < baseStart_5904273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904309 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 7]
def baseStart_5904309 : Nat := 118140960795 + 5904309 * 2 ^ 59
def prefixEnd_5904309 : Nat := 4983230072969 + 3 ^ 40 * 5904309 * 2
def baseEnd_5904309 : Nat := 336860938851916121953787

theorem tailTrace_5904309 : CollatzResearch.WordTrace tailWord_5904309 prefixEnd_5904309 336860938851916121953787 := by
  unfold tailWord_5904309
  simp only [CollatzResearch.WordTrace]
  refine ⟨215347840766704343541419981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143565227177802895694279987 215347840766704343541419981)
  ·
    refine ⟨80755440287514128828032493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215347840766704343541419981 80755440287514128828032493)
    ·
      refine ⟨30283290107817798310512185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80755440287514128828032493 30283290107817798310512185)
      ·
        refine ⟨22712467580863348732884139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30283290107817798310512185 22712467580863348732884139)
        ·
          refine ⟨34068701371295023099326209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22712467580863348732884139 34068701371295023099326209)
          ·
            refine ⟨25551526028471267324494657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34068701371295023099326209 25551526028471267324494657)
            ·
              refine ⟨19163644521353450493370993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25551526028471267324494657 19163644521353450493370993)
              ·
                refine ⟨14372733391015087870028245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19163644521353450493370993 14372733391015087870028245)
                ·
                  refine ⟨336860938851916121953787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14372733391015087870028245 336860938851916121953787)
                  ·
                    rfl

theorem cell23_5904309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 7].length) (baseStart_5904309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904309 prefixEnd_5904309 := by exact prefixLift 5904309
  have htrace : WordTrace (prefixWord ++ tailWord_5904309) baseStart_5904309 baseEnd_5904309 := by
    simpa [prefixWord, tailWord_5904309, baseEnd_5904309] using wordTrace_append hprefix tailTrace_5904309
  have hstable : (prefixWord ++ tailWord_5904309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904309).length < 2 ^ (prefixWord ++ tailWord_5904309).sum := by decide
  have hdescent : baseEnd_5904309 < baseStart_5904309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904379 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 3]
def baseStart_5904379 : Nat := 118140960795 + 5904379 * 2 ^ 59
def prefixEnd_5904379 : Nat := 4983230072969 + 3 ^ 40 * 5904379 * 2
def baseEnd_5904379 : Nat := 3031784393313059823708761

theorem tailTrace_5904379 : CollatzResearch.WordTrace tailWord_5904379 prefixEnd_5904379 3031784393313059823708761 := by
  unfold tailWord_5904379
  simp only [CollatzResearch.WordTrace]
  refine ⟨215350393876450745496468191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143566929250967163664312127 215350393876450745496468191)
  ·
    refine ⟨323025590814676118244702287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215350393876450745496468191 323025590814676118244702287)
    ·
      refine ⟨484538386222014177367053431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323025590814676118244702287 484538386222014177367053431)
      ·
        refine ⟨726807579333021266050580147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484538386222014177367053431 726807579333021266050580147)
        ·
          refine ⟨1090211368999531899075870221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726807579333021266050580147 1090211368999531899075870221)
          ·
            refine ⟨408829263374824462153451333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1090211368999531899075870221 408829263374824462153451333)
            ·
              refine ⟨76655486882779586653772125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 408829263374824462153451333 76655486882779586653772125)
              ·
                refine ⟨28745807581042344995164547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76655486882779586653772125 28745807581042344995164547)
                ·
                  refine ⟨43118711371563517492746821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28745807581042344995164547 43118711371563517492746821)
                  ·
                    refine ⟨8084758382168159529890029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43118711371563517492746821 8084758382168159529890029)
                    ·
                      refine ⟨3031784393313059823708761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8084758382168159529890029 3031784393313059823708761)
                      ·
                        rfl

theorem cell23_5904379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 3].length) (baseStart_5904379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904379 prefixEnd_5904379 := by exact prefixLift 5904379
  have htrace : WordTrace (prefixWord ++ tailWord_5904379) baseStart_5904379 baseEnd_5904379 := by
    simpa [prefixWord, tailWord_5904379, baseEnd_5904379] using wordTrace_append hprefix tailTrace_5904379
  have hstable : (prefixWord ++ tailWord_5904379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904379).length < 2 ^ (prefixWord ++ tailWord_5904379).sum := by decide
  have hdescent : baseEnd_5904379 < baseStart_5904379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904396 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 2, 2, 3]
def baseStart_5904396 : Nat := 118140960795 + 5904396 * 2 ^ 59
def prefixEnd_5904396 : Nat := 4983230072969 + 3 ^ 40 * 5904396 * 2
def baseEnd_5904396 : Nat := 3031793122484186257196183

theorem tailTrace_5904396 : CollatzResearch.WordTrace tailWord_5904396 prefixEnd_5904396 3031793122484186257196183 := by
  unfold tailWord_5904396
  simp only [CollatzResearch.WordTrace]
  refine ⟨107675506958694578699918521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143567342611592771599891361 107675506958694578699918521)
  ·
    refine ⟨80756630219020934024938891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107675506958694578699918521 80756630219020934024938891)
    ·
      refine ⟨121134945328531401037408337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80756630219020934024938891 121134945328531401037408337)
      ·
        refine ⟨90851208996398550778056253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121134945328531401037408337 90851208996398550778056253)
        ·
          refine ⟨34069203373649456541771095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90851208996398550778056253 34069203373649456541771095)
          ·
            refine ⟨51103805060474184812656643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34069203373649456541771095 51103805060474184812656643)
            ·
              refine ⟨76655707590711277218984965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51103805060474184812656643 76655707590711277218984965)
              ·
                refine ⟨14372945173258364478559681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76655707590711277218984965 14372945173258364478559681)
                ·
                  refine ⟨10779708879943773358919761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14372945173258364478559681 10779708879943773358919761)
                  ·
                    refine ⟨8084781659957830019189821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10779708879943773358919761 8084781659957830019189821)
                    ·
                      refine ⟨3031793122484186257196183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8084781659957830019189821 3031793122484186257196183)
                      ·
                        rfl

theorem cell23_5904396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_5904396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904396 prefixEnd_5904396 := by exact prefixLift 5904396
  have htrace : WordTrace (prefixWord ++ tailWord_5904396) baseStart_5904396 baseEnd_5904396 := by
    simpa [prefixWord, tailWord_5904396, baseEnd_5904396] using wordTrace_append hprefix tailTrace_5904396
  have hstable : (prefixWord ++ tailWord_5904396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904396).length < 2 ^ (prefixWord ++ tailWord_5904396).sum := by decide
  have hdescent : baseEnd_5904396 < baseStart_5904396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904409 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 2, 5, 3]
def baseStart_5904409 : Nat := 118140960795 + 5904409 * 2 ^ 59
def prefixEnd_5904409 : Nat := 4983230072969 + 3 ^ 40 * 5904409 * 2
def baseEnd_5904409 : Nat := 3031799797732694706333623

theorem tailTrace_5904409 : CollatzResearch.WordTrace tailWord_5904409 prefixEnd_5904409 3031799797732694706333623 := by
  unfold tailWord_5904409
  simp only [CollatzResearch.WordTrace]
  refine ⟨215351488066342060620060281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143567658710894707080040187 215351488066342060620060281)
  ·
    refine ⟨161513616049756545465045211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215351488066342060620060281 161513616049756545465045211)
    ·
      refine ⟨242270424074634818197567817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161513616049756545465045211 242270424074634818197567817)
      ·
        refine ⟨181702818055976113648175863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242270424074634818197567817 181702818055976113648175863)
        ·
          refine ⟨272554227083964170472263795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181702818055976113648175863 272554227083964170472263795)
          ·
            refine ⟨408831340625946255708395693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272554227083964170472263795 408831340625946255708395693)
            ·
              refine ⟨153311752734729845890648385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 408831340625946255708395693 153311752734729845890648385)
              ·
                refine ⟨114983814551047384417986289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153311752734729845890648385 114983814551047384417986289)
                ·
                  refine ⟨86237860913285538313489717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114983814551047384417986289 86237860913285538313489717)
                  ·
                    refine ⟨8084799460620519216889661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86237860913285538313489717 8084799460620519216889661)
                    ·
                      refine ⟨3031799797732694706333623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8084799460620519216889661 3031799797732694706333623)
                      ·
                        rfl

theorem cell23_5904409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_5904409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904409 prefixEnd_5904409 := by exact prefixLift 5904409
  have htrace : WordTrace (prefixWord ++ tailWord_5904409) baseStart_5904409 baseEnd_5904409 := by
    simpa [prefixWord, tailWord_5904409, baseEnd_5904409] using wordTrace_append hprefix tailTrace_5904409
  have hstable : (prefixWord ++ tailWord_5904409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904409).length < 2 ^ (prefixWord ++ tailWord_5904409).sum := by decide
  have hdescent : baseEnd_5904409 < baseStart_5904409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904430 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_5904430 : Nat := 118140960795 + 5904430 * 2 ^ 59
def prefixEnd_5904430 : Nat := 4983230072969 + 3 ^ 40 * 5904430 * 2
def baseEnd_5904430 : Nat := 3031810580826439124171027

theorem tailTrace_5904430 : CollatzResearch.WordTrace tailWord_5904430 prefixEnd_5904430 3031810580826439124171027 := by
  unfold tailWord_5904430
  simp only [CollatzResearch.WordTrace]
  refine ⟨26919031749908247650821843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143568169332843987471049829 26919031749908247650821843)
  ·
    refine ⟨40378547624862371476232765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26919031749908247650821843 40378547624862371476232765)
    ·
      refine ⟨15141955359323389303587287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40378547624862371476232765 15141955359323389303587287)
      ·
        refine ⟨22712933038985083955380931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15141955359323389303587287 22712933038985083955380931)
        ·
          refine ⟨34069399558477625933071397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22712933038985083955380931 34069399558477625933071397)
          ·
            refine ⟨6388012417214554862450887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34069399558477625933071397 6388012417214554862450887)
            ·
              refine ⟨9582018625821832293676331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6388012417214554862450887 9582018625821832293676331)
              ·
                refine ⟨14373027938732748440514497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9582018625821832293676331 14373027938732748440514497)
                ·
                  refine ⟨10779770954049561330385873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14373027938732748440514497 10779770954049561330385873)
                  ·
                    refine ⟨8084828215537170997789405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10779770954049561330385873 8084828215537170997789405)
                    ·
                      refine ⟨3031810580826439124171027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8084828215537170997789405 3031810580826439124171027)
                      ·
                        rfl

theorem cell23_5904430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_5904430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904430 prefixEnd_5904430 := by exact prefixLift 5904430
  have htrace : WordTrace (prefixWord ++ tailWord_5904430) baseStart_5904430 baseEnd_5904430 := by
    simpa [prefixWord, tailWord_5904430, baseEnd_5904430] using wordTrace_append hprefix tailTrace_5904430
  have hstable : (prefixWord ++ tailWord_5904430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904430).length < 2 ^ (prefixWord ++ tailWord_5904430).sum := by decide
  have hdescent : baseEnd_5904430 < baseStart_5904430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904460 : List Nat := [2, 2, 1, 3, 1, 1, 4, 4, 1, 1, 3]
def baseStart_5904460 : Nat := 118140960795 + 5904460 * 2 ^ 59
def prefixEnd_5904460 : Nat := 4983230072969 + 3 ^ 40 * 5904460 * 2
def baseEnd_5904460 : Nat := 3031825985246074006795889

theorem tailTrace_5904460 : CollatzResearch.WordTrace tailWord_5904460 prefixEnd_5904460 3031825985246074006795889 := by
  unfold tailWord_5904460
  simp only [CollatzResearch.WordTrace]
  refine ⟨107676674094578648165083417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143568898792771530886777889 107676674094578648165083417)
  ·
    refine ⟨80757505570933986123812563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107676674094578648165083417 80757505570933986123812563)
    ·
      refine ⟨121136258356400979185718845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80757505570933986123812563 121136258356400979185718845)
      ·
        refine ⟨45426096883650367194644567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121136258356400979185718845 45426096883650367194644567)
        ·
          refine ⟨68139145325475550791966851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45426096883650367194644567 68139145325475550791966851)
          ·
            refine ⟨102208717988213326187950277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68139145325475550791966851 102208717988213326187950277)
            ·
              refine ⟨19164134622789998660240677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102208717988213326187950277 19164134622789998660240677)
              ·
                refine ⟨3593275241773124748795127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19164134622789998660240677 3593275241773124748795127)
                ·
                  refine ⟨5389912862659687123192691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593275241773124748795127 5389912862659687123192691)
                  ·
                    refine ⟨8084869293989530684789037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5389912862659687123192691 8084869293989530684789037)
                    ·
                      refine ⟨3031825985246074006795889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8084869293989530684789037 3031825985246074006795889)
                      ·
                        rfl

theorem cell23_5904460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_5904460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904460 prefixEnd_5904460 := by exact prefixLift 5904460
  have htrace : WordTrace (prefixWord ++ tailWord_5904460) baseStart_5904460 baseEnd_5904460 := by
    simpa [prefixWord, tailWord_5904460, baseEnd_5904460] using wordTrace_append hprefix tailTrace_5904460
  have hstable : (prefixWord ++ tailWord_5904460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904460).length < 2 ^ (prefixWord ++ tailWord_5904460).sum := by decide
  have hdescent : baseEnd_5904460 < baseStart_5904460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904489 : List Nat := [1, 2, 1, 1, 1, 5, 3, 9]
def baseStart_5904489 : Nat := 118140960795 + 5904489 * 2 ^ 59
def prefixEnd_5904489 : Nat := 4983230072969 + 3 ^ 40 * 5904489 * 2
def baseEnd_5904489 : Nat := 112290402821668681234565

theorem tailTrace_5904489 : CollatzResearch.WordTrace tailWord_5904489 prefixEnd_5904489 112290402821668681234565 := by
  unfold tailWord_5904489
  simp only [CollatzResearch.WordTrace]
  refine ⟨215354405906052234282972521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143569603937368156188648347 215354405906052234282972521)
  ·
    refine ⟨161515804429539175712229391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215354405906052234282972521 161515804429539175712229391)
    ·
      refine ⟨242273706644308763568344087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161515804429539175712229391 242273706644308763568344087)
      ·
        refine ⟨363410559966463145352516131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242273706644308763568344087 363410559966463145352516131)
        ·
          refine ⟨545115839949694718028774197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363410559966463145352516131 545115839949694718028774197)
          ·
            refine ⟨51104609995283879815197581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 545115839949694718028774197 51104609995283879815197581)
            ·
              refine ⟨19164228748231454930699093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51104609995283879815197581 19164228748231454930699093)
              ·
                refine ⟨112290402821668681234565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19164228748231454930699093 112290402821668681234565)
                ·
                  rfl

theorem cell23_5904489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 9].length) (baseStart_5904489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904489 prefixEnd_5904489 := by exact prefixLift 5904489
  have htrace : WordTrace (prefixWord ++ tailWord_5904489) baseStart_5904489 baseEnd_5904489 := by
    simpa [prefixWord, tailWord_5904489, baseEnd_5904489] using wordTrace_append hprefix tailTrace_5904489
  have hstable : (prefixWord ++ tailWord_5904489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904489).length < 2 ^ (prefixWord ++ tailWord_5904489).sum := by decide
  have hdescent : baseEnd_5904489 < baseStart_5904489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904503 : List Nat := [1, 1, 3, 1, 1, 5, 2, 3, 1, 2, 3]
def baseStart_5904503 : Nat := 118140960795 + 5904503 * 2 ^ 59
def prefixEnd_5904503 : Nat := 4983230072969 + 3 ^ 40 * 5904503 * 2
def baseEnd_5904503 : Nat := 3031848064914217338558191

theorem tailTrace_5904503 : CollatzResearch.WordTrace tailWord_5904503 prefixEnd_5904503 3031848064914217338558191 := by
  unfold tailWord_5904503
  simp only [CollatzResearch.WordTrace]
  refine ⟨215354916528001514673982163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143569944352001009782654775 215354916528001514673982163)
  ·
    refine ⟨323032374792002272010973245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215354916528001514673982163 323032374792002272010973245)
    ·
      refine ⟨121137140547000852004114967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323032374792002272010973245 121137140547000852004114967)
      ·
        refine ⟨181705710820501278006172451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121137140547000852004114967 181705710820501278006172451)
        ·
          refine ⟨272558566230751917009258677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181705710820501278006172451 272558566230751917009258677)
          ·
            refine ⟨25552365584132992219618001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 272558566230751917009258677 25552365584132992219618001)
            ·
              refine ⟨19164274188099744164713501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25552365584132992219618001 19164274188099744164713501)
              ·
                refine ⟨7186602820537404061767563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19164274188099744164713501 7186602820537404061767563)
                ·
                  refine ⟨10779904230806106092651345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7186602820537404061767563 10779904230806106092651345)
                  ·
                    refine ⟨8084928173104579569488509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10779904230806106092651345 8084928173104579569488509)
                    ·
                      refine ⟨3031848064914217338558191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8084928173104579569488509 3031848064914217338558191)
                      ·
                        rfl

theorem cell23_5904503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_5904503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904503 prefixEnd_5904503 := by exact prefixLift 5904503
  have htrace : WordTrace (prefixWord ++ tailWord_5904503) baseStart_5904503 baseEnd_5904503 := by
    simpa [prefixWord, tailWord_5904503, baseEnd_5904503] using wordTrace_append hprefix tailTrace_5904503
  have hstable : (prefixWord ++ tailWord_5904503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904503).length < 2 ^ (prefixWord ++ tailWord_5904503).sum := by decide
  have hdescent : baseEnd_5904503 < baseStart_5904503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904517 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 3, 2, 2]
def baseStart_5904517 : Nat := 118140960795 + 5904517 * 2 ^ 59
def prefixEnd_5904517 : Nat := 4983230072969 + 3 ^ 40 * 5904517 * 2
def baseEnd_5904517 : Nat := 3031855253643380283783127

theorem tailTrace_5904517 : CollatzResearch.WordTrace tailWord_5904517 prefixEnd_5904517 3031855253643380283783127 := by
  unfold tailWord_5904517
  simp only [CollatzResearch.WordTrace]
  refine ⟨215355427149950795064991805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143570284766633863376661203 215355427149950795064991805)
  ·
    refine ⟨80758285181231548149371927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215355427149950795064991805 80758285181231548149371927)
    ·
      refine ⟨121137427771847322224057891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80758285181231548149371927 121137427771847322224057891)
      ·
        refine ⟨181706141657770983336086837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121137427771847322224057891 181706141657770983336086837)
        ·
          refine ⟨17034950780416029687758141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181706141657770983336086837 17034950780416029687758141)
          ·
            refine ⟨6388106542656011132909303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17034950780416029687758141 6388106542656011132909303)
            ·
              refine ⟨9582159813984016699363955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6388106542656011132909303 9582159813984016699363955)
              ·
                refine ⟨14373239720976025049045933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9582159813984016699363955 14373239720976025049045933)
                ·
                  refine ⟨5389964895366009393392225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14373239720976025049045933 5389964895366009393392225)
                  ·
                    refine ⟨4042473671524507045044169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5389964895366009393392225 4042473671524507045044169)
                    ·
                      refine ⟨3031855253643380283783127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4042473671524507045044169 3031855253643380283783127)
                      ·
                        rfl

theorem cell23_5904517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 2, 2].length) (baseStart_5904517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904517 prefixEnd_5904517 := by exact prefixLift 5904517
  have htrace : WordTrace (prefixWord ++ tailWord_5904517) baseStart_5904517 baseEnd_5904517 := by
    simpa [prefixWord, tailWord_5904517, baseEnd_5904517] using wordTrace_append hprefix tailTrace_5904517
  have hstable : (prefixWord ++ tailWord_5904517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904517).length < 2 ^ (prefixWord ++ tailWord_5904517).sum := by decide
  have hdescent : baseEnd_5904517 < baseStart_5904517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904554 : List Nat := [3, 1, 5, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_5904554 : Nat := 118140960795 + 5904554 * 2 ^ 59
def prefixEnd_5904554 : Nat := 4983230072969 + 3 ^ 40 * 5904554 * 2
def baseEnd_5904554 : Nat := 3031874252427596639020457

theorem tailTrace_5904554 : CollatzResearch.WordTrace tailWord_5904554 prefixEnd_5904554 3031874252427596639020457 := by
  unfold tailWord_5904554
  simp only [CollatzResearch.WordTrace]
  refine ⟨53839194162704187596022179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143571184433877833589392477 53839194162704187596022179)
  ·
    refine ⟨80758791244056281394033269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53839194162704187596022179 80758791244056281394033269)
    ·
      refine ⟨7571136679130276380690619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80758791244056281394033269 7571136679130276380690619)
      ·
        refine ⟨11356705018695414571035929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7571136679130276380690619 11356705018695414571035929)
        ·
          refine ⟨8517528764021560928276947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11356705018695414571035929 8517528764021560928276947)
          ·
            refine ⟨12776293146032341392415421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8517528764021560928276947 12776293146032341392415421)
            ·
              refine ⟨4791109929762128022155783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12776293146032341392415421 4791109929762128022155783)
              ·
                refine ⟨7186664894643192033233675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4791109929762128022155783 7186664894643192033233675)
                ·
                  refine ⟨10779997341964788049850513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7186664894643192033233675 10779997341964788049850513)
                  ·
                    refine ⟨8084998006473591037387885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10779997341964788049850513 8084998006473591037387885)
                    ·
                      refine ⟨3031874252427596639020457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8084998006473591037387885 3031874252427596639020457)
                      ·
                        rfl

theorem cell23_5904554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_5904554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904554 prefixEnd_5904554 := by exact prefixLift 5904554
  have htrace : WordTrace (prefixWord ++ tailWord_5904554) baseStart_5904554 baseEnd_5904554 := by
    simpa [prefixWord, tailWord_5904554, baseEnd_5904554] using wordTrace_append hprefix tailTrace_5904554
  have hstable : (prefixWord ++ tailWord_5904554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904554).length < 2 ^ (prefixWord ++ tailWord_5904554).sum := by decide
  have hdescent : baseEnd_5904554 < baseStart_5904554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904573 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 5, 4, 2]
def baseStart_5904573 : Nat := 118140960795 + 5904573 * 2 ^ 59
def prefixEnd_5904573 : Nat := 4983230072969 + 3 ^ 40 * 5904573 * 2
def baseEnd_5904573 : Nat := 3031884008560032064682869

theorem tailTrace_5904573 : CollatzResearch.WordTrace tailWord_5904573 prefixEnd_5904573 3031884008560032064682869 := by
  unfold tailWord_5904573
  simp only [CollatzResearch.WordTrace]
  refine ⟨215357469637747916629030373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143571646425165277752686915 215357469637747916629030373)
  ·
    refine ⟨40379525557077734367943195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215357469637747916629030373 40379525557077734367943195)
    ·
      refine ⟨60569288335616601551914793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40379525557077734367943195 60569288335616601551914793)
      ·
        refine ⟨45426966251712451163936095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60569288335616601551914793 45426966251712451163936095)
        ·
          refine ⟨68140449377568676745904143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45426966251712451163936095 68140449377568676745904143)
          ·
            refine ⟨102210674066353015118856215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68140449377568676745904143 102210674066353015118856215)
            ·
              refine ⟨153316011099529522678284323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102210674066353015118856215 153316011099529522678284323)
              ·
                refine ⟨229974016649294284017426485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153316011099529522678284323 229974016649294284017426485)
                ·
                  refine ⟨21560064060871339126633733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 229974016649294284017426485 21560064060871339126633733)
                  ·
                    refine ⟨4042512011413376086243825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21560064060871339126633733 4042512011413376086243825)
                    ·
                      refine ⟨3031884008560032064682869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4042512011413376086243825 3031884008560032064682869)
                      ·
                        rfl

theorem cell23_5904573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_5904573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904573 prefixEnd_5904573 := by exact prefixLift 5904573
  have htrace : WordTrace (prefixWord ++ tailWord_5904573) baseStart_5904573 baseEnd_5904573 := by
    simpa [prefixWord, tailWord_5904573, baseEnd_5904573] using wordTrace_append hprefix tailTrace_5904573
  have hstable : (prefixWord ++ tailWord_5904573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904573).length < 2 ^ (prefixWord ++ tailWord_5904573).sum := by decide
  have hdescent : baseEnd_5904573 < baseStart_5904573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904590 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2]
def baseStart_5904590 : Nat := 118140960795 + 5904590 * 2 ^ 59
def prefixEnd_5904590 : Nat := 4983230072969 + 3 ^ 40 * 5904590 * 2
def baseEnd_5904590 : Nat := 3031892737731158498170291

theorem tailTrace_5904590 : CollatzResearch.WordTrace tailWord_5904590 prefixEnd_5904590 3031892737731158498170291 := by
  unfold tailWord_5904590
  simp only [CollatzResearch.WordTrace]
  refine ⟨26919761209835791066549903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143572059785790885688266149 26919761209835791066549903)
  ·
    refine ⟨40379641814753686599824855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26919761209835791066549903 40379641814753686599824855)
    ·
      refine ⟨60569462722130529899737283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40379641814753686599824855 60569462722130529899737283)
      ·
        refine ⟨90854194083195794849605925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60569462722130529899737283 90854194083195794849605925)
        ·
          refine ⟨17035161390599211534301111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90854194083195794849605925 17035161390599211534301111)
          ·
            refine ⟨25552742085898817301451667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17035161390599211534301111 25552742085898817301451667)
            ·
              refine ⟨38329113128848225952177501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25552742085898817301451667 38329113128848225952177501)
              ·
                refine ⟨14373417423318084732066563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38329113128848225952177501 14373417423318084732066563)
                ·
                  refine ⟨21560126134977127098099845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14373417423318084732066563 21560126134977127098099845)
                  ·
                    refine ⟨4042523650308211330893721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21560126134977127098099845 4042523650308211330893721)
                    ·
                      refine ⟨3031892737731158498170291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4042523650308211330893721 3031892737731158498170291)
                      ·
                        rfl

theorem cell23_5904590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_5904590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904590 prefixEnd_5904590 := by exact prefixLift 5904590
  have htrace : WordTrace (prefixWord ++ tailWord_5904590) baseStart_5904590 baseEnd_5904590 := by
    simpa [prefixWord, tailWord_5904590, baseEnd_5904590] using wordTrace_append hprefix tailTrace_5904590
  have hstable : (prefixWord ++ tailWord_5904590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904590).length < 2 ^ (prefixWord ++ tailWord_5904590).sum := by decide
  have hdescent : baseEnd_5904590 < baseStart_5904590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904611 : List Nat := [1, 1, 1, 8, 1, 2, 2, 1, 1, 3, 2]
def baseStart_5904611 : Nat := 118140960795 + 5904611 * 2 ^ 59
def prefixEnd_5904611 : Nat := 4983230072969 + 3 ^ 40 * 5904611 * 2
def baseEnd_5904611 : Nat := 3031903520824902916007695

theorem tailTrace_5904611 : CollatzResearch.WordTrace tailWord_5904611 prefixEnd_5904611 3031903520824902916007695 := by
  unfold tailWord_5904611
  simp only [CollatzResearch.WordTrace]
  refine ⟨215358855611610249118913687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143572570407740166079275791 215358855611610249118913687)
  ·
    refine ⟨323038283417415373678370531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215358855611610249118913687 323038283417415373678370531)
    ·
      refine ⟨484557425126123060517555797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323038283417415373678370531 484557425126123060517555797)
      ·
        refine ⟨5678407325696754615440107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 484557425126123060517555797 5678407325696754615440107)
        ·
          refine ⟨8517610988545131923160161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5678407325696754615440107 8517610988545131923160161)
          ·
            refine ⟨6388208241408848942370121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8517610988545131923160161 6388208241408848942370121)
            ·
              refine ⟨4791156181056636706777591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6388208241408848942370121 4791156181056636706777591)
              ·
                refine ⟨7186734271584955060166387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4791156181056636706777591 7186734271584955060166387)
                ·
                  refine ⟨10780101407377432590249581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7186734271584955060166387 10780101407377432590249581)
                  ·
                    refine ⟨4042538027766537221343593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10780101407377432590249581 4042538027766537221343593)
                    ·
                      refine ⟨3031903520824902916007695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4042538027766537221343593 3031903520824902916007695)
                      ·
                        rfl

theorem cell23_5904611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_5904611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904611 prefixEnd_5904611 := by exact prefixLift 5904611
  have htrace : WordTrace (prefixWord ++ tailWord_5904611) baseStart_5904611 baseEnd_5904611 := by
    simpa [prefixWord, tailWord_5904611, baseEnd_5904611] using wordTrace_append hprefix tailTrace_5904611
  have hstable : (prefixWord ++ tailWord_5904611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904611).length < 2 ^ (prefixWord ++ tailWord_5904611).sum := by decide
  have hdescent : baseEnd_5904611 < baseStart_5904611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904623 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 3]
def baseStart_5904623 : Nat := 118140960795 + 5904623 * 2 ^ 59
def prefixEnd_5904623 : Nat := 4983230072969 + 3 ^ 40 * 5904623 * 2
def baseEnd_5904623 : Nat := 3031909682592756869057639

theorem tailTrace_5904623 : CollatzResearch.WordTrace tailWord_5904623 prefixEnd_5904623 3031909682592756869057639 := by
  unfold tailWord_5904623
  simp only [CollatzResearch.WordTrace]
  refine ⟨215359293287566775168350523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143572862191711183445567015 215359293287566775168350523)
  ·
    refine ⟨323038939931350162752525785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215359293287566775168350523 323038939931350162752525785)
    ·
      refine ⟨242279204948512622064394339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323038939931350162752525785 242279204948512622064394339)
      ·
        refine ⟨363418807422768933096591509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242279204948512622064394339 363418807422768933096591509)
        ·
          refine ⟨17035256597942293738902727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 363418807422768933096591509 17035256597942293738902727)
          ·
            refine ⟨25552884896913440608354091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17035256597942293738902727 25552884896913440608354091)
            ·
              refine ⟨38329327345370160912531137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25552884896913440608354091 38329327345370160912531137)
              ·
                refine ⟨28746995509027620684398353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38329327345370160912531137 28746995509027620684398353)
                ·
                  refine ⟨21560246631770715513298765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28746995509027620684398353 21560246631770715513298765)
                  ·
                    refine ⟨8085092486914018317487037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21560246631770715513298765 8085092486914018317487037)
                    ·
                      refine ⟨3031909682592756869057639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8085092486914018317487037 3031909682592756869057639)
                      ·
                        rfl

theorem cell23_5904623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 3].length) (baseStart_5904623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904623 prefixEnd_5904623 := by exact prefixLift 5904623
  have htrace : WordTrace (prefixWord ++ tailWord_5904623) baseStart_5904623 baseEnd_5904623 := by
    simpa [prefixWord, tailWord_5904623, baseEnd_5904623] using wordTrace_append hprefix tailTrace_5904623
  have hstable : (prefixWord ++ tailWord_5904623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904623).length < 2 ^ (prefixWord ++ tailWord_5904623).sum := by decide
  have hdescent : baseEnd_5904623 < baseStart_5904623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904630 : List Nat := [5, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_5904630 : Nat := 118140960795 + 5904630 * 2 ^ 59
def prefixEnd_5904630 : Nat := 4983230072969 + 3 ^ 40 * 5904630 * 2
def baseEnd_5904630 : Nat := 336879252995259815741123

theorem tailTrace_5904630 : CollatzResearch.WordTrace tailWord_5904630 prefixEnd_5904630 336879252995259815741123 := by
  unfold tailWord_5904630
  simp only [CollatzResearch.WordTrace]
  refine ⟨13459971787408838460240959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143573032399027610242570229 13459971787408838460240959)
  ·
    refine ⟨20189957681113257690361439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13459971787408838460240959 20189957681113257690361439)
    ·
      refine ⟨30284936521669886535542159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20189957681113257690361439 30284936521669886535542159)
      ·
        refine ⟨45427404782504829803313239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30284936521669886535542159 45427404782504829803313239)
        ·
          refine ⟨68141107173757244704969859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45427404782504829803313239 68141107173757244704969859)
          ·
            refine ⟨102211660760635867057454789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68141107173757244704969859 102211660760635867057454789)
            ·
              refine ⟨19164686392619225073272773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102211660760635867057454789 19164686392619225073272773)
              ·
                refine ⟨3593378698616104701238645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19164686392619225073272773 3593378698616104701238645)
                ·
                  refine ⟨336879252995259815741123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3593378698616104701238645 336879252995259815741123)
                  ·
                    rfl

theorem cell23_5904630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_5904630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904630 prefixEnd_5904630 := by exact prefixLift 5904630
  have htrace : WordTrace (prefixWord ++ tailWord_5904630) baseStart_5904630 baseEnd_5904630 := by
    simpa [prefixWord, tailWord_5904630, baseEnd_5904630] using wordTrace_append hprefix tailTrace_5904630
  have hstable : (prefixWord ++ tailWord_5904630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904630).length < 2 ^ (prefixWord ++ tailWord_5904630).sum := by decide
  have hdescent : baseEnd_5904630 < baseStart_5904630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904633 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 2, 5, 2]
def baseStart_5904633 : Nat := 118140960795 + 5904633 * 2 ^ 59
def prefixEnd_5904633 : Nat := 4983230072969 + 3 ^ 40 * 5904633 * 2
def baseEnd_5904633 : Nat := 3031914817399301829932593

theorem tailTrace_5904633 : CollatzResearch.WordTrace tailWord_5904633 prefixEnd_5904633 3031914817399301829932593 := by
  unfold tailWord_5904633
  simp only [CollatzResearch.WordTrace]
  refine ⟨215359658017530546876214553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143573105345020364584143035 215359658017530546876214553)
  ·
    refine ⟨161519743513147910157160915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215359658017530546876214553 161519743513147910157160915)
    ·
      refine ⟨242279615269721865235741373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161519743513147910157160915 242279615269721865235741373)
      ·
        refine ⟨90854855726145699463403015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242279615269721865235741373 90854855726145699463403015)
        ·
          refine ⟨136282283589218549195104523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90854855726145699463403015 136282283589218549195104523)
          ·
            refine ⟨204423425383827823792656785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136282283589218549195104523 204423425383827823792656785)
            ·
              refine ⟨153317569037870867844492589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204423425383827823792656785 153317569037870867844492589)
              ·
                refine ⟨57494088389201575441684721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153317569037870867844492589 57494088389201575441684721)
                ·
                  refine ⟨43120566291901181581263541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57494088389201575441684721 43120566291901181581263541)
                  ·
                    refine ⟨4042553089865735773243457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43120566291901181581263541 4042553089865735773243457)
                    ·
                      refine ⟨3031914817399301829932593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4042553089865735773243457 3031914817399301829932593)
                      ·
                        rfl

theorem cell23_5904633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_5904633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904633 prefixEnd_5904633 := by exact prefixLift 5904633
  have htrace : WordTrace (prefixWord ++ tailWord_5904633) baseStart_5904633 baseEnd_5904633 := by
    simpa [prefixWord, tailWord_5904633, baseEnd_5904633] using wordTrace_append hprefix tailTrace_5904633
  have hstable : (prefixWord ++ tailWord_5904633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904633).length < 2 ^ (prefixWord ++ tailWord_5904633).sum := by decide
  have hdescent : baseEnd_5904633 < baseStart_5904633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904663 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 4]
def baseStart_5904663 : Nat := 118140960795 + 5904663 * 2 ^ 59
def prefixEnd_5904663 : Nat := 4983230072969 + 3 ^ 40 * 5904663 * 2
def baseEnd_5904663 : Nat := 3031930221818936712557455

theorem tailTrace_5904663 : CollatzResearch.WordTrace tailWord_5904663 prefixEnd_5904663 3031930221818936712557455 := by
  unfold tailWord_5904663
  simp only [CollatzResearch.WordTrace]
  refine ⟨215360752207421861999806643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143573834804947907999871095 215360752207421861999806643)
  ·
    refine ⟨323041128311132792999709965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215360752207421861999806643 323041128311132792999709965)
    ·
      refine ⟨121140423116674797374891237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323041128311132792999709965 121140423116674797374891237)
      ·
        refine ⟨22713829334376524507792107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121140423116674797374891237 22713829334376524507792107)
        ·
          refine ⟨34070744001564786761688161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22713829334376524507792107 34070744001564786761688161)
          ·
            refine ⟨25553058001173590071266121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34070744001564786761688161 25553058001173590071266121)
            ·
              refine ⟨19164793500880192553449591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25553058001173590071266121 19164793500880192553449591)
              ·
                refine ⟨28747190251320288830174387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19164793500880192553449591 28747190251320288830174387)
                ·
                  refine ⟨43120785376980433245261581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28747190251320288830174387 43120785376980433245261581)
                  ·
                    refine ⟨16170294516367662466973093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43120785376980433245261581 16170294516367662466973093)
                    ·
                      refine ⟨3031930221818936712557455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16170294516367662466973093 3031930221818936712557455)
                      ·
                        rfl

theorem cell23_5904663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_5904663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904663 prefixEnd_5904663 := by exact prefixLift 5904663
  have htrace : WordTrace (prefixWord ++ tailWord_5904663) baseStart_5904663 baseEnd_5904663 := by
    simpa [prefixWord, tailWord_5904663, baseEnd_5904663] using wordTrace_append hprefix tailTrace_5904663
  have hstable : (prefixWord ++ tailWord_5904663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904663).length < 2 ^ (prefixWord ++ tailWord_5904663).sum := by decide
  have hdescent : baseEnd_5904663 < baseStart_5904663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904673 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 5, 4]
def baseStart_5904673 : Nat := 118140960795 + 5904673 * 2 ^ 59
def prefixEnd_5904673 : Nat := 4983230072969 + 3 ^ 40 * 5904673 * 2
def baseEnd_5904673 : Nat := 1010645118875160557810803

theorem tailTrace_5904673 : CollatzResearch.WordTrace tailWord_5904673 prefixEnd_5904673 1010645118875160557810803 := by
  unfold tailWord_5904673
  simp only [CollatzResearch.WordTrace]
  refine ⟨215361116937385633707670673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143574077958257089138447115 215361116937385633707670673)
  ·
    refine ⟨161520837703039225280753005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215361116937385633707670673 161520837703039225280753005)
    ·
      refine ⟨60570314138639709480282377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161520837703039225280753005 60570314138639709480282377)
      ·
        refine ⟨45427735603979782110211783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60570314138639709480282377 45427735603979782110211783)
        ·
          refine ⟨68141603405969673165317675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45427735603979782110211783 68141603405969673165317675)
          ·
            refine ⟨102212405108954509747976513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68141603405969673165317675 102212405108954509747976513)
            ·
              refine ⟨76659303831715882310982385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102212405108954509747976513 76659303831715882310982385)
              ·
                refine ⟨57494477873786911733236789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76659303831715882310982385 57494477873786911733236789)
                ·
                  refine ⟨5390107300667522974990949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57494477873786911733236789 5390107300667522974990949)
                  ·
                    refine ⟨1010645118875160557810803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5390107300667522974990949 1010645118875160557810803)
                    ·
                      rfl

theorem cell23_5904673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_5904673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904673 prefixEnd_5904673 := by exact prefixLift 5904673
  have htrace : WordTrace (prefixWord ++ tailWord_5904673) baseStart_5904673 baseEnd_5904673 := by
    simpa [prefixWord, tailWord_5904673, baseEnd_5904673] using wordTrace_append hprefix tailTrace_5904673
  have hstable : (prefixWord ++ tailWord_5904673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904673).length < 2 ^ (prefixWord ++ tailWord_5904673).sum := by decide
  have hdescent : baseEnd_5904673 < baseStart_5904673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904703 : List Nat := [1, 1, 2, 2, 4, 1, 3, 3, 6]
def baseStart_5904703 : Nat := 118140960795 + 5904703 * 2 ^ 59
def prefixEnd_5904703 : Nat := 4983230072969 + 3 ^ 40 * 5904703 * 2
def baseEnd_5904703 : Nat := 336883417893901839561919

theorem tailTrace_5904703 : CollatzResearch.WordTrace tailWord_5904703 prefixEnd_5904703 336883417893901839561919 := by
  unfold tailWord_5904703
  simp only [CollatzResearch.WordTrace]
  refine ⟨215362211127276948831262763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143574807418184632554175175 215362211127276948831262763)
  ·
    refine ⟨323043316690915423246894145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215362211127276948831262763 323043316690915423246894145)
    ·
      refine ⟨242282487518186567435170609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323043316690915423246894145 242282487518186567435170609)
      ·
        refine ⟨181711865638639925576377957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242282487518186567435170609 181711865638639925576377957)
        ·
          refine ⟨34070974807244986045570867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181711865638639925576377957 34070974807244986045570867)
          ·
            refine ⟨51106462210867479068356301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34070974807244986045570867 51106462210867479068356301)
            ·
              refine ⟨19164923329075304650633613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51106462210867479068356301 19164923329075304650633613)
              ·
                refine ⟨7186846248403239243987605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19164923329075304650633613 7186846248403239243987605)
                ·
                  refine ⟨336883417893901839561919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7186846248403239243987605 336883417893901839561919)
                  ·
                    rfl

theorem cell23_5904703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 6].length) (baseStart_5904703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904703 prefixEnd_5904703 := by exact prefixLift 5904703
  have htrace : WordTrace (prefixWord ++ tailWord_5904703) baseStart_5904703 baseEnd_5904703 := by
    simpa [prefixWord, tailWord_5904703, baseEnd_5904703] using wordTrace_append hprefix tailTrace_5904703
  have hstable : (prefixWord ++ tailWord_5904703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904703).length < 2 ^ (prefixWord ++ tailWord_5904703).sum := by decide
  have hdescent : baseEnd_5904703 < baseStart_5904703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904747 : List Nat := [1, 1, 1, 1, 2, 2, 2, 8, 1, 1, 3]
def baseStart_5904747 : Nat := 118140960795 + 5904747 * 2 ^ 59
def prefixEnd_5904747 : Nat := 4983230072969 + 3 ^ 40 * 5904747 * 2
def baseEnd_5904747 : Nat := 3031973354193914383907069

theorem tailTrace_5904747 : CollatzResearch.WordTrace tailWord_5904747 prefixEnd_5904747 3031973354193914383907069 := by
  unfold tailWord_5904747
  simp only [CollatzResearch.WordTrace]
  refine ⟨215363815939117544345864495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143575877292745029563909663 215363815939117544345864495)
  ·
    refine ⟨323045723908676316518796743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215363815939117544345864495 323045723908676316518796743)
    ·
      refine ⟨484568585863014474778195115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323045723908676316518796743 484568585863014474778195115)
      ·
        refine ⟨726852878794521712167292673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484568585863014474778195115 726852878794521712167292673)
        ·
          refine ⟨545139659095891284125469505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 726852878794521712167292673 545139659095891284125469505)
          ·
            refine ⟨408854744321918463094102129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 545139659095891284125469505 408854744321918463094102129)
            ·
              refine ⟨306641058241438847320576597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408854744321918463094102129 306641058241438847320576597)
              ·
                refine ⟨3593449901266861492038007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 306641058241438847320576597 3593449901266861492038007)
                ·
                  refine ⟨5390174851900292238057011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593449901266861492038007 5390174851900292238057011)
                  ·
                    refine ⟨8085262277850438357085517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5390174851900292238057011 8085262277850438357085517)
                    ·
                      refine ⟨3031973354193914383907069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8085262277850438357085517 3031973354193914383907069)
                      ·
                        rfl

theorem cell23_5904747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 1, 1, 3].length) (baseStart_5904747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904747 prefixEnd_5904747 := by exact prefixLift 5904747
  have htrace : WordTrace (prefixWord ++ tailWord_5904747) baseStart_5904747 baseEnd_5904747 := by
    simpa [prefixWord, tailWord_5904747, baseEnd_5904747] using wordTrace_append hprefix tailTrace_5904747
  have hstable : (prefixWord ++ tailWord_5904747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904747).length < 2 ^ (prefixWord ++ tailWord_5904747).sum := by decide
  have hdescent : baseEnd_5904747 < baseStart_5904747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904763 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 1, 6]
def baseStart_5904763 : Nat := 118140960795 + 5904763 * 2 ^ 59
def prefixEnd_5904763 : Nat := 4983230072969 + 3 ^ 40 * 5904763 * 2
def baseEnd_5904763 : Nat := 1010660523294795440435665

theorem tailTrace_5904763 : CollatzResearch.WordTrace tailWord_5904763 prefixEnd_5904763 1010660523294795440435665 := by
  unfold tailWord_5904763
  simp only [CollatzResearch.WordTrace]
  refine ⟨215364399507059579078446943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143576266338039719385631295 215364399507059579078446943)
  ·
    refine ⟨323046599260589368617670415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215364399507059579078446943 323046599260589368617670415)
    ·
      refine ⟨484569898890884052926505623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323046599260589368617670415 484569898890884052926505623)
      ·
        refine ⟨726854848336326079389758435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484569898890884052926505623 726854848336326079389758435)
        ·
          refine ⟨1090282272504489119084637653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726854848336326079389758435 1090282272504489119084637653)
          ·
            refine ⟨25553490761823963728546195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1090282272504489119084637653 25553490761823963728546195)
            ·
              refine ⟨38330236142735945592819293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25553490761823963728546195 38330236142735945592819293)
              ·
                refine ⟨14373838553525979597307235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38330236142735945592819293 14373838553525979597307235)
                ·
                  refine ⟨21560757830288969395960853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14373838553525979597307235 21560757830288969395960853)
                  ·
                    refine ⟨1010660523294795440435665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21560757830288969395960853 1010660523294795440435665)
                    ·
                      rfl

theorem cell23_5904763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 6].length) (baseStart_5904763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904763 prefixEnd_5904763 := by exact prefixLift 5904763
  have htrace : WordTrace (prefixWord ++ tailWord_5904763) baseStart_5904763 baseEnd_5904763 := by
    simpa [prefixWord, tailWord_5904763, baseEnd_5904763] using wordTrace_append hprefix tailTrace_5904763
  have hstable : (prefixWord ++ tailWord_5904763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904763).length < 2 ^ (prefixWord ++ tailWord_5904763).sum := by decide
  have hdescent : baseEnd_5904763 < baseStart_5904763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904797 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 4, 4]
def baseStart_5904797 : Nat := 118140960795 + 5904797 * 2 ^ 59
def prefixEnd_5904797 : Nat := 4983230072969 + 3 ^ 40 * 5904797 * 2
def baseEnd_5904797 : Nat := 1010666342742213062760613

theorem tailTrace_5904797 : CollatzResearch.WordTrace tailWord_5904797 prefixEnd_5904797 1010666342742213062760613 := by
  unfold tailWord_5904797
  simp only [CollatzResearch.WordTrace]
  refine ⟨215365639588936402885184645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143577093059290935256789763 215365639588936402885184645)
  ·
    refine ⟨40381057422925575540972121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215365639588936402885184645 40381057422925575540972121)
    ·
      refine ⟨30285793067194181655729091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40381057422925575540972121 30285793067194181655729091)
      ·
        refine ⟨45428689600791272483593637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30285793067194181655729091 45428689600791272483593637)
        ·
          refine ⟨8517879300148363590673807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45428689600791272483593637 8517879300148363590673807)
          ·
            refine ⟨12776818950222545386010711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8517879300148363590673807 12776818950222545386010711)
            ·
              refine ⟨19165228425333818079016067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12776818950222545386010711 19165228425333818079016067)
              ·
                refine ⟨28747842638000727118524101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19165228425333818079016067 28747842638000727118524101)
                ·
                  refine ⟨5390220494625136334723269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28747842638000727118524101 5390220494625136334723269)
                  ·
                    refine ⟨1010666342742213062760613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5390220494625136334723269 1010666342742213062760613)
                    ·
                      rfl

theorem cell23_5904797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_5904797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904797 prefixEnd_5904797 := by exact prefixLift 5904797
  have htrace : WordTrace (prefixWord ++ tailWord_5904797) baseStart_5904797 baseEnd_5904797 := by
    simpa [prefixWord, tailWord_5904797, baseEnd_5904797] using wordTrace_append hprefix tailTrace_5904797
  have hstable : (prefixWord ++ tailWord_5904797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904797).length < 2 ^ (prefixWord ++ tailWord_5904797).sum := by decide
  have hdescent : baseEnd_5904797 < baseStart_5904797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904817 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 1, 2, 4]
def baseStart_5904817 : Nat := 118140960795 + 5904817 * 2 ^ 59
def prefixEnd_5904817 : Nat := 4983230072969 + 3 ^ 40 * 5904817 * 2
def baseEnd_5904817 : Nat := 3032009297839729110031747

theorem tailTrace_5904817 : CollatzResearch.WordTrace tailWord_5904817 prefixEnd_5904817 3032009297839729110031747 := by
  unfold tailWord_5904817
  simp only [CollatzResearch.WordTrace]
  refine ⟨215366369048863946300912705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143577579365909297533941803 215366369048863946300912705)
  ·
    refine ⟨161524776786647959725684529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215366369048863946300912705 161524776786647959725684529)
    ·
      refine ⟨121143582589985969794263397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161524776786647959725684529 121143582589985969794263397)
      ·
        refine ⟨22714421735622369336424387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121143582589985969794263397 22714421735622369336424387)
        ·
          refine ⟨34071632603433554004636581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22714421735622369336424387 34071632603433554004636581)
          ·
            refine ⟨6388431113143791375869359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34071632603433554004636581 6388431113143791375869359)
            ·
              refine ⟨9582646669715687063804039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6388431113143791375869359 9582646669715687063804039)
              ·
                refine ⟨14373970004573530595706059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9582646669715687063804039 14373970004573530595706059)
                ·
                  refine ⟨21560955006860295893559089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14373970004573530595706059 21560955006860295893559089)
                  ·
                    refine ⟨16170716255145221920169317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21560955006860295893559089 16170716255145221920169317)
                    ·
                      refine ⟨3032009297839729110031747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16170716255145221920169317 3032009297839729110031747)
                      ·
                        rfl

theorem cell23_5904817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_5904817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904817 prefixEnd_5904817 := by exact prefixLift 5904817
  have htrace : WordTrace (prefixWord ++ tailWord_5904817) baseStart_5904817 baseEnd_5904817 := by
    simpa [prefixWord, tailWord_5904817, baseEnd_5904817] using wordTrace_append hprefix tailTrace_5904817
  have hstable : (prefixWord ++ tailWord_5904817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904817).length < 2 ^ (prefixWord ++ tailWord_5904817).sum := by decide
  have hdescent : baseEnd_5904817 < baseStart_5904817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904843 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 4]
def baseStart_5904843 : Nat := 118140960795 + 5904843 * 2 ^ 59
def prefixEnd_5904843 : Nat := 4983230072969 + 3 ^ 40 * 5904843 * 2
def baseEnd_5904843 : Nat := 3032022648336746008306627

theorem tailTrace_5904843 : CollatzResearch.WordTrace tailWord_5904843 prefixEnd_5904843 3032022648336746008306627 := by
  unfold tailWord_5904843
  simp only [CollatzResearch.WordTrace]
  refine ⟨215367317346769752741359183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143578211564513168494239455 215367317346769752741359183)
  ·
    refine ⟨323050976020154629112038775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215367317346769752741359183 323050976020154629112038775)
    ·
      refine ⟨484576464030231943668058163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323050976020154629112038775 484576464030231943668058163)
      ·
        refine ⟨726864696045347915502087245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484576464030231943668058163 726864696045347915502087245)
        ·
          refine ⟨272574261017005468313282717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 726864696045347915502087245 272574261017005468313282717)
          ·
            refine ⟨102215347881377050617481019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272574261017005468313282717 102215347881377050617481019)
            ·
              refine ⟨153323021822065575926221529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102215347881377050617481019 153323021822065575926221529)
              ·
                refine ⟨114992266366549181944666147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153323021822065575926221529 114992266366549181944666147)
                ·
                  refine ⟨172488399549823772916999221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114992266366549181944666147 172488399549823772916999221)
                  ·
                    refine ⟨16170787457795978710968677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 172488399549823772916999221 16170787457795978710968677)
                    ·
                      refine ⟨3032022648336746008306627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16170787457795978710968677 3032022648336746008306627)
                      ·
                        rfl

theorem cell23_5904843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 4].length) (baseStart_5904843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904843 prefixEnd_5904843 := by exact prefixLift 5904843
  have htrace : WordTrace (prefixWord ++ tailWord_5904843) baseStart_5904843 baseEnd_5904843 := by
    simpa [prefixWord, tailWord_5904843, baseEnd_5904843] using wordTrace_append hprefix tailTrace_5904843
  have hstable : (prefixWord ++ tailWord_5904843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904843).length < 2 ^ (prefixWord ++ tailWord_5904843).sum := by decide
  have hdescent : baseEnd_5904843 < baseStart_5904843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904854 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_5904854 : Nat := 118140960795 + 5904854 * 2 ^ 59
def prefixEnd_5904854 : Nat := 4983230072969 + 3 ^ 40 * 5904854 * 2
def baseEnd_5904854 : Nat := 3032028296623945465269077

theorem tailTrace_5904854 : CollatzResearch.WordTrace tailWord_5904854 prefixEnd_5904854 3032028296623945465269077 := by
  unfold tailWord_5904854
  simp only [CollatzResearch.WordTrace]
  refine ⟨13460482409358118851250601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143578479033153267746673077 13460482409358118851250601)
  ·
    refine ⟨10095361807018589138437951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13460482409358118851250601 10095361807018589138437951)
    ·
      refine ⟨15143042710527883707656927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10095361807018589138437951 15143042710527883707656927)
      ·
        refine ⟨22714564065791825561485391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15143042710527883707656927 22714564065791825561485391)
        ·
          refine ⟨34071846098687738342228087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22714564065791825561485391 34071846098687738342228087)
          ·
            refine ⟨51107769148031607513342131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34071846098687738342228087 51107769148031607513342131)
            ·
              refine ⟨76661653722047411270013197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51107769148031607513342131 76661653722047411270013197)
              ·
                refine ⟨28748120145767779226254949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76661653722047411270013197 28748120145767779226254949)
                ·
                  refine ⟨5390272527331458604922803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28748120145767779226254949 5390272527331458604922803)
                  ·
                    refine ⟨8085408790997187907384205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5390272527331458604922803 8085408790997187907384205)
                    ·
                      refine ⟨3032028296623945465269077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8085408790997187907384205 3032028296623945465269077)
                      ·
                        rfl

theorem cell23_5904854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_5904854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904854 prefixEnd_5904854 := by exact prefixLift 5904854
  have htrace : WordTrace (prefixWord ++ tailWord_5904854) baseStart_5904854 baseEnd_5904854 := by
    simpa [prefixWord, tailWord_5904854, baseEnd_5904854] using wordTrace_append hprefix tailTrace_5904854
  have hstable : (prefixWord ++ tailWord_5904854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904854).length < 2 ^ (prefixWord ++ tailWord_5904854).sum := by decide
  have hdescent : baseEnd_5904854 < baseStart_5904854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904883 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 9]
def baseStart_5904883 : Nat := 118140960795 + 5904883 * 2 ^ 59
def prefixEnd_5904883 : Nat := 4983230072969 + 3 ^ 40 * 5904883 * 2
def baseEnd_5904883 : Nat := 336893687506991761311827

theorem tailTrace_5904883 : CollatzResearch.WordTrace tailWord_5904883 prefixEnd_5904883 336893687506991761311827 := by
  unfold tailWord_5904883
  simp only [CollatzResearch.WordTrace]
  refine ⟨215368776266624839572815303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143579184177749893048543535 215368776266624839572815303)
  ·
    refine ⟨323053164399937259359222955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215368776266624839572815303 323053164399937259359222955)
    ·
      refine ⟨484579746599905889038834433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323053164399937259359222955 484579746599905889038834433)
      ·
        refine ⟨363434809949929416779125825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484579746599905889038834433 363434809949929416779125825)
        ·
          refine ⟨272576107462447062584344369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363434809949929416779125825 272576107462447062584344369)
          ·
            refine ⟨204432080596835296938258277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272576107462447062584344369 204432080596835296938258277)
            ·
              refine ⟨38331015111906618175923427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204432080596835296938258277 38331015111906618175923427)
              ·
                refine ⟨57496522667859927263885141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38331015111906618175923427 57496522667859927263885141)
                ·
                  refine ⟨336893687506991761311827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57496522667859927263885141 336893687506991761311827)
                  ·
                    rfl

theorem cell23_5904883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 9].length) (baseStart_5904883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904883 prefixEnd_5904883 := by exact prefixLift 5904883
  have htrace : WordTrace (prefixWord ++ tailWord_5904883) baseStart_5904883 baseEnd_5904883 := by
    simpa [prefixWord, tailWord_5904883, baseEnd_5904883] using wordTrace_append hprefix tailTrace_5904883
  have hstable : (prefixWord ++ tailWord_5904883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904883).length < 2 ^ (prefixWord ++ tailWord_5904883).sum := by decide
  have hdescent : baseEnd_5904883 < baseStart_5904883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904917 : List Nat := [1, 3, 2, 1, 3, 1, 3, 4, 5]
def baseStart_5904917 : Nat := 118140960795 + 5904917 * 2 ^ 59
def prefixEnd_5904917 : Nat := 4983230072969 + 3 ^ 40 * 5904917 * 2
def baseEnd_5904917 : Nat := 336895627322797635420143

theorem tailTrace_5904917 : CollatzResearch.WordTrace tailWord_5904917 prefixEnd_5904917 336895627322797635420143 := by
  unfold tailWord_5904917
  simp only [CollatzResearch.WordTrace]
  refine ⟨215370016348501663379553005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143580010899001108919702003 215370016348501663379553005)
  ·
    refine ⟨80763756130688123767332377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215370016348501663379553005 80763756130688123767332377)
    ·
      refine ⟨60572817098016092825499283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80763756130688123767332377 60572817098016092825499283)
      ·
        refine ⟨90859225647024139238248925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60572817098016092825499283 90859225647024139238248925)
        ·
          refine ⟨34072209617634052214343347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90859225647024139238248925 34072209617634052214343347)
          ·
            refine ⟨51108314426451078321515021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34072209617634052214343347 51108314426451078321515021)
            ·
              refine ⟨19165617909919154370568133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51108314426451078321515021 19165617909919154370568133)
              ·
                refine ⟨3593553358109841444481525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19165617909919154370568133 3593553358109841444481525)
                ·
                  refine ⟨336895627322797635420143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3593553358109841444481525 336895627322797635420143)
                  ·
                    rfl

theorem cell23_5904917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 5].length) (baseStart_5904917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904917 prefixEnd_5904917 := by exact prefixLift 5904917
  have htrace : WordTrace (prefixWord ++ tailWord_5904917) baseStart_5904917 baseEnd_5904917 := by
    simpa [prefixWord, tailWord_5904917, baseEnd_5904917] using wordTrace_append hprefix tailTrace_5904917
  have hstable : (prefixWord ++ tailWord_5904917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904917).length < 2 ^ (prefixWord ++ tailWord_5904917).sum := by decide
  have hdescent : baseEnd_5904917 < baseStart_5904917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904930 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_5904930 : Nat := 118140960795 + 5904930 * 2 ^ 59
def prefixEnd_5904930 : Nat := 4983230072969 + 3 ^ 40 * 5904930 * 2
def baseEnd_5904930 : Nat := 1010689107051229055972909

theorem tailTrace_5904930 : CollatzResearch.WordTrace tailWord_5904930 prefixEnd_5904930 1010689107051229055972909 := by
  unfold tailWord_5904930
  simp only [CollatzResearch.WordTrace]
  refine ⟨53842622624363641649944061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143580326998303044399850829 53842622624363641649944061)
  ·
    refine ⟨20190983484136365618729023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53842622624363641649944061 20190983484136365618729023)
    ·
      refine ⟨30286475226204548428093535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20190983484136365618729023 30286475226204548428093535)
      ·
        refine ⟨45429712839306822642140303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30286475226204548428093535 45429712839306822642140303)
        ·
          refine ⟨68144569258960233963210455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45429712839306822642140303 68144569258960233963210455)
          ·
            refine ⟨102216853888440350944815683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68144569258960233963210455 102216853888440350944815683)
            ·
              refine ⟨153325280832660526417223525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102216853888440350944815683 153325280832660526417223525)
              ·
                refine ⟨28748490156123848703229411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153325280832660526417223525 28748490156123848703229411)
                ·
                  refine ⟨43122735234185773054844117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28748490156123848703229411 43122735234185773054844117)
                  ·
                    refine ⟨1010689107051229055972909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43122735234185773054844117 1010689107051229055972909)
                    ·
                      rfl

theorem cell23_5904930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_5904930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904930 prefixEnd_5904930 := by exact prefixLift 5904930
  have htrace : WordTrace (prefixWord ++ tailWord_5904930) baseStart_5904930 baseEnd_5904930 := by
    simpa [prefixWord, tailWord_5904930, baseEnd_5904930] using wordTrace_append hprefix tailTrace_5904930
  have hstable : (prefixWord ++ tailWord_5904930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904930).length < 2 ^ (prefixWord ++ tailWord_5904930).sum := by decide
  have hdescent : baseEnd_5904930 < baseStart_5904930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904977 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 3, 4]
def baseStart_5904977 : Nat := 118140960795 + 5904977 * 2 ^ 59
def prefixEnd_5904977 : Nat := 4983230072969 + 3 ^ 40 * 5904977 * 2
def baseEnd_5904977 : Nat := 1010697151581482828010337

theorem tailTrace_5904977 : CollatzResearch.WordTrace tailWord_5904977 prefixEnd_5904977 1010697151581482828010337 := by
  unfold tailWord_5904977
  simp only [CollatzResearch.WordTrace]
  refine ⟨215372204728284293626737185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143581469818856195751158123 215372204728284293626737185)
  ·
    refine ⟨161529153546213220220052889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215372204728284293626737185 161529153546213220220052889)
    ·
      refine ⟨121146865159659915165039667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161529153546213220220052889 121146865159659915165039667)
      ·
        refine ⟨181720297739489872747559501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121146865159659915165039667 181720297739489872747559501)
        ·
          refine ⟨68145111652308702280334813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181720297739489872747559501 68145111652308702280334813)
          ·
            refine ⟨25554416869615763355125555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68145111652308702280334813 25554416869615763355125555)
            ·
              refine ⟨38331625304423645032688333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25554416869615763355125555 38331625304423645032688333)
              ·
                refine ⟨14374359489158866887258125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38331625304423645032688333 14374359489158866887258125)
                ·
                  refine ⟨5390384808434575082721797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14374359489158866887258125 5390384808434575082721797)
                  ·
                    refine ⟨1010697151581482828010337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5390384808434575082721797 1010697151581482828010337)
                    ·
                      rfl

theorem cell23_5904977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_5904977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904977 prefixEnd_5904977 := by exact prefixLift 5904977
  have htrace : WordTrace (prefixWord ++ tailWord_5904977) baseStart_5904977 baseEnd_5904977 := by
    simpa [prefixWord, tailWord_5904977, baseEnd_5904977] using wordTrace_append hprefix tailTrace_5904977
  have hstable : (prefixWord ++ tailWord_5904977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904977).length < 2 ^ (prefixWord ++ tailWord_5904977).sum := by decide
  have hdescent : baseEnd_5904977 < baseStart_5904977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905028 : List Nat := [2, 3, 2, 1, 3, 2, 3, 2, 1, 4]
def baseStart_5905028 : Nat := 118140960795 + 5905028 * 2 ^ 59
def prefixEnd_5905028 : Nat := 4983230072969 + 3 ^ 40 * 5905028 * 2
def baseEnd_5905028 : Nat := 1010705880752609261497759

theorem tailTrace_5905028 : CollatzResearch.WordTrace tailWord_5905028 prefixEnd_5905028 1010705880752609261497759 := by
  unfold tailWord_5905028
  simp only [CollatzResearch.WordTrace]
  refine ⟨107687032425549764668421869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143582709900733019557895825 107687032425549764668421869)
  ·
    refine ⟨40382637159581161750658201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107687032425549764668421869 40382637159581161750658201)
    ·
      refine ⟨30286977869685871312993651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40382637159581161750658201 30286977869685871312993651)
      ·
        refine ⟨45430466804528806969490477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30286977869685871312993651 45430466804528806969490477)
        ·
          refine ⟨17036425051698302613558929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45430466804528806969490477 17036425051698302613558929)
          ·
            refine ⟨12777318788773726960169197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17036425051698302613558929 12777318788773726960169197)
            ·
              refine ⟨4791494545790147610063449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12777318788773726960169197 4791494545790147610063449)
              ·
                refine ⟨3593620909342610707547587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4791494545790147610063449 3593620909342610707547587)
                ·
                  refine ⟨5390431364013916061321381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593620909342610707547587 5390431364013916061321381)
                  ·
                    refine ⟨1010705880752609261497759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5390431364013916061321381 1010705880752609261497759)
                    ·
                      rfl

theorem cell23_5905028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_5905028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905028 prefixEnd_5905028 := by exact prefixLift 5905028
  have htrace : WordTrace (prefixWord ++ tailWord_5905028) baseStart_5905028 baseEnd_5905028 := by
    simpa [prefixWord, tailWord_5905028, baseEnd_5905028] using wordTrace_append hprefix tailTrace_5905028
  have hstable : (prefixWord ++ tailWord_5905028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905028).length < 2 ^ (prefixWord ++ tailWord_5905028).sum := by decide
  have hdescent : baseEnd_5905028 < baseStart_5905028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905040 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 4]
def baseStart_5905040 : Nat := 118140960795 + 5905040 * 2 ^ 59
def prefixEnd_5905040 : Nat := 4983230072969 + 3 ^ 40 * 5905040 * 2
def baseEnd_5905040 : Nat := 3032123804025681737543221

theorem tailTrace_5905040 : CollatzResearch.WordTrace tailWord_5905040 prefixEnd_5905040 3032123804025681737543221 := by
  unfold tailWord_5905040
  simp only [CollatzResearch.WordTrace]
  refine ⟨107687251263528027693140287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143583001684704036924187049 107687251263528027693140287)
  ·
    refine ⟨161530876895292041539710431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107687251263528027693140287 161530876895292041539710431)
    ·
      refine ⟨242296315342938062309565647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161530876895292041539710431 242296315342938062309565647)
      ·
        refine ⟨363444473014407093464348471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242296315342938062309565647 363444473014407093464348471)
        ·
          refine ⟨545166709521610640196522707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363444473014407093464348471 545166709521610640196522707)
          ·
            refine ⟨817750064282415960294784061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545166709521610640196522707 817750064282415960294784061)
            ·
              refine ⟨306656274105905985110544023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 817750064282415960294784061 306656274105905985110544023)
              ·
                refine ⟨459984411158858977665816035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306656274105905985110544023 459984411158858977665816035)
                ·
                  refine ⟨689976616738288466498724053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459984411158858977665816035 689976616738288466498724053)
                  ·
                    refine ⟨16171326954803635933563845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 689976616738288466498724053 16171326954803635933563845)
                    ·
                      refine ⟨3032123804025681737543221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16171326954803635933563845 3032123804025681737543221)
                      ·
                        rfl

theorem cell23_5905040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_5905040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905040 prefixEnd_5905040 := by exact prefixLift 5905040
  have htrace : WordTrace (prefixWord ++ tailWord_5905040) baseStart_5905040 baseEnd_5905040 := by
    simpa [prefixWord, tailWord_5905040, baseEnd_5905040] using wordTrace_append hprefix tailTrace_5905040
  have hstable : (prefixWord ++ tailWord_5905040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905040).length < 2 ^ (prefixWord ++ tailWord_5905040).sum := by decide
  have hdescent : baseEnd_5905040 < baseStart_5905040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905054 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_5905054 : Nat := 118140960795 + 5905054 * 2 ^ 59
def prefixEnd_5905054 : Nat := 4983230072969 + 3 ^ 40 * 5905054 * 2
def baseEnd_5905054 : Nat := 1010710330918281560922719

theorem tailTrace_5905054 : CollatzResearch.WordTrace tailWord_5905054 prefixEnd_5905054 1010710330918281560922719 := by
  unfold tailWord_5905054
  simp only [CollatzResearch.WordTrace]
  refine ⟨26921876643625666972161277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143583342099336890518193477 26921876643625666972161277)
  ·
    refine ⟨10095703741359625114560479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26921876643625666972161277 10095703741359625114560479)
    ·
      refine ⟨15143555612039437671840719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10095703741359625114560479 15143555612039437671840719)
      ·
        refine ⟨22715333418059156507761079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15143555612039437671840719 22715333418059156507761079)
        ·
          refine ⟨34073000127088734761641619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22715333418059156507761079 34073000127088734761641619)
          ·
            refine ⟨51109500190633102142462429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34073000127088734761641619 51109500190633102142462429)
            ·
              refine ⟨19166062571487413303423411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51109500190633102142462429 19166062571487413303423411)
              ·
                refine ⟨28749093857231119955135117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19166062571487413303423411 28749093857231119955135117)
                ·
                  refine ⟨10780910196461669983175669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28749093857231119955135117 10780910196461669983175669)
                  ·
                    refine ⟨1010710330918281560922719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10780910196461669983175669 1010710330918281560922719)
                    ·
                      rfl

theorem cell23_5905054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_5905054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905054 prefixEnd_5905054 := by exact prefixLift 5905054
  have htrace : WordTrace (prefixWord ++ tailWord_5905054) baseStart_5905054 baseEnd_5905054 := by
    simpa [prefixWord, tailWord_5905054, baseEnd_5905054] using wordTrace_append hprefix tailTrace_5905054
  have hstable : (prefixWord ++ tailWord_5905054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905054).length < 2 ^ (prefixWord ++ tailWord_5905054).sum := by decide
  have hdescent : baseEnd_5905054 < baseStart_5905054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905085 : List Nat := [1, 4, 1, 2, 1, 5, 2, 2, 1, 1, 3]
def baseStart_5905085 : Nat := 118140960795 + 5905085 * 2 ^ 59
def prefixEnd_5905085 : Nat := 4983230072969 + 3 ^ 40 * 5905085 * 2
def baseEnd_5905085 : Nat := 3032146910655134061480515

theorem tailTrace_5905085 : CollatzResearch.WordTrace tailWord_5905085 prefixEnd_5905085 3032146910655134061480515 := by
  unfold tailWord_5905085
  simp only [CollatzResearch.WordTrace]
  refine ⟨215376143811893028071668709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143584095874595352047779139 215376143811893028071668709)
  ·
    refine ⟨40383026964729942763437883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215376143811893028071668709 40383026964729942763437883)
    ·
      refine ⟨60574540447094914145156825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40383026964729942763437883 60574540447094914145156825)
      ·
        refine ⟨45430905335321185608867619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60574540447094914145156825 45430905335321185608867619)
        ·
          refine ⟨68146358002981778413301429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45430905335321185608867619 68146358002981778413301429)
          ·
            refine ⟨6388721062779541726247009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68146358002981778413301429 6388721062779541726247009)
            ·
              refine ⟨4791540797084656294685257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6388721062779541726247009 4791540797084656294685257)
              ·
                refine ⟨3593655597813492221013943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4791540797084656294685257 3593655597813492221013943)
                ·
                  refine ⟨5390483396720238331520915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593655597813492221013943 5390483396720238331520915)
                  ·
                    refine ⟨8085725095080357497281373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5390483396720238331520915 8085725095080357497281373)
                    ·
                      refine ⟨3032146910655134061480515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8085725095080357497281373 3032146910655134061480515)
                      ·
                        rfl

theorem cell23_5905085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_5905085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905085 prefixEnd_5905085 := by exact prefixLift 5905085
  have htrace : WordTrace (prefixWord ++ tailWord_5905085) baseStart_5905085 baseEnd_5905085 := by
    simpa [prefixWord, tailWord_5905085, baseEnd_5905085] using wordTrace_append hprefix tailTrace_5905085
  have hstable : (prefixWord ++ tailWord_5905085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905085).length < 2 ^ (prefixWord ++ tailWord_5905085).sum := by decide
  have hdescent : baseEnd_5905085 < baseStart_5905085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905124 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 1, 3, 3]
def baseStart_5905124 : Nat := 118140960795 + 5905124 * 2 ^ 59
def prefixEnd_5905124 : Nat := 4983230072969 + 3 ^ 40 * 5905124 * 2
def baseEnd_5905124 : Nat := 3032166936400659408892835

theorem tailTrace_5905124 : CollatzResearch.WordTrace tailWord_5905124 prefixEnd_5905124 3032166936400659408892835 := by
  unfold tailWord_5905124
  simp only [CollatzResearch.WordTrace]
  refine ⟨107688783129375868866169213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143585044172501158488225617 107688783129375868866169213)
  ·
    refine ⟨40383293673515950824813455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107688783129375868866169213 40383293673515950824813455)
    ·
      refine ⟨60574940510273926237220183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40383293673515950824813455 60574940510273926237220183)
      ·
        refine ⟨90862410765410889355830275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60574940510273926237220183 90862410765410889355830275)
        ·
          refine ⟨136293616148116334033745413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90862410765410889355830275 136293616148116334033745413)
          ·
            refine ⟨25555053027771812631327265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136293616148116334033745413 25555053027771812631327265)
            ·
              refine ⟨19166289770828859473495449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25555053027771812631327265 19166289770828859473495449)
              ·
                refine ⟨14374717328121644605121587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19166289770828859473495449 14374717328121644605121587)
                ·
                  refine ⟨21562075992182466907682381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14374717328121644605121587 21562075992182466907682381)
                  ·
                    refine ⟨8085778497068425090380893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21562075992182466907682381 8085778497068425090380893)
                    ·
                      refine ⟨3032166936400659408892835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8085778497068425090380893 3032166936400659408892835)
                      ·
                        rfl

theorem cell23_5905124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_5905124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905124 prefixEnd_5905124 := by exact prefixLift 5905124
  have htrace : WordTrace (prefixWord ++ tailWord_5905124) baseStart_5905124 baseEnd_5905124 := by
    simpa [prefixWord, tailWord_5905124, baseEnd_5905124] using wordTrace_append hprefix tailTrace_5905124
  have hstable : (prefixWord ++ tailWord_5905124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905124).length < 2 ^ (prefixWord ++ tailWord_5905124).sum := by decide
  have hdescent : baseEnd_5905124 < baseStart_5905124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905125 : List Nat := [1, 3, 1, 4, 1, 3, 2, 3, 1, 2, 2]
def baseStart_5905125 : Nat := 118140960795 + 5905125 * 2 ^ 59
def prefixEnd_5905125 : Nat := 4983230072969 + 3 ^ 40 * 5905125 * 2
def baseEnd_5905125 : Nat := 3032167449881313904980331

theorem tailTrace_5905125 : CollatzResearch.WordTrace tailWord_5905125 prefixEnd_5905125 3032167449881313904980331 := by
  unfold tailWord_5905125
  simp only [CollatzResearch.WordTrace]
  refine ⟨215377602731748114903124829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143585068487832076602083219 215377602731748114903124829)
  ·
    refine ⟨80766601024405543088671811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215377602731748114903124829 80766601024405543088671811)
    ·
      refine ⟨121149901536608314633007717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80766601024405543088671811 121149901536608314633007717)
      ·
        refine ⟨22715606538114058993688947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121149901536608314633007717 22715606538114058993688947)
        ·
          refine ⟨34073409807171088490533421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22715606538114058993688947 34073409807171088490533421)
          ·
            refine ⟨12777528677689158183950033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34073409807171088490533421 12777528677689158183950033)
            ·
              refine ⟨9583146508266868637962525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12777528677689158183950033 9583146508266868637962525)
              ·
                refine ⟨3593679940600075739235947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9583146508266868637962525 3593679940600075739235947)
                ·
                  refine ⟨5390519910900113608853921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593679940600075739235947 5390519910900113608853921)
                  ·
                    refine ⟨4042889933175085206640441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5390519910900113608853921 4042889933175085206640441)
                    ·
                      refine ⟨3032167449881313904980331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4042889933175085206640441 3032167449881313904980331)
                      ·
                        rfl

theorem cell23_5905125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_5905125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905125 prefixEnd_5905125 := by exact prefixLift 5905125
  have htrace : WordTrace (prefixWord ++ tailWord_5905125) baseStart_5905125 baseEnd_5905125 := by
    simpa [prefixWord, tailWord_5905125, baseEnd_5905125] using wordTrace_append hprefix tailTrace_5905125
  have hstable : (prefixWord ++ tailWord_5905125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905125).length < 2 ^ (prefixWord ++ tailWord_5905125).sum := by decide
  have hdescent : baseEnd_5905125 < baseStart_5905125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905167 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 5]
def baseStart_5905167 : Nat := 118140960795 + 5905167 * 2 ^ 59
def prefixEnd_5905167 : Nat := 4983230072969 + 3 ^ 40 * 5905167 * 2
def baseEnd_5905167 : Nat := 3032189016068802740655137

theorem tailTrace_5905167 : CollatzResearch.WordTrace tailWord_5905167 prefixEnd_5905167 3032189016068802740655137 := by
  unfold tailWord_5905167
  simp only [CollatzResearch.WordTrace]
  refine ⟨215379134597595956076153755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143586089731730637384102503 215379134597595956076153755)
  ·
    refine ⟨323068701896393934114230633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215379134597595956076153755 323068701896393934114230633)
    ·
      refine ⟨242301526422295450585672975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323068701896393934114230633 242301526422295450585672975)
      ·
        refine ⟨363452289633443175878509463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242301526422295450585672975 363452289633443175878509463)
        ·
          refine ⟨545178434450164763817764195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363452289633443175878509463 545178434450164763817764195)
          ·
            refine ⟨817767651675247145726646293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545178434450164763817764195 817767651675247145726646293)
            ·
              refine ⟨38332858672277209955936545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 817767651675247145726646293 38332858672277209955936545)
              ·
                refine ⟨28749644004207907466952409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38332858672277209955936545 28749644004207907466952409)
                ·
                  refine ⟨21562233003155930600214307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28749644004207907466952409 21562233003155930600214307)
                  ·
                    refine ⟨32343349504733895900321461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21562233003155930600214307 32343349504733895900321461)
                    ·
                      refine ⟨3032189016068802740655137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32343349504733895900321461 3032189016068802740655137)
                      ·
                        rfl

theorem cell23_5905167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_5905167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905167 prefixEnd_5905167 := by exact prefixLift 5905167
  have htrace : WordTrace (prefixWord ++ tailWord_5905167) baseStart_5905167 baseEnd_5905167 := by
    simpa [prefixWord, tailWord_5905167, baseEnd_5905167] using wordTrace_append hprefix tailTrace_5905167
  have hstable : (prefixWord ++ tailWord_5905167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905167).length < 2 ^ (prefixWord ++ tailWord_5905167).sum := by decide
  have hdescent : baseEnd_5905167 < baseStart_5905167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905177 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 4, 2, 4]
def baseStart_5905177 : Nat := 118140960795 + 5905177 * 2 ^ 59
def prefixEnd_5905177 : Nat := 4983230072969 + 3 ^ 40 * 5905177 * 2
def baseEnd_5905177 : Nat := 3032194150875347701530091

theorem tailTrace_5905177 : CollatzResearch.WordTrace tailWord_5905177 prefixEnd_5905177 3032194150875347701530091 := by
  unfold tailWord_5905177
  simp only [CollatzResearch.WordTrace]
  refine ⟨215379499327559727784017785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143586332885039818522678523 215379499327559727784017785)
  ·
    refine ⟨161534624495669795838013339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215379499327559727784017785 161534624495669795838013339)
    ·
      refine ⟨242301936743504693757020009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161534624495669795838013339 242301936743504693757020009)
      ·
        refine ⟨181726452557628520317765007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242301936743504693757020009 181726452557628520317765007)
        ·
          refine ⟨272589678836442780476647511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181726452557628520317765007 272589678836442780476647511)
          ·
            refine ⟨408884518254664170714971267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272589678836442780476647511 408884518254664170714971267)
            ·
              refine ⟨613326777381996256072456901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408884518254664170714971267 613326777381996256072456901)
              ·
                refine ⟨114998770759124298013585669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 613326777381996256072456901 114998770759124298013585669)
                ·
                  refine ⟨21562269517335805877547313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114998770759124298013585669 21562269517335805877547313)
                  ·
                    refine ⟨16171702138001854408160485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21562269517335805877547313 16171702138001854408160485)
                    ·
                      refine ⟨3032194150875347701530091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16171702138001854408160485 3032194150875347701530091)
                      ·
                        rfl

theorem cell23_5905177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_5905177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905177 prefixEnd_5905177 := by exact prefixLift 5905177
  have htrace : WordTrace (prefixWord ++ tailWord_5905177) baseStart_5905177 baseEnd_5905177 := by
    simpa [prefixWord, tailWord_5905177, baseEnd_5905177] using wordTrace_append hprefix tailTrace_5905177
  have hstable : (prefixWord ++ tailWord_5905177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905177).length < 2 ^ (prefixWord ++ tailWord_5905177).sum := by decide
  have hdescent : baseEnd_5905177 < baseStart_5905177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905184 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 5]
def baseStart_5905184 : Nat := 118140960795 + 5905184 * 2 ^ 59
def prefixEnd_5905184 : Nat := 4983230072969 + 3 ^ 40 * 5905184 * 2
def baseEnd_5905184 : Nat := 3032197745239929174142559

theorem tailTrace_5905184 : CollatzResearch.WordTrace tailWord_5905184 prefixEnd_5905184 3032197745239929174142559 := by
  unfold tailWord_5905184
  simp only [CollatzResearch.WordTrace]
  refine ⟨107689877319267183989761303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143586503092356245319681737 107689877319267183989761303)
  ·
    refine ⟨161534815978900775984641955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107689877319267183989761303 161534815978900775984641955)
    ·
      refine ⟨242302223968351163976962933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161534815978900775984641955 242302223968351163976962933)
      ·
        refine ⟨22715833497032921622840275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242302223968351163976962933 22715833497032921622840275)
        ·
          refine ⟨34073750245549382434260413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22715833497032921622840275 34073750245549382434260413)
          ·
            refine ⟨12777656342081018412847655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34073750245549382434260413 12777656342081018412847655)
            ·
              refine ⟨19166484513121527619271483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12777656342081018412847655 19166484513121527619271483)
              ·
                refine ⟨28749726769682291428907225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19166484513121527619271483 28749726769682291428907225)
                ·
                  refine ⟨21562295077261718571680419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28749726769682291428907225 21562295077261718571680419)
                  ·
                    refine ⟨32343442615892577857520629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21562295077261718571680419 32343442615892577857520629)
                    ·
                      refine ⟨3032197745239929174142559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32343442615892577857520629 3032197745239929174142559)
                      ·
                        rfl

theorem cell23_5905184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_5905184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905184 prefixEnd_5905184 := by exact prefixLift 5905184
  have htrace : WordTrace (prefixWord ++ tailWord_5905184) baseStart_5905184 baseEnd_5905184 := by
    simpa [prefixWord, tailWord_5905184, baseEnd_5905184] using wordTrace_append hprefix tailTrace_5905184
  have hstable : (prefixWord ++ tailWord_5905184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905184).length < 2 ^ (prefixWord ++ tailWord_5905184).sum := by decide
  have hdescent : baseEnd_5905184 < baseStart_5905184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905215 : List Nat := [1, 1, 2, 2, 5, 1, 4, 1, 2, 2, 2]
def baseStart_5905215 : Nat := 118140960795 + 5905215 * 2 ^ 59
def prefixEnd_5905215 : Nat := 4983230072969 + 3 ^ 40 * 5905215 * 2
def baseEnd_5905215 : Nat := 3032213663140218552854917

theorem tailTrace_5905215 : CollatzResearch.WordTrace tailWord_5905215 prefixEnd_5905215 3032213663140218552854917 := by
  unfold tailWord_5905215
  simp only [CollatzResearch.WordTrace]
  refine ⟨215380885301422060273901099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143587256867614706849267399 215380885301422060273901099)
  ·
    refine ⟨323071327952133090410851649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215380885301422060273901099 323071327952133090410851649)
    ·
      refine ⟨242303495964099817808138737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323071327952133090410851649 242303495964099817808138737)
      ·
        refine ⟨181727621973074863356104053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242303495964099817808138737 181727621973074863356104053)
        ·
          refine ⟨17036964559975768439634755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181727621973074863356104053 17036964559975768439634755)
          ·
            refine ⟨25555446839963652659452133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17036964559975768439634755 25555446839963652659452133)
            ·
              refine ⟨4791646282493184873647275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25555446839963652659452133 4791646282493184873647275)
              ·
                refine ⟨7187469423739777310470913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4791646282493184873647275 7187469423739777310470913)
                ·
                  refine ⟨5390602067804832982853185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7187469423739777310470913 5390602067804832982853185)
                  ·
                    refine ⟨4042951550853624737139889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5390602067804832982853185 4042951550853624737139889)
                    ·
                      refine ⟨3032213663140218552854917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4042951550853624737139889 3032213663140218552854917)
                      ·
                        rfl

theorem cell23_5905215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 2, 2, 2].length) (baseStart_5905215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905215 prefixEnd_5905215 := by exact prefixLift 5905215
  have htrace : WordTrace (prefixWord ++ tailWord_5905215) baseStart_5905215 baseEnd_5905215 := by
    simpa [prefixWord, tailWord_5905215, baseEnd_5905215] using wordTrace_append hprefix tailTrace_5905215
  have hstable : (prefixWord ++ tailWord_5905215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905215).length < 2 ^ (prefixWord ++ tailWord_5905215).sum := by decide
  have hdescent : baseEnd_5905215 < baseStart_5905215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905274 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3]
def baseStart_5905274 : Nat := 118140960795 + 5905274 * 2 ^ 59
def prefixEnd_5905274 : Nat := 4983230072969 + 3 ^ 40 * 5905274 * 2
def baseEnd_5905274 : Nat := 3032243958498833822017145

theorem tailTrace_5905274 : CollatzResearch.WordTrace tailWord_5905274 prefixEnd_5905274 3032243958498833822017145 := by
  unfold tailWord_5905274
  simp only [CollatzResearch.WordTrace]
  refine ⟨53845759302052078337574719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143588691472138875566865917 53845759302052078337574719)
  ·
    refine ⟨80768638953078117506362079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53845759302052078337574719 80768638953078117506362079)
    ·
      refine ⟨121152958429617176259543119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80768638953078117506362079 121152958429617176259543119)
      ·
        refine ⟨181729437644425764389314679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121152958429617176259543119 181729437644425764389314679)
        ·
          refine ⟨272594156466638646583972019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181729437644425764389314679 272594156466638646583972019)
          ·
            refine ⟨408891234699957969875958029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272594156466638646583972019 408891234699957969875958029)
            ·
              refine ⟨153334213012484238703484261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 408891234699957969875958029 153334213012484238703484261)
              ·
                refine ⟨28750164939840794756903299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153334213012484238703484261 28750164939840794756903299)
                ·
                  refine ⟨43125247409761192135354949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28750164939840794756903299 43125247409761192135354949)
                  ·
                    refine ⟨8085983889330223525379053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43125247409761192135354949 8085983889330223525379053)
                    ·
                      refine ⟨3032243958498833822017145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8085983889330223525379053 3032243958498833822017145)
                      ·
                        rfl

theorem cell23_5905274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_5905274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905274 prefixEnd_5905274 := by exact prefixLift 5905274
  have htrace : WordTrace (prefixWord ++ tailWord_5905274) baseStart_5905274 baseEnd_5905274 := by
    simpa [prefixWord, tailWord_5905274, baseEnd_5905274] using wordTrace_append hprefix tailTrace_5905274
  have hstable : (prefixWord ++ tailWord_5905274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905274).length < 2 ^ (prefixWord ++ tailWord_5905274).sum := by decide
  have hdescent : baseEnd_5905274 < baseStart_5905274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905288 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 2, 1, 4]
def baseStart_5905288 : Nat := 118140960795 + 5905288 * 2 ^ 59
def prefixEnd_5905288 : Nat := 4983230072969 + 3 ^ 40 * 5905288 * 2
def baseEnd_5905288 : Nat := 3032251147227996767242081

theorem tailTrace_5905288 : CollatzResearch.WordTrace tailWord_5905288 prefixEnd_5905288 3032251147227996767242081 := by
  unfold tailWord_5905288
  simp only [CollatzResearch.WordTrace]
  refine ⟨107691773915078796870654259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143589031886771729160872345 107691773915078796870654259)
  ·
    refine ⟨161537660872618195305981389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107691773915078796870654259 161537660872618195305981389)
    ·
      refine ⟨60576622827231823239743021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161537660872618195305981389 60576622827231823239743021)
      ·
        refine ⟨22716233560211933714903633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60576622827231823239743021 22716233560211933714903633)
        ·
          refine ⟨17037175170158950286177725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22716233560211933714903633 17037175170158950286177725)
          ·
            refine ⟨6388940688809606357316647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17037175170158950286177725 6388940688809606357316647)
            ·
              refine ⟨9583411033214409535974971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6388940688809606357316647 9583411033214409535974971)
              ·
                refine ⟨14375116549821614303962457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9583411033214409535974971 14375116549821614303962457)
                ·
                  refine ⟨10781337412366210727971843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14375116549821614303962457 10781337412366210727971843)
                  ·
                    refine ⟨16172006118549316091957765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10781337412366210727971843 16172006118549316091957765)
                    ·
                      refine ⟨3032251147227996767242081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16172006118549316091957765 3032251147227996767242081)
                      ·
                        rfl

theorem cell23_5905288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_5905288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905288 prefixEnd_5905288 := by exact prefixLift 5905288
  have htrace : WordTrace (prefixWord ++ tailWord_5905288) baseStart_5905288 baseEnd_5905288 := by
    simpa [prefixWord, tailWord_5905288, baseEnd_5905288] using wordTrace_append hprefix tailTrace_5905288
  have hstable : (prefixWord ++ tailWord_5905288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905288).length < 2 ^ (prefixWord ++ tailWord_5905288).sum := by decide
  have hdescent : baseEnd_5905288 < baseStart_5905288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905291 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 3]
def baseStart_5905291 : Nat := 118140960795 + 5905291 * 2 ^ 59
def prefixEnd_5905291 : Nat := 4983230072969 + 3 ^ 40 * 5905291 * 2
def baseEnd_5905291 : Nat := 3032252687669960255504567

theorem tailTrace_5905291 : CollatzResearch.WordTrace tailWord_5905291 prefixEnd_5905291 3032252687669960255504567 := by
  unfold tailWord_5905291
  simp only [CollatzResearch.WordTrace]
  refine ⟨215383657249146725253667727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143589104832764483502445151 215383657249146725253667727)
  ·
    refine ⟨323075485873720087880501591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215383657249146725253667727 323075485873720087880501591)
    ·
      refine ⟨484613228810580131820752387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323075485873720087880501591 484613228810580131820752387)
      ·
        refine ⟨726919843215870197731128581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484613228810580131820752387 726919843215870197731128581)
        ·
          refine ⟨136297470602975662074586609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 726919843215870197731128581 136297470602975662074586609)
          ·
            refine ⟨102223102952231746555939957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136297470602975662074586609 102223102952231746555939957)
            ·
              refine ⟨9583415901771726239619371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102223102952231746555939957 9583415901771726239619371)
              ·
                refine ⟨14375123852657589359429057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9583415901771726239619371 14375123852657589359429057)
                ·
                  refine ⟨10781342889493192019571793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14375123852657589359429057 10781342889493192019571793)
                  ·
                    refine ⟨8086007167119894014678845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10781342889493192019571793 8086007167119894014678845)
                    ·
                      refine ⟨3032252687669960255504567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8086007167119894014678845 3032252687669960255504567)
                      ·
                        rfl

theorem cell23_5905291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 3].length) (baseStart_5905291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905291 prefixEnd_5905291 := by exact prefixLift 5905291
  have htrace : WordTrace (prefixWord ++ tailWord_5905291) baseStart_5905291 baseEnd_5905291 := by
    simpa [prefixWord, tailWord_5905291, baseEnd_5905291] using wordTrace_append hprefix tailTrace_5905291
  have hstable : (prefixWord ++ tailWord_5905291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905291).length < 2 ^ (prefixWord ++ tailWord_5905291).sum := by decide
  have hdescent : baseEnd_5905291 < baseStart_5905291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905311 : List Nat := [1, 1, 2, 5, 2, 1, 3, 2, 6]
def baseStart_5905311 : Nat := 118140960795 + 5905311 * 2 ^ 59
def prefixEnd_5905311 : Nat := 4983230072969 + 3 ^ 40 * 5905311 * 2
def baseEnd_5905311 : Nat := 336918106364783353028275

theorem tailTrace_5905311 : CollatzResearch.WordTrace tailWord_5905311 prefixEnd_5905311 336918106364783353028275 := by
  unfold tailWord_5905311
  simp only [CollatzResearch.WordTrace]
  refine ⟨215384386709074268669395787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143589591139382845779597191 215384386709074268669395787)
  ·
    refine ⟨323076580063611403004093681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215384386709074268669395787 323076580063611403004093681)
    ·
      refine ⟨242307435047708552253070261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323076580063611403004093681 242307435047708552253070261)
      ·
        refine ⟨22716322035722676773725337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242307435047708552253070261 22716322035722676773725337)
        ·
          refine ⟨17037241526792007580294003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22716322035722676773725337 17037241526792007580294003)
          ·
            refine ⟨25555862290188011370441005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17037241526792007580294003 25555862290188011370441005)
            ·
              refine ⟨9583448358820504263915377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25555862290188011370441005 9583448358820504263915377)
              ·
                refine ⟨7187586269115378197936533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9583448358820504263915377 7187586269115378197936533)
                ·
                  refine ⟨336918106364783353028275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7187586269115378197936533 336918106364783353028275)
                  ·
                    rfl

theorem cell23_5905311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 6].length) (baseStart_5905311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905311 prefixEnd_5905311 := by exact prefixLift 5905311
  have htrace : WordTrace (prefixWord ++ tailWord_5905311) baseStart_5905311 baseEnd_5905311 := by
    simpa [prefixWord, tailWord_5905311, baseEnd_5905311] using wordTrace_append hprefix tailTrace_5905311
  have hstable : (prefixWord ++ tailWord_5905311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905311).length < 2 ^ (prefixWord ++ tailWord_5905311).sum := by decide
  have hdescent : baseEnd_5905311 < baseStart_5905311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905331 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 6, 3, 2]
def baseStart_5905331 : Nat := 118140960795 + 5905331 * 2 ^ 59
def prefixEnd_5905331 : Nat := 4983230072969 + 3 ^ 40 * 5905331 * 2
def baseEnd_5905331 : Nat := 3032273226896140099004383

theorem tailTrace_5905331 : CollatzResearch.WordTrace tailWord_5905331 prefixEnd_5905331 3032273226896140099004383 := by
  unfold tailWord_5905331
  simp only [CollatzResearch.WordTrace]
  refine ⟨215385116169001812085123847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143590077446001208056749231 215385116169001812085123847)
  ·
    refine ⟨323077674253502718127685771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215385116169001812085123847 323077674253502718127685771)
    ·
      refine ⟨484616511380254077191528657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323077674253502718127685771 484616511380254077191528657)
      ·
        refine ⟨363462383535190557893646493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484616511380254077191528657 363462383535190557893646493)
        ·
          refine ⟨136298393825696459210117435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363462383535190557893646493 136298393825696459210117435)
          ·
            refine ⟨204447590738544688815176153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136298393825696459210117435 204447590738544688815176153)
            ·
              refine ⟨153335693053908516611382115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204447590738544688815176153 153335693053908516611382115)
              ·
                refine ⟨230003539580862774917073173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153335693053908516611382115 230003539580862774917073173)
                ·
                  refine ⟨10781415917852942574237805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 230003539580862774917073173 10781415917852942574237805)
                  ·
                    refine ⟨4043030969194853465339177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10781415917852942574237805 4043030969194853465339177)
                    ·
                      refine ⟨3032273226896140099004383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043030969194853465339177 3032273226896140099004383)
                      ·
                        rfl

theorem cell23_5905331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 3, 2].length) (baseStart_5905331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905331 prefixEnd_5905331 := by exact prefixLift 5905331
  have htrace : WordTrace (prefixWord ++ tailWord_5905331) baseStart_5905331 baseEnd_5905331 := by
    simpa [prefixWord, tailWord_5905331, baseEnd_5905331] using wordTrace_append hprefix tailTrace_5905331
  have hstable : (prefixWord ++ tailWord_5905331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905331).length < 2 ^ (prefixWord ++ tailWord_5905331).sum := by decide
  have hdescent : baseEnd_5905331 < baseStart_5905331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905354 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 3, 6]
def baseStart_5905354 : Nat := 118140960795 + 5905354 * 2 ^ 59
def prefixEnd_5905354 : Nat := 4983230072969 + 3 ^ 40 * 5905354 * 2
def baseEnd_5905354 : Nat := 1010761678983731169672259

theorem tailTrace_5905354 : CollatzResearch.WordTrace tailWord_5905354 prefixEnd_5905354 1010761678983731169672259 := by
  unfold tailWord_5905354
  simp only [CollatzResearch.WordTrace]
  refine ⟨53846488761979621753302779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143590636698612324675474077 53846488761979621753302779)
  ·
    refine ⟨80769733142969432629954169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53846488761979621753302779 80769733142969432629954169)
    ·
      refine ⟨60577299857227074472465627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80769733142969432629954169 60577299857227074472465627)
      ·
        refine ⟨90865949785840611708698441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60577299857227074472465627 90865949785840611708698441)
        ·
          refine ⟨68149462339380458781523831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90865949785840611708698441 68149462339380458781523831)
          ·
            refine ⟨102224193509070688172285747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68149462339380458781523831 102224193509070688172285747)
            ·
              refine ⟨153336290263606032258428621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102224193509070688172285747 153336290263606032258428621)
              ·
                refine ⟨57501108848852262096910733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153336290263606032258428621 57501108848852262096910733)
                ·
                  refine ⟨21562915818319598286341525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57501108848852262096910733 21562915818319598286341525)
                  ·
                    refine ⟨1010761678983731169672259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21562915818319598286341525 1010761678983731169672259)
                    ·
                      rfl

theorem cell23_5905354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_5905354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905354 prefixEnd_5905354 := by exact prefixLift 5905354
  have htrace : WordTrace (prefixWord ++ tailWord_5905354) baseStart_5905354 baseEnd_5905354 := by
    simpa [prefixWord, tailWord_5905354, baseEnd_5905354] using wordTrace_append hprefix tailTrace_5905354
  have hstable : (prefixWord ++ tailWord_5905354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905354).length < 2 ^ (prefixWord ++ tailWord_5905354).sum := by decide
  have hdescent : baseEnd_5905354 < baseStart_5905354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905355 : List Nat := [1, 1, 1, 1, 3, 5, 3, 3, 1, 1, 3]
def baseStart_5905355 : Nat := 118140960795 + 5905355 * 2 ^ 59
def prefixEnd_5905355 : Nat := 4983230072969 + 3 ^ 40 * 5905355 * 2
def baseEnd_5905355 : Nat := 3032285550431848005104273

theorem tailTrace_5905355 : CollatzResearch.WordTrace tailWord_5905355 prefixEnd_5905355 3032285550431848005104273 := by
  unfold tailWord_5905355
  simp only [CollatzResearch.WordTrace]
  refine ⟨215385991520914864183997519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143590661013943242789331679 215385991520914864183997519)
  ·
    refine ⟨323078987281372296275996279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215385991520914864183997519 323078987281372296275996279)
    ·
      refine ⟨484618480922058444413994419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323078987281372296275996279 484618480922058444413994419)
      ·
        refine ⟨726927721383087666620991629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484618480922058444413994419 726927721383087666620991629)
        ·
          refine ⟨272597895518657874982871861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 726927721383087666620991629 272597895518657874982871861)
          ·
            refine ⟨25556052704874175779644237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 272597895518657874982871861 25556052704874175779644237)
            ·
              refine ⟨9583519764327815917366589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25556052704874175779644237 9583519764327815917366589)
              ·
                refine ⟨3593819911622930969012471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9583519764327815917366589 3593819911622930969012471)
                ·
                  refine ⟨5390729867434396453518707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593819911622930969012471 5390729867434396453518707)
                  ·
                    refine ⟨8086094801151594680278061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5390729867434396453518707 8086094801151594680278061)
                    ·
                      refine ⟨3032285550431848005104273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8086094801151594680278061 3032285550431848005104273)
                      ·
                        rfl

theorem cell23_5905355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 1, 1, 3].length) (baseStart_5905355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905355 prefixEnd_5905355 := by exact prefixLift 5905355
  have htrace : WordTrace (prefixWord ++ tailWord_5905355) baseStart_5905355 baseEnd_5905355 := by
    simpa [prefixWord, tailWord_5905355, baseEnd_5905355] using wordTrace_append hprefix tailTrace_5905355
  have hstable : (prefixWord ++ tailWord_5905355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905355).length < 2 ^ (prefixWord ++ tailWord_5905355).sum := by decide
  have hdescent : baseEnd_5905355 < baseStart_5905355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905361 : List Nat := [1, 2, 2, 1, 2, 1, 3, 5, 1, 1, 4]
def baseStart_5905361 : Nat := 118140960795 + 5905361 * 2 ^ 59
def prefixEnd_5905361 : Nat := 4983230072969 + 3 ^ 40 * 5905361 * 2
def baseEnd_5905361 : Nat := 3032288631315774981629245

theorem tailTrace_5905361 : CollatzResearch.WordTrace tailWord_5905361 prefixEnd_5905361 3032288631315774981629245 := by
  unfold tailWord_5905361
  simp only [CollatzResearch.WordTrace]
  refine ⟨215386210358893127208715937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143590806905928751472477291 215386210358893127208715937)
  ·
    refine ⟨161539657769169845406536953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215386210358893127208715937 161539657769169845406536953)
    ·
      refine ⟨121154743326877384054902715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161539657769169845406536953 121154743326877384054902715)
      ·
        refine ⟨181732114990316076082354073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121154743326877384054902715 181732114990316076082354073)
        ·
          refine ⟨136299086242737057061765555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181732114990316076082354073 136299086242737057061765555)
          ·
            refine ⟨204448629364105585592648333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136299086242737057061765555 204448629364105585592648333)
            ·
              refine ⟨76668236011539594597243125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204448629364105585592648333 76668236011539594597243125)
              ·
                refine ⟨7187647126081836993491543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76668236011539594597243125 7187647126081836993491543)
                ·
                  refine ⟨10781470689122755490237315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7187647126081836993491543 10781470689122755490237315)
                  ·
                    refine ⟨16172206033684133235355973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10781470689122755490237315 16172206033684133235355973)
                    ·
                      refine ⟨3032288631315774981629245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16172206033684133235355973 3032288631315774981629245)
                      ·
                        rfl

theorem cell23_5905361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_5905361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905361 prefixEnd_5905361 := by exact prefixLift 5905361
  have htrace : WordTrace (prefixWord ++ tailWord_5905361) baseStart_5905361 baseEnd_5905361 := by
    simpa [prefixWord, tailWord_5905361, baseEnd_5905361] using wordTrace_append hprefix tailTrace_5905361
  have hstable : (prefixWord ++ tailWord_5905361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905361).length < 2 ^ (prefixWord ++ tailWord_5905361).sum := by decide
  have hdescent : baseEnd_5905361 < baseStart_5905361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905365 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 2, 3, 2]
def baseStart_5905365 : Nat := 118140960795 + 5905365 * 2 ^ 59
def prefixEnd_5905365 : Nat := 4983230072969 + 3 ^ 40 * 5905365 * 2
def baseEnd_5905365 : Nat := 3032290685238392965979227

theorem tailTrace_5905365 : CollatzResearch.WordTrace tailWord_5905365 prefixEnd_5905365 3032290685238392965979227 := by
  unfold tailWord_5905365
  simp only [CollatzResearch.WordTrace]
  refine ⟨215386356250878635891861549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143590904167252423927907699 215386356250878635891861549)
  ·
    refine ⟨80769883594079488459448081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215386356250878635891861549 80769883594079488459448081)
    ·
      refine ⟨60577412695559616344586061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80769883594079488459448081 60577412695559616344586061)
      ·
        refine ⟨22716529760834856129219773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60577412695559616344586061 22716529760834856129219773)
        ·
          refine ⟨8518698660313071048457415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22716529760834856129219773 8518698660313071048457415)
          ·
            refine ⟨12778047990469606572686123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8518698660313071048457415 12778047990469606572686123)
            ·
              refine ⟨19167071985704409859029185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12778047990469606572686123 19167071985704409859029185)
              ·
                refine ⟨14375303989278307394271889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19167071985704409859029185 14375303989278307394271889)
                ·
                  refine ⟨10781477991958730545703917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14375303989278307394271889 10781477991958730545703917)
                  ·
                    refine ⟨4043054246984523954638969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10781477991958730545703917 4043054246984523954638969)
                    ·
                      refine ⟨3032290685238392965979227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043054246984523954638969 3032290685238392965979227)
                      ·
                        rfl

theorem cell23_5905365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_5905365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905365 prefixEnd_5905365 := by exact prefixLift 5905365
  have htrace : WordTrace (prefixWord ++ tailWord_5905365) baseStart_5905365 baseEnd_5905365 := by
    simpa [prefixWord, tailWord_5905365, baseEnd_5905365] using wordTrace_append hprefix tailTrace_5905365
  have hstable : (prefixWord ++ tailWord_5905365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905365).length < 2 ^ (prefixWord ++ tailWord_5905365).sum := by decide
  have hdescent : baseEnd_5905365 < baseStart_5905365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905384 : List Nat := [2, 1, 4, 1, 1, 1, 3, 10]
def baseStart_5905384 : Nat := 118140960795 + 5905384 * 2 ^ 59
def prefixEnd_5905384 : Nat := 4983230072969 + 3 ^ 40 * 5905384 * 2
def baseEnd_5905384 : Nat := 112307423754475125616357

theorem tailTrace_5905384 : CollatzResearch.WordTrace tailWord_5905384 prefixEnd_5905384 112307423754475125616357 := by
  unfold tailWord_5905384
  simp only [CollatzResearch.WordTrace]
  refine ⟨107693524618904901068401603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143591366158539868091202137 107693524618904901068401603)
  ·
    refine ⟨161540286928357351602602405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107693524618904901068401603 161540286928357351602602405)
    ·
      refine ⟨30288803799067003425487951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161540286928357351602602405 30288803799067003425487951)
      ·
        refine ⟨45433205698600505138231927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30288803799067003425487951 45433205698600505138231927)
        ·
          refine ⟨68149808547900757707347891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45433205698600505138231927 68149808547900757707347891)
          ·
            refine ⟨102224712821851136561021837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68149808547900757707347891 102224712821851136561021837)
            ·
              refine ⟨38334267308194176210383189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102224712821851136561021837 38334267308194176210383189)
              ·
                refine ⟨112307423754475125616357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38334267308194176210383189 112307423754475125616357)
                ·
                  rfl

theorem cell23_5905384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 10].length) (baseStart_5905384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905384 prefixEnd_5905384 := by exact prefixLift 5905384
  have htrace : WordTrace (prefixWord ++ tailWord_5905384) baseStart_5905384 baseEnd_5905384 := by
    simpa [prefixWord, tailWord_5905384, baseEnd_5905384] using wordTrace_append hprefix tailTrace_5905384
  have hstable : (prefixWord ++ tailWord_5905384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905384).length < 2 ^ (prefixWord ++ tailWord_5905384).sum := by decide
  have hdescent : baseEnd_5905384 < baseStart_5905384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905415 : List Nat := [1, 1, 4, 3, 1, 1, 5, 1, 1, 2, 3]
def baseStart_5905415 : Nat := 118140960795 + 5905415 * 2 ^ 59
def prefixEnd_5905415 : Nat := 4983230072969 + 3 ^ 40 * 5905415 * 2
def baseEnd_5905415 : Nat := 3032316359271117770353997

theorem tailTrace_5905415 : CollatzResearch.WordTrace tailWord_5905415 prefixEnd_5905415 3032316359271117770353997 := by
  unfold tailWord_5905415
  simp only [CollatzResearch.WordTrace]
  refine ⟨215388179900697494431181699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143592119933798329620787799 215388179900697494431181699)
  ·
    refine ⟨323082269851046241646772549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215388179900697494431181699 323082269851046241646772549)
    ·
      refine ⟨60577925597071170308769853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323082269851046241646772549 60577925597071170308769853)
      ·
        refine ⟨22716722098901688865788695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60577925597071170308769853 22716722098901688865788695)
        ·
          refine ⟨34075083148352533298683043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22716722098901688865788695 34075083148352533298683043)
          ·
            refine ⟨51112624722528799948024565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34075083148352533298683043 51112624722528799948024565)
            ·
              refine ⟨4791808567737074995127303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51112624722528799948024565 4791808567737074995127303)
              ·
                refine ⟨7187712851605612492690955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4791808567737074995127303 7187712851605612492690955)
                ·
                  refine ⟨10781569277408418739036433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7187712851605612492690955 10781569277408418739036433)
                  ·
                    refine ⟨8086176958056314054277325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10781569277408418739036433 8086176958056314054277325)
                    ·
                      refine ⟨3032316359271117770353997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8086176958056314054277325 3032316359271117770353997)
                      ·
                        rfl

theorem cell23_5905415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_5905415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905415 prefixEnd_5905415 := by exact prefixLift 5905415
  have htrace : WordTrace (prefixWord ++ tailWord_5905415) baseStart_5905415 baseEnd_5905415 := by
    simpa [prefixWord, tailWord_5905415, baseEnd_5905415] using wordTrace_append hprefix tailTrace_5905415
  have hstable : (prefixWord ++ tailWord_5905415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905415).length < 2 ^ (prefixWord ++ tailWord_5905415).sum := by decide
  have hdescent : baseEnd_5905415 < baseStart_5905415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905429 : List Nat := [1, 3, 2, 1, 4, 1, 4, 2, 1, 2, 2]
def baseStart_5905429 : Nat := 118140960795 + 5905429 * 2 ^ 59
def prefixEnd_5905429 : Nat := 4983230072969 + 3 ^ 40 * 5905429 * 2
def baseEnd_5905429 : Nat := 3032323548000280715578933

theorem tailTrace_5905429 : CollatzResearch.WordTrace tailWord_5905429 prefixEnd_5905429 3032323548000280715578933 := by
  unfold tailWord_5905429
  simp only [CollatzResearch.WordTrace]
  refine ⟨215388690522646774822191341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143592460348431183214794227 215388690522646774822191341)
  ·
    refine ⟨80770758945992540558321753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215388690522646774822191341 80770758945992540558321753)
    ·
      refine ⟨60578069209494405418741315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80770758945992540558321753 60578069209494405418741315)
      ·
        refine ⟨90867103814241608128111973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60578069209494405418741315 90867103814241608128111973)
        ·
          refine ⟨17037581965170301524020995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90867103814241608128111973 17037581965170301524020995)
          ·
            refine ⟨25556372947755452286031493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17037581965170301524020995 25556372947755452286031493)
            ·
              refine ⟨4791819927704147303630905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25556372947755452286031493 4791819927704147303630905)
              ·
                refine ⟨3593864945778110477723179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4791819927704147303630905 3593864945778110477723179)
                ·
                  refine ⟨5390797418667165716584769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593864945778110477723179 5390797418667165716584769)
                  ·
                    refine ⟨4043098064000374287438577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5390797418667165716584769 4043098064000374287438577)
                    ·
                      refine ⟨3032323548000280715578933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043098064000374287438577 3032323548000280715578933)
                      ·
                        rfl

theorem cell23_5905429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_5905429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905429 prefixEnd_5905429 := by exact prefixLift 5905429
  have htrace : WordTrace (prefixWord ++ tailWord_5905429) baseStart_5905429 baseEnd_5905429 := by
    simpa [prefixWord, tailWord_5905429, baseEnd_5905429] using wordTrace_append hprefix tailTrace_5905429
  have hstable : (prefixWord ++ tailWord_5905429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905429).length < 2 ^ (prefixWord ++ tailWord_5905429).sum := by decide
  have hdescent : baseEnd_5905429 < baseStart_5905429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905431 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 2, 7]
def baseStart_5905431 : Nat := 118140960795 + 5905431 * 2 ^ 59
def prefixEnd_5905431 : Nat := 4983230072969 + 3 ^ 40 * 5905431 * 2
def baseEnd_5905431 : Nat := 1010774858320529902584641

theorem tailTrace_5905431 : CollatzResearch.WordTrace tailWord_5905431 prefixEnd_5905431 1010774858320529902584641 := by
  unfold tailWord_5905431
  simp only [CollatzResearch.WordTrace]
  refine ⟨215388763468639529163764147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143592508979093019442509431 215388763468639529163764147)
  ·
    refine ⟨323083145202959293745646221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215388763468639529163764147 323083145202959293745646221)
    ·
      refine ⟨121156179451109735154617333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323083145202959293745646221 121156179451109735154617333)
      ·
        refine ⟨11358391823541537670745375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121156179451109735154617333 11358391823541537670745375)
        ·
          refine ⟨17037587735312306506118063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11358391823541537670745375 17037587735312306506118063)
          ·
            refine ⟨25556381602968459759177095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17037587735312306506118063 25556381602968459759177095)
            ·
              refine ⟨38334572404452689638765643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25556381602968459759177095 38334572404452689638765643)
              ·
                refine ⟨57501858606679034458148465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38334572404452689638765643 57501858606679034458148465)
                ·
                  refine ⟨43126393955009275843611349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57501858606679034458148465 43126393955009275843611349)
                  ·
                    refine ⟨1010774858320529902584641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43126393955009275843611349 1010774858320529902584641)
                    ·
                      rfl

theorem cell23_5905431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_5905431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905431 prefixEnd_5905431 := by exact prefixLift 5905431
  have htrace : WordTrace (prefixWord ++ tailWord_5905431) baseStart_5905431 baseEnd_5905431 := by
    simpa [prefixWord, tailWord_5905431, baseEnd_5905431] using wordTrace_append hprefix tailTrace_5905431
  have hstable : (prefixWord ++ tailWord_5905431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905431).length < 2 ^ (prefixWord ++ tailWord_5905431).sum := by decide
  have hdescent : baseEnd_5905431 < baseStart_5905431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905568 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 5, 4]
def baseStart_5905568 : Nat := 118140960795 + 5905568 * 2 ^ 59
def prefixEnd_5905568 : Nat := 4983230072969 + 3 ^ 40 * 5905568 * 2
def baseEnd_5905568 : Nat := 1010798307270418557246931

theorem tailTrace_5905568 : CollatzResearch.WordTrace tailWord_5905568 prefixEnd_5905568 1010798307270418557246931 := by
  unfold tailWord_5905568
  simp only [CollatzResearch.WordTrace]
  refine ⟨107696880134571600780750679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143595840179428801041000905 107696880134571600780750679)
  ·
    refine ⟨161545320201857401171126019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107696880134571600780750679 161545320201857401171126019)
    ·
      refine ⟨242317980302786101756689029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161545320201857401171126019 242317980302786101756689029)
      ·
        refine ⟨45434621306772394079379193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242317980302786101756689029 45434621306772394079379193)
        ·
          refine ⟨34075965980079295559534395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45434621306772394079379193 34075965980079295559534395)
          ·
            refine ⟨51113948970118943339301593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34075965980079295559534395 51113948970118943339301593)
            ·
              refine ⟨38335461727589207504476195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51113948970118943339301593 38335461727589207504476195)
              ·
                refine ⟨57503192591383811256714293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38335461727589207504476195 57503192591383811256714293)
                ·
                  refine ⟨5390924305442232305316965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57503192591383811256714293 5390924305442232305316965)
                  ·
                    refine ⟨1010798307270418557246931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5390924305442232305316965 1010798307270418557246931)
                    ·
                      rfl

theorem cell23_5905568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 5, 4].length) (baseStart_5905568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905568 prefixEnd_5905568 := by exact prefixLift 5905568
  have htrace : WordTrace (prefixWord ++ tailWord_5905568) baseStart_5905568 baseEnd_5905568 := by
    simpa [prefixWord, tailWord_5905568, baseEnd_5905568] using wordTrace_append hprefix tailTrace_5905568
  have hstable : (prefixWord ++ tailWord_5905568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905568).length < 2 ^ (prefixWord ++ tailWord_5905568).sum := by decide
  have hdescent : baseEnd_5905568 < baseStart_5905568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905571 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 4]
def baseStart_5905571 : Nat := 118140960795 + 5905571 * 2 ^ 59
def prefixEnd_5905571 : Nat := 4983230072969 + 3 ^ 40 * 5905571 * 2
def baseEnd_5905571 : Nat := 3032396462253219160003279

theorem tailTrace_5905571 : CollatzResearch.WordTrace tailWord_5905571 prefixEnd_5905571 3032396462253219160003279 := by
  unfold tailWord_5905571
  simp only [CollatzResearch.WordTrace]
  refine ⟨215393869688132333073860567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143595913125421555382573711 215393869688132333073860567)
  ·
    refine ⟨323090804532198499610790851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215393869688132333073860567 323090804532198499610790851)
    ·
      refine ⟨484636206798297749416186277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323090804532198499610790851 484636206798297749416186277)
      ·
        refine ⟨90869288774680828015534927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 484636206798297749416186277 90869288774680828015534927)
        ·
          refine ⟨136303933162021242023302391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90869288774680828015534927 136303933162021242023302391)
          ·
            refine ⟨204455899743031863034953587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136303933162021242023302391 204455899743031863034953587)
            ·
              refine ⟨306683849614547794552430381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204455899743031863034953587 306683849614547794552430381)
              ·
                refine ⟨115006443605455422957161393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306683849614547794552430381 115006443605455422957161393)
                ·
                  refine ⟨86254832704091567217871045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115006443605455422957161393 86254832704091567217871045)
                  ·
                    refine ⟨16172781132017168853350821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86254832704091567217871045 16172781132017168853350821)
                    ·
                      refine ⟨3032396462253219160003279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16172781132017168853350821 3032396462253219160003279)
                      ·
                        rfl

theorem cell23_5905571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_5905571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905571 prefixEnd_5905571 := by exact prefixLift 5905571
  have htrace : WordTrace (prefixWord ++ tailWord_5905571) baseStart_5905571 baseEnd_5905571 := by
    simpa [prefixWord, tailWord_5905571, baseEnd_5905571] using wordTrace_append hprefix tailTrace_5905571
  have hstable : (prefixWord ++ tailWord_5905571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905571).length < 2 ^ (prefixWord ++ tailWord_5905571).sum := by decide
  have hdescent : baseEnd_5905571 < baseStart_5905571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905575 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_5905575 : Nat := 118140960795 + 5905575 * 2 ^ 59
def prefixEnd_5905575 : Nat := 4983230072969 + 3 ^ 40 * 5905575 * 2
def baseEnd_5905575 : Nat := 3032398516175837144353261

theorem tailTrace_5905575 : CollatzResearch.WordTrace tailWord_5905575 prefixEnd_5905575 3032398516175837144353261 := by
  unfold tailWord_5905575
  simp only [CollatzResearch.WordTrace]
  refine ⟨215394015580117841757006179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143596010386745227838004119 215394015580117841757006179)
  ·
    refine ⟨323091023370176762635509269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215394015580117841757006179 323091023370176762635509269)
    ·
      refine ⟨15144891720477035748539497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 323091023370176762635509269 15144891720477035748539497)
      ·
        refine ⟨11358668790357776811404623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15144891720477035748539497 11358668790357776811404623)
        ·
          refine ⟨17038003185536665217106935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11358668790357776811404623 17038003185536665217106935)
          ·
            refine ⟨25557004778304997825660403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17038003185536665217106935 25557004778304997825660403)
            ·
              refine ⟨38335507167457496738490605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25557004778304997825660403 38335507167457496738490605)
              ·
                refine ⟨14375815187796561276933977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38335507167457496738490605 14375815187796561276933977)
                ·
                  refine ⟨10781861390847420957700483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14375815187796561276933977 10781861390847420957700483)
                  ·
                    refine ⟨16172792086271131436550725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10781861390847420957700483 16172792086271131436550725)
                    ·
                      refine ⟨3032398516175837144353261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16172792086271131436550725 3032398516175837144353261)
                      ·
                        rfl

theorem cell23_5905575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_5905575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905575 prefixEnd_5905575 := by exact prefixLift 5905575
  have htrace : WordTrace (prefixWord ++ tailWord_5905575) baseStart_5905575 baseEnd_5905575 := by
    simpa [prefixWord, tailWord_5905575, baseEnd_5905575] using wordTrace_append hprefix tailTrace_5905575
  have hstable : (prefixWord ++ tailWord_5905575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905575).length < 2 ^ (prefixWord ++ tailWord_5905575).sum := by decide
  have hdescent : baseEnd_5905575 < baseStart_5905575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905629 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_5905629 : Nat := 118140960795 + 5905629 * 2 ^ 59
def prefixEnd_5905629 : Nat := 4983230072969 + 3 ^ 40 * 5905629 * 2
def baseEnd_5905629 : Nat := 3032426244131179933078013

theorem tailTrace_5905629 : CollatzResearch.WordTrace tailWord_5905629 prefixEnd_5905629 3032426244131179933078013 := by
  unfold tailWord_5905629
  simp only [CollatzResearch.WordTrace]
  refine ⟨215395985121922208979471941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143597323414614805986314627 215395985121922208979471941)
  ·
    refine ⟨40386747210360414183650989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215395985121922208979471941 40386747210360414183650989)
    ·
      refine ⟨15145030203885155318869121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40386747210360414183650989 15145030203885155318869121)
      ·
        refine ⟨11358772652913866489151841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15145030203885155318869121 11358772652913866489151841)
        ·
          refine ⟨8519079489685399866863881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11358772652913866489151841 8519079489685399866863881)
          ·
            refine ⟨6389309617264049900147911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8519079489685399866863881 6389309617264049900147911)
            ·
              refine ⟨9583964425896074850221867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389309617264049900147911 9583964425896074850221867)
              ·
                refine ⟨14375946638844112275332801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9583964425896074850221867 14375946638844112275332801)
                ·
                  refine ⟨10781959979133084206499601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14375946638844112275332801 10781959979133084206499601)
                  ·
                    refine ⟨8086469984349813154874701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10781959979133084206499601 8086469984349813154874701)
                    ·
                      refine ⟨3032426244131179933078013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8086469984349813154874701 3032426244131179933078013)
                      ·
                        rfl

theorem cell23_5905629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_5905629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905629 prefixEnd_5905629 := by exact prefixLift 5905629
  have htrace : WordTrace (prefixWord ++ tailWord_5905629) baseStart_5905629 baseEnd_5905629 := by
    simpa [prefixWord, tailWord_5905629, baseEnd_5905629] using wordTrace_append hprefix tailTrace_5905629
  have hstable : (prefixWord ++ tailWord_5905629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905629).length < 2 ^ (prefixWord ++ tailWord_5905629).sum := by decide
  have hdescent : baseEnd_5905629 < baseStart_5905629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905675 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 1, 6]
def baseStart_5905675 : Nat := 118140960795 + 5905675 * 2 ^ 59
def prefixEnd_5905675 : Nat := 4983230072969 + 3 ^ 40 * 5905675 * 2
def baseEnd_5905675 : Nat := 1010816621413762251034267

theorem tailTrace_5905675 : CollatzResearch.WordTrace tailWord_5905675 prefixEnd_5905675 1010816621413762251034267 := by
  unfold tailWord_5905675
  simp only [CollatzResearch.WordTrace]
  refine ⟨215397662879755558835646479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143598441919837039223764319 215397662879755558835646479)
  ·
    refine ⟨323096494319633338253469719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215397662879755558835646479 323096494319633338253469719)
    ·
      refine ⟨484644741479450007380204579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323096494319633338253469719 484644741479450007380204579)
      ·
        refine ⟨726967112219175011070306869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484644741479450007380204579 726967112219175011070306869)
        ·
          refine ⟨68153166770547657287841269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 726967112219175011070306869 68153166770547657287841269)
          ·
            refine ⟨6389359384738842870735119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68153166770547657287841269 6389359384738842870735119)
            ·
              refine ⟨9584039077108264306102679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389359384738842870735119 9584039077108264306102679)
              ·
                refine ⟨14376058615662396459154019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9584039077108264306102679 14376058615662396459154019)
                ·
                  refine ⟨21564087923493594688731029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14376058615662396459154019 21564087923493594688731029)
                  ·
                    refine ⟨1010816621413762251034267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21564087923493594688731029 1010816621413762251034267)
                    ·
                      rfl

theorem cell23_5905675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 6].length) (baseStart_5905675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905675 prefixEnd_5905675 := by exact prefixLift 5905675
  have htrace : WordTrace (prefixWord ++ tailWord_5905675) baseStart_5905675 baseEnd_5905675 := by
    simpa [prefixWord, tailWord_5905675, baseEnd_5905675] using wordTrace_append hprefix tailTrace_5905675
  have hstable : (prefixWord ++ tailWord_5905675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905675).length < 2 ^ (prefixWord ++ tailWord_5905675).sum := by decide
  have hdescent : baseEnd_5905675 < baseStart_5905675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905688 : List Nat := [2, 1, 2, 3, 1, 4, 1, 9]
def baseStart_5905688 : Nat := 118140960795 + 5905688 * 2 ^ 59
def prefixEnd_5905688 : Nat := 4983230072969 + 3 ^ 40 * 5905688 * 2
def baseEnd_5905688 : Nat := 112313205166288711194083

theorem tailTrace_5905688 : CollatzResearch.WordTrace tailWord_5905688 prefixEnd_5905688 112313205166288711194083 := by
  unfold tailWord_5905688
  simp only [CollatzResearch.WordTrace]
  refine ⟨107699068514354231027934859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143598758019138974703913145 107699068514354231027934859)
  ·
    refine ⟨161548602771531346541902289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107699068514354231027934859 161548602771531346541902289)
    ·
      refine ⟨121161452078648509906426717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161548602771531346541902289 121161452078648509906426717)
      ·
        refine ⟨45435544529493191214910019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121161452078648509906426717 45435544529493191214910019)
        ·
          refine ⟨68153316794239786822365029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45435544529493191214910019 68153316794239786822365029)
          ·
            refine ⟨12778746898919960029193443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68153316794239786822365029 12778746898919960029193443)
            ·
              refine ⟨19168120348379940043790165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12778746898919960029193443 19168120348379940043790165)
              ·
                refine ⟨112313205166288711194083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19168120348379940043790165 112313205166288711194083)
                ·
                  rfl

theorem cell23_5905688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 9].length) (baseStart_5905688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905688 prefixEnd_5905688 := by exact prefixLift 5905688
  have htrace : WordTrace (prefixWord ++ tailWord_5905688) baseStart_5905688 baseEnd_5905688 := by
    simpa [prefixWord, tailWord_5905688, baseEnd_5905688] using wordTrace_append hprefix tailTrace_5905688
  have hstable : (prefixWord ++ tailWord_5905688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905688).length < 2 ^ (prefixWord ++ tailWord_5905688).sum := by decide
  have hdescent : baseEnd_5905688 < baseStart_5905688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905742 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2]
def baseStart_5905742 : Nat := 118140960795 + 5905742 * 2 ^ 59
def prefixEnd_5905742 : Nat := 4983230072969 + 3 ^ 40 * 5905742 * 2
def baseEnd_5905742 : Nat := 3032484267445137990964993

theorem tailTrace_5905742 : CollatzResearch.WordTrace tailWord_5905742 prefixEnd_5905742 3032484267445137990964993 := by
  unfold tailWord_5905742
  simp only [CollatzResearch.WordTrace]
  refine ⟨26925013321314103659791935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143600071047008552852223653 26925013321314103659791935)
  ·
    refine ⟨40387519981971155489687903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26925013321314103659791935 40387519981971155489687903)
    ·
      refine ⟨60581279972956733234531855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40387519981971155489687903 60581279972956733234531855)
      ·
        refine ⟨90871919959435099851797783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60581279972956733234531855 90871919959435099851797783)
        ·
          refine ⟨136307879939152649777696675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90871919959435099851797783 136307879939152649777696675)
          ·
            refine ⟨204461819908728974666545013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136307879939152649777696675 204461819908728974666545013)
            ·
              refine ⟨19168295616443341374988595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 204461819908728974666545013 19168295616443341374988595)
              ·
                refine ⟨28752443424665012062482893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19168295616443341374988595 28752443424665012062482893)
                ·
                  refine ⟨10782166284249379523431085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28752443424665012062482893 10782166284249379523431085)
                  ·
                    refine ⟨4043312356593517321286657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10782166284249379523431085 4043312356593517321286657)
                    ·
                      refine ⟨3032484267445137990964993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043312356593517321286657 3032484267445137990964993)
                      ·
                        rfl

theorem cell23_5905742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_5905742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905742 prefixEnd_5905742 := by exact prefixLift 5905742
  have htrace : WordTrace (prefixWord ++ tailWord_5905742) baseStart_5905742 baseEnd_5905742 := by
    simpa [prefixWord, tailWord_5905742, baseEnd_5905742] using wordTrace_append hprefix tailTrace_5905742
  have hstable : (prefixWord ++ tailWord_5905742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905742).length < 2 ^ (prefixWord ++ tailWord_5905742).sum := by decide
  have hdescent : baseEnd_5905742 < baseStart_5905742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905750 : List Nat := [5, 2, 3, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_5905750 : Nat := 118140960795 + 5905750 * 2 ^ 59
def prefixEnd_5905750 : Nat := 4983230072969 + 3 ^ 40 * 5905750 * 2
def baseEnd_5905750 : Nat := 3032488375290373959664957

theorem tailTrace_5905750 : CollatzResearch.WordTrace tailWord_5905750 prefixEnd_5905750 3032488375290373959664957 := by
  unfold tailWord_5905750
  simp only [CollatzResearch.WordTrace]
  refine ⟨13462524897155240415289169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143600265569655897763084469 13462524897155240415289169)
  ·
    refine ⟨10096893672866430311466877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13462524897155240415289169 10096893672866430311466877)
    ·
      refine ⟨3786335127324911366800079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10096893672866430311466877 3786335127324911366800079)
      ·
        refine ⟨5679502690987367050200119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786335127324911366800079 5679502690987367050200119)
        ·
          refine ⟨8519254036481050575300179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5679502690987367050200119 8519254036481050575300179)
          ·
            refine ⟨12778881054721575862950269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8519254036481050575300179 12778881054721575862950269)
            ·
              refine ⟨4792080395520590948606351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12778881054721575862950269 4792080395520590948606351)
              ·
                refine ⟨7188120593280886422909527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4792080395520590948606351 7188120593280886422909527)
                ·
                  refine ⟨10782180889921329634364291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7188120593280886422909527 10782180889921329634364291)
                  ·
                    refine ⟨16173271334881994451546437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10782180889921329634364291 16173271334881994451546437)
                    ·
                      refine ⟨3032488375290373959664957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16173271334881994451546437 3032488375290373959664957)
                      ·
                        rfl

theorem cell23_5905750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_5905750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905750 prefixEnd_5905750 := by exact prefixLift 5905750
  have htrace : WordTrace (prefixWord ++ tailWord_5905750) baseStart_5905750 baseEnd_5905750 := by
    simpa [prefixWord, tailWord_5905750, baseEnd_5905750] using wordTrace_append hprefix tailTrace_5905750
  have hstable : (prefixWord ++ tailWord_5905750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905750).length < 2 ^ (prefixWord ++ tailWord_5905750).sum := by decide
  have hdescent : baseEnd_5905750 < baseStart_5905750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905789 : List Nat := [1, 4, 1, 1, 2, 2, 1, 5, 2, 2, 2]
def baseStart_5905789 : Nat := 118140960795 + 5905789 * 2 ^ 59
def prefixEnd_5905789 : Nat := 4983230072969 + 3 ^ 40 * 5905789 * 2
def baseEnd_5905789 : Nat := 3032508401035899307077277

theorem tailTrace_5905789 : CollatzResearch.WordTrace tailWord_5905789 prefixEnd_5905789 3032508401035899307077277 := by
  unfold tailWord_5905789
  simp only [CollatzResearch.WordTrace]
  refine ⟨215401820801342556305296421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143601213867561704203530947 215401820801342556305296421)
  ·
    refine ⟨40387841400251729307243079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215401820801342556305296421 40387841400251729307243079)
    ·
      refine ⟨60581762100377593960864619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40387841400251729307243079 60581762100377593960864619)
      ·
        refine ⟨90872643150566390941296929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60581762100377593960864619 90872643150566390941296929)
        ·
          refine ⟨68154482362924793205972697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90872643150566390941296929 68154482362924793205972697)
          ·
            refine ⟨51115861772193594904479523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68154482362924793205972697 51115861772193594904479523)
            ·
              refine ⟨76673792658290392356719285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51115861772193594904479523 76673792658290392356719285)
              ·
                refine ⟨7188168061714724283442433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76673792658290392356719285 7188168061714724283442433)
                ·
                  refine ⟨5391126046286043212581825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7188168061714724283442433 5391126046286043212581825)
                  ·
                    refine ⟨4043344534714532409436369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5391126046286043212581825 4043344534714532409436369)
                    ·
                      refine ⟨3032508401035899307077277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043344534714532409436369 3032508401035899307077277)
                      ·
                        rfl

theorem cell23_5905789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_5905789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905789 prefixEnd_5905789 := by exact prefixLift 5905789
  have htrace : WordTrace (prefixWord ++ tailWord_5905789) baseStart_5905789 baseEnd_5905789 := by
    simpa [prefixWord, tailWord_5905789, baseEnd_5905789] using wordTrace_append hprefix tailTrace_5905789
  have hstable : (prefixWord ++ tailWord_5905789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905789).length < 2 ^ (prefixWord ++ tailWord_5905789).sum := by decide
  have hdescent : baseEnd_5905789 < baseStart_5905789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905795 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 7]
def baseStart_5905795 : Nat := 118140960795 + 5905795 * 2 ^ 59
def prefixEnd_5905795 : Nat := 4983230072969 + 3 ^ 40 * 5905795 * 2
def baseEnd_5905795 : Nat := 336945720213314031511361

theorem tailTrace_5905795 : CollatzResearch.WordTrace tailWord_5905795 prefixEnd_5905795 336945720213314031511361 := by
  unfold tailWord_5905795
  simp only [CollatzResearch.WordTrace]
  refine ⟨215402039639320819330014839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143601359759547212886676559 215402039639320819330014839)
  ·
    refine ⟨323103059458981228995022259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215402039639320819330014839 323103059458981228995022259)
    ·
      refine ⟨484654589188471843492533389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323103059458981228995022259 484654589188471843492533389)
      ·
        refine ⟨181745470945676941309700021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 484654589188471843492533389 181745470945676941309700021)
        ·
          refine ⟨17038637901157213247784377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181745470945676941309700021 17038637901157213247784377)
          ·
            refine ⟨12778978425867909935838283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17038637901157213247784377 12778978425867909935838283)
            ·
              refine ⟨19168467638801864903757425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12778978425867909935838283 19168467638801864903757425)
              ·
                refine ⟨14376350729101398677818069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19168467638801864903757425 14376350729101398677818069)
                ·
                  refine ⟨336945720213314031511361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14376350729101398677818069 336945720213314031511361)
                  ·
                    rfl

theorem cell23_5905795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 7].length) (baseStart_5905795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905795 prefixEnd_5905795 := by exact prefixLift 5905795
  have htrace : WordTrace (prefixWord ++ tailWord_5905795) baseStart_5905795 baseEnd_5905795 := by
    simpa [prefixWord, tailWord_5905795, baseEnd_5905795] using wordTrace_append hprefix tailTrace_5905795
  have hstable : (prefixWord ++ tailWord_5905795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905795).length < 2 ^ (prefixWord ++ tailWord_5905795).sum := by decide
  have hdescent : baseEnd_5905795 < baseStart_5905795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905810 : List Nat := [3, 2, 3, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_5905810 : Nat := 118140960795 + 5905810 * 2 ^ 59
def prefixEnd_5905810 : Nat := 4983230072969 + 3 ^ 40 * 5905810 * 2
def baseEnd_5905810 : Nat := 3032519184129643724914681

theorem tailTrace_5905810 : CollatzResearch.WordTrace tailWord_5905810 prefixEnd_5905810 3032519184129643724914681 := by
  unfold tailWord_5905810
  simp only [CollatzResearch.WordTrace]
  refine ⟨53850646683566619222952721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143601724489510984594540589 53850646683566619222952721)
  ·
    refine ⟨40387985012674964417214541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53850646683566619222952721 40387985012674964417214541)
    ·
      refine ⟨15145494379753111656455453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40387985012674964417214541 15145494379753111656455453)
      ·
        refine ⟨5679560392407416871170795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15145494379753111656455453 5679560392407416871170795)
        ·
          refine ⟨8519340588611125306756193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5679560392407416871170795 8519340588611125306756193)
          ·
            refine ⟨6389505441458343980067145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8519340588611125306756193 6389505441458343980067145)
            ·
              refine ⟨4792129081093757985050359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6389505441458343980067145 4792129081093757985050359)
              ·
                refine ⟨7188193621640636977575539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4792129081093757985050359 7188193621640636977575539)
                ·
                  refine ⟨10782290432460955466363309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7188193621640636977575539 10782290432460955466363309)
                  ·
                    refine ⟨4043358912172858299886241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10782290432460955466363309 4043358912172858299886241)
                    ·
                      refine ⟨3032519184129643724914681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043358912172858299886241 3032519184129643724914681)
                      ·
                        rfl

theorem cell23_5905810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_5905810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905810 prefixEnd_5905810 := by exact prefixLift 5905810
  have htrace : WordTrace (prefixWord ++ tailWord_5905810) baseStart_5905810 baseEnd_5905810 := by
    simpa [prefixWord, tailWord_5905810, baseEnd_5905810] using wordTrace_append hprefix tailTrace_5905810
  have hstable : (prefixWord ++ tailWord_5905810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905810).length < 2 ^ (prefixWord ++ tailWord_5905810).sum := by decide
  have hdescent : baseEnd_5905810 < baseStart_5905810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905882 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3]
def baseStart_5905882 : Nat := 118140960795 + 5905882 * 2 ^ 59
def prefixEnd_5905882 : Nat := 4983230072969 + 3 ^ 40 * 5905882 * 2
def baseEnd_5905882 : Nat := 3032556154736767443214349

theorem tailTrace_5905882 : CollatzResearch.WordTrace tailWord_5905882 prefixEnd_5905882 3032556154736767443214349 := by
  unfold tailWord_5905882
  simp only [CollatzResearch.WordTrace]
  refine ⟨53851303197501408297107975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143603475193337088792287933 53851303197501408297107975)
  ·
    refine ⟨80776954796252112445661963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53851303197501408297107975 80776954796252112445661963)
    ·
      refine ⟨121165432194378168668492945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80776954796252112445661963 121165432194378168668492945)
      ·
        refine ⟨90874074145783626501369709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121165432194378168668492945 90874074145783626501369709)
        ·
          refine ⟨34077777804668859938013641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90874074145783626501369709 34077777804668859938013641)
          ·
            refine ⟨25558333353501644953510231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34077777804668859938013641 25558333353501644953510231)
            ·
              refine ⟨38337500030252467430265347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25558333353501644953510231 38337500030252467430265347)
              ·
                refine ⟨57506250045378701145398021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38337500030252467430265347 57506250045378701145398021)
                ·
                  refine ⟨10782421883508506464762129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57506250045378701145398021 10782421883508506464762129)
                  ·
                    refine ⟨8086816412631379848571597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10782421883508506464762129 8086816412631379848571597)
                    ·
                      refine ⟨3032556154736767443214349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8086816412631379848571597 3032556154736767443214349)
                      ·
                        rfl

theorem cell23_5905882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_5905882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905882 prefixEnd_5905882 := by exact prefixLift 5905882
  have htrace : WordTrace (prefixWord ++ tailWord_5905882) baseStart_5905882 baseEnd_5905882 := by
    simpa [prefixWord, tailWord_5905882, baseEnd_5905882] using wordTrace_append hprefix tailTrace_5905882
  have hstable : (prefixWord ++ tailWord_5905882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905882).length < 2 ^ (prefixWord ++ tailWord_5905882).sum := by decide
  have hdescent : baseEnd_5905882 < baseStart_5905882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905889 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 3, 4]
def baseStart_5905889 : Nat := 118140960795 + 5905889 * 2 ^ 59
def prefixEnd_5905889 : Nat := 4983230072969 + 3 ^ 40 * 5905889 * 2
def baseEnd_5905889 : Nat := 1010853249700449638608939

theorem tailTrace_5905889 : CollatzResearch.WordTrace tailWord_5905889 prefixEnd_5905889 1010853249700449638608939 := by
  unfold tailWord_5905889
  simp only [CollatzResearch.WordTrace]
  refine ⟨215405468100980273383936721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143603645400653515589291147 215405468100980273383936721)
  ·
    refine ⟨161554101075735205037952541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215405468100980273383936721 161554101075735205037952541)
    ·
      refine ⟨60582787903400701889232203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161554101075735205037952541 60582787903400701889232203)
      ·
        refine ⟨90874181855101052833848305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60582787903400701889232203 90874181855101052833848305)
        ·
          refine ⟨68155636391325789625386229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90874181855101052833848305 68155636391325789625386229)
          ·
            refine ⟨6389590911686792777379959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68155636391325789625386229 6389590911686792777379959)
            ·
              refine ⟨9584386367530189166069939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389590911686792777379959 9584386367530189166069939)
              ·
                refine ⟨14376579551295283749104909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9584386367530189166069939 14376579551295283749104909)
                ·
                  refine ⟨5391217331735731405914341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14376579551295283749104909 5391217331735731405914341)
                  ·
                    refine ⟨1010853249700449638608939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5391217331735731405914341 1010853249700449638608939)
                    ·
                      rfl

theorem cell23_5905889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_5905889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905889 prefixEnd_5905889 := by exact prefixLift 5905889
  have htrace : WordTrace (prefixWord ++ tailWord_5905889) baseStart_5905889 baseEnd_5905889 := by
    simpa [prefixWord, tailWord_5905889, baseEnd_5905889] using wordTrace_append hprefix tailTrace_5905889
  have hstable : (prefixWord ++ tailWord_5905889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905889).length < 2 ^ (prefixWord ++ tailWord_5905889).sum := by decide
  have hdescent : baseEnd_5905889 < baseStart_5905889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905902 : List Nat := [4, 1, 2, 1, 2, 1, 3, 3, 6]
def baseStart_5905902 : Nat := 118140960795 + 5905902 * 2 ^ 59
def prefixEnd_5905902 : Nat := 4983230072969 + 3 ^ 40 * 5905902 * 2
def baseEnd_5905902 : Nat := 336951824927761929440473

theorem tailTrace_5905902 : CollatzResearch.WordTrace tailWord_5905902 prefixEnd_5905902 336951824927761929440473 := by
  unfold tailWord_5905902
  simp only [CollatzResearch.WordTrace]
  refine ⟨26925742781241647075519995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143603961499955451069439973 26925742781241647075519995)
  ·
    refine ⟨40388614171862470613279993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26925742781241647075519995 40388614171862470613279993)
    ·
      refine ⟨30291460628896852959959995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40388614171862470613279993 30291460628896852959959995)
      ·
        refine ⟨45437190943345279439939993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30291460628896852959959995 45437190943345279439939993)
        ·
          refine ⟨34077893207508959579954995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45437190943345279439939993 34077893207508959579954995)
          ·
            refine ⟨51116839811263439369932493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34077893207508959579954995 51116839811263439369932493)
            ·
              refine ⟨19168814929223789763724685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51116839811263439369932493 19168814929223789763724685)
              ·
                refine ⟨7188305598458921161396757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19168814929223789763724685 7188305598458921161396757)
                ·
                  refine ⟨336951824927761929440473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7188305598458921161396757 336951824927761929440473)
                  ·
                    rfl

theorem cell23_5905902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_5905902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905902 prefixEnd_5905902 := by exact prefixLift 5905902
  have htrace : WordTrace (prefixWord ++ tailWord_5905902) baseStart_5905902 baseEnd_5905902 := by
    simpa [prefixWord, tailWord_5905902, baseEnd_5905902] using wordTrace_append hprefix tailTrace_5905902
  have hstable : (prefixWord ++ tailWord_5905902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905902).length < 2 ^ (prefixWord ++ tailWord_5905902).sum := by decide
  have hdescent : baseEnd_5905902 < baseStart_5905902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905915 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 3, 5]
def baseStart_5905915 : Nat := 118140960795 + 5905915 * 2 ^ 59
def prefixEnd_5905915 : Nat := 4983230072969 + 3 ^ 40 * 5905915 * 2
def baseEnd_5905915 : Nat := 1010857699866121938033899

theorem tailTrace_5905915 : CollatzResearch.WordTrace tailWord_5905915 prefixEnd_5905915 1010857699866121938033899 := by
  unfold tailWord_5905915
  simp only [CollatzResearch.WordTrace]
  refine ⟨215406416398886079824383199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143604277599257386549588799 215406416398886079824383199)
  ·
    refine ⟨323109624598329119736574799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215406416398886079824383199 323109624598329119736574799)
    ·
      refine ⟨484664436897493679604862199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323109624598329119736574799 484664436897493679604862199)
      ·
        refine ⟨726996655346240519407293299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484664436897493679604862199 726996655346240519407293299)
        ·
          refine ⟨1090494983019360779110939949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726996655346240519407293299 1090494983019360779110939949)
          ·
            refine ⟨408935618632260292166602481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1090494983019360779110939949 408935618632260292166602481)
            ·
              refine ⟨306701713974195219124951861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408935618632260292166602481 306701713974195219124951861)
              ·
                refine ⟨28753285685080801792964237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 306701713974195219124951861 28753285685080801792964237)
                ·
                  refine ⟨10782482131905300672361589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28753285685080801792964237 10782482131905300672361589)
                  ·
                    refine ⟨1010857699866121938033899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10782482131905300672361589 1010857699866121938033899)
                    ·
                      rfl

theorem cell23_5905915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 5].length) (baseStart_5905915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905915 prefixEnd_5905915 := by exact prefixLift 5905915
  have htrace : WordTrace (prefixWord ++ tailWord_5905915) baseStart_5905915 baseEnd_5905915 := by
    simpa [prefixWord, tailWord_5905915, baseEnd_5905915] using wordTrace_append hprefix tailTrace_5905915
  have hstable : (prefixWord ++ tailWord_5905915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905915).length < 2 ^ (prefixWord ++ tailWord_5905915).sum := by decide
  have hdescent : baseEnd_5905915 < baseStart_5905915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905939 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 2, 3, 2]
def baseStart_5905939 : Nat := 118140960795 + 5905939 * 2 ^ 59
def prefixEnd_5905939 : Nat := 4983230072969 + 3 ^ 40 * 5905939 * 2
def baseEnd_5905939 : Nat := 3032585423134073720201587

theorem tailTrace_5905939 : CollatzResearch.WordTrace tailWord_5905939 prefixEnd_5905939 3032585423134073720201587 := by
  unfold tailWord_5905939
  simp only [CollatzResearch.WordTrace]
  refine ⟨215407291750799131923256871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143604861167199421282171247 215407291750799131923256871)
  ·
    refine ⟨323110937626198697884885307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215407291750799131923256871 323110937626198697884885307)
    ·
      refine ⟨484666406439298046827327961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323110937626198697884885307 484666406439298046827327961)
      ·
        refine ⟨363499804829473535120495971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484666406439298046827327961 363499804829473535120495971)
        ·
          refine ⟨545249707244210302680743957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363499804829473535120495971 545249707244210302680743957)
          ·
            refine ⟨25558580027072357938159873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 545249707244210302680743957 25558580027072357938159873)
            ·
              refine ⟨19168935020304268453619905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25558580027072357938159873 19168935020304268453619905)
              ·
                refine ⟨14376701265228201340214929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19168935020304268453619905 14376701265228201340214929)
                ·
                  refine ⟨10782525948921151005161197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14376701265228201340214929 10782525948921151005161197)
                  ·
                    refine ⟨4043447230845431626935449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10782525948921151005161197 4043447230845431626935449)
                    ·
                      refine ⟨3032585423134073720201587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043447230845431626935449 3032585423134073720201587)
                      ·
                        rfl

theorem cell23_5905939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 3, 2].length) (baseStart_5905939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905939 prefixEnd_5905939 := by exact prefixLift 5905939
  have htrace : WordTrace (prefixWord ++ tailWord_5905939) baseStart_5905939 baseEnd_5905939 := by
    simpa [prefixWord, tailWord_5905939, baseEnd_5905939] using wordTrace_append hprefix tailTrace_5905939
  have hstable : (prefixWord ++ tailWord_5905939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905939).length < 2 ^ (prefixWord ++ tailWord_5905939).sum := by decide
  have hdescent : baseEnd_5905939 < baseStart_5905939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905989 : List Nat := [1, 3, 1, 1, 1, 4, 3, 3, 1, 2, 3]
def baseStart_5905989 : Nat := 118140960795 + 5905989 * 2 ^ 59
def prefixEnd_5905989 : Nat := 4983230072969 + 3 ^ 40 * 5905989 * 2
def baseEnd_5905989 : Nat := 3032611097166798524576357

theorem tailTrace_5905989 : CollatzResearch.WordTrace tailWord_5905989 prefixEnd_5905989 3032611097166798524576357 := by
  unfold tailWord_5905989
  simp only [CollatzResearch.WordTrace]
  refine ⟨215409115400617990462577021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143606076933745326975051347 215409115400617990462577021)
  ·
    refine ⟨80778418275231746423466383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215409115400617990462577021 80778418275231746423466383)
    ·
      refine ⟨121167627412847619635199575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80778418275231746423466383 121167627412847619635199575)
      ·
        refine ⟨181751441119271429452799363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121167627412847619635199575 181751441119271429452799363)
        ·
          refine ⟨272627161678907144179199045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181751441119271429452799363 272627161678907144179199045)
          ·
            refine ⟨51117592814795089533599821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 272627161678907144179199045 51117592814795089533599821)
            ·
              refine ⟨19169097305548158575099933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51117592814795089533599821 19169097305548158575099933)
              ·
                refine ⟨7188411489580559465662475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19169097305548158575099933 7188411489580559465662475)
                ·
                  refine ⟨10782617234370839198493713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7188411489580559465662475 10782617234370839198493713)
                  ·
                    refine ⟨8086962925778129398870285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10782617234370839198493713 8086962925778129398870285)
                    ·
                      refine ⟨3032611097166798524576357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8086962925778129398870285 3032611097166798524576357)
                      ·
                        rfl

theorem cell23_5905989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_5905989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905989 prefixEnd_5905989 := by exact prefixLift 5905989
  have htrace : WordTrace (prefixWord ++ tailWord_5905989) baseStart_5905989 baseEnd_5905989 := by
    simpa [prefixWord, tailWord_5905989, baseEnd_5905989] using wordTrace_append hprefix tailTrace_5905989
  have hstable : (prefixWord ++ tailWord_5905989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905989).length < 2 ^ (prefixWord ++ tailWord_5905989).sum := by decide
  have hdescent : baseEnd_5905989 < baseStart_5905989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905995 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 6]
def baseStart_5905995 : Nat := 118140960795 + 5905995 * 2 ^ 59
def prefixEnd_5905995 : Nat := 4983230072969 + 3 ^ 40 * 5905995 * 2
def baseEnd_5905995 : Nat := 3032614178050725501101329

theorem tailTrace_5905995 : CollatzResearch.WordTrace tailWord_5905995 prefixEnd_5905995 3032614178050725501101329 := by
  unfold tailWord_5905995
  simp only [CollatzResearch.WordTrace]
  refine ⟨215409334238596253487295439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143606222825730835658196959 215409334238596253487295439)
  ·
    refine ⟨323114001357894380230943159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215409334238596253487295439 323114001357894380230943159)
    ·
      refine ⟨484671002036841570346414739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323114001357894380230943159 484671002036841570346414739)
      ·
        refine ⟨727006503055262355519622109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484671002036841570346414739 727006503055262355519622109)
        ·
          refine ⟨272627438645723383319858291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 727006503055262355519622109 272627438645723383319858291)
          ·
            refine ⟨408941157968585074979787437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272627438645723383319858291 408941157968585074979787437)
            ·
              refine ⟨153352934238219403117420289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 408941157968585074979787437 153352934238219403117420289)
              ·
                refine ⟨115014700678664552338065217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153352934238219403117420289 115014700678664552338065217)
                ·
                  refine ⟨86261025508998414253548913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115014700678664552338065217 86261025508998414253548913)
                  ·
                    refine ⟨64695769131748810690161685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86261025508998414253548913 64695769131748810690161685)
                    ·
                      refine ⟨3032614178050725501101329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64695769131748810690161685 3032614178050725501101329)
                      ·
                        rfl

theorem cell23_5905995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 6].length) (baseStart_5905995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905995 prefixEnd_5905995 := by exact prefixLift 5905995
  have htrace : WordTrace (prefixWord ++ tailWord_5905995) baseStart_5905995 baseEnd_5905995 := by
    simpa [prefixWord, tailWord_5905995, baseEnd_5905995] using wordTrace_append hprefix tailTrace_5905995
  have hstable : (prefixWord ++ tailWord_5905995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905995).length < 2 ^ (prefixWord ++ tailWord_5905995).sum := by decide
  have hdescent : baseEnd_5905995 < baseStart_5905995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5905996 : List Nat := [2, 2, 1, 3, 1, 5, 1, 2, 2, 4]
def baseStart_5905996 : Nat := 118140960795 + 5905996 * 2 ^ 59
def prefixEnd_5905996 : Nat := 4983230072969 + 3 ^ 40 * 5905996 * 2
def baseEnd_5905996 : Nat := 1010871563843793332396275

theorem tailTrace_5905996 : CollatzResearch.WordTrace tailWord_5905996 prefixEnd_5905996 1010871563843793332396275 := by
  unfold tailWord_5905996
  simp only [CollatzResearch.WordTrace]
  refine ⟨107704685355796315329040921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143606247141061753772054561 107704685355796315329040921)
  ·
    refine ⟨80778514016847236496780691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107704685355796315329040921 80778514016847236496780691)
    ·
      refine ⟨121167771025270854745171037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80778514016847236496780691 121167771025270854745171037)
      ·
        refine ⟨45437914134476570529439139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121167771025270854745171037 45437914134476570529439139)
        ·
          refine ⟨68156871201714855794158709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45437914134476570529439139 68156871201714855794158709)
          ·
            refine ⟨6389706675160767730702379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68156871201714855794158709 6389706675160767730702379)
            ·
              refine ⟨9584560012741151596053569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389706675160767730702379 9584560012741151596053569)
              ·
                refine ⟨7188420009555863697040177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9584560012741151596053569 7188420009555863697040177)
                ·
                  refine ⟨5391315007166897772780133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7188420009555863697040177 5391315007166897772780133)
                  ·
                    refine ⟨1010871563843793332396275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5391315007166897772780133 1010871563843793332396275)
                    ·
                      rfl

theorem cell23_5905996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_5905996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5905996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5905996 prefixEnd_5905996 := by exact prefixLift 5905996
  have htrace : WordTrace (prefixWord ++ tailWord_5905996) baseStart_5905996 baseEnd_5905996 := by
    simpa [prefixWord, tailWord_5905996, baseEnd_5905996] using wordTrace_append hprefix tailTrace_5905996
  have hstable : (prefixWord ++ tailWord_5905996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5905996).length < 2 ^ (prefixWord ++ tailWord_5905996).sum := by decide
  have hdescent : baseEnd_5905996 < baseStart_5905996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5905996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906013 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 1, 6]
def baseStart_5906013 : Nat := 118140960795 + 5906013 * 2 ^ 59
def prefixEnd_5906013 : Nat := 4983230072969 + 3 ^ 40 * 5906013 * 2
def baseEnd_5906013 : Nat := 1010874473567502143558749

theorem tailTrace_5906013 : CollatzResearch.WordTrace tailWord_5906013 prefixEnd_5906013 1010874473567502143558749 := by
  unfold tailWord_5906013
  simp only [CollatzResearch.WordTrace]
  refine ⟨215409990752531042561450693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143606660501687361707633795 215409990752531042561450693)
  ·
    refine ⟨40389373266099570480272005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215409990752531042561450693 40389373266099570480272005)
    ·
      refine ⟨7573007487393669465051001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40389373266099570480272005 7573007487393669465051001)
      ·
        refine ⟨5679755615545252098788251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7573007487393669465051001 5679755615545252098788251)
        ·
          refine ⟨8519633423317878148182377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5679755615545252098788251 8519633423317878148182377)
          ·
            refine ⟨6389725067488408611136783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8519633423317878148182377 6389725067488408611136783)
            ·
              refine ⟨9584587601232612916705175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389725067488408611136783 9584587601232612916705175)
              ·
                refine ⟨14376881401848919375057763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9584587601232612916705175 14376881401848919375057763)
                ·
                  refine ⟨21565322102773379062586645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14376881401848919375057763 21565322102773379062586645)
                  ·
                    refine ⟨1010874473567502143558749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21565322102773379062586645 1010874473567502143558749)
                    ·
                      rfl

theorem cell23_5906013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_5906013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906013 prefixEnd_5906013 := by exact prefixLift 5906013
  have htrace : WordTrace (prefixWord ++ tailWord_5906013) baseStart_5906013 baseEnd_5906013 := by
    simpa [prefixWord, tailWord_5906013, baseEnd_5906013] using wordTrace_append hprefix tailTrace_5906013
  have hstable : (prefixWord ++ tailWord_5906013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906013).length < 2 ^ (prefixWord ++ tailWord_5906013).sum := by decide
  have hdescent : baseEnd_5906013 < baseStart_5906013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906019 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 3]
def baseStart_5906019 : Nat := 118140960795 + 5906019 * 2 ^ 59
def prefixEnd_5906019 : Nat := 4983230072969 + 3 ^ 40 * 5906019 * 2
def baseEnd_5906019 : Nat := 3032626501586433407201219

theorem tailTrace_5906019 : CollatzResearch.WordTrace tailWord_5906019 prefixEnd_5906019 3032626501586433407201219 := by
  unfold tailWord_5906019
  simp only [CollatzResearch.WordTrace]
  refine ⟨215410209590509305586169111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143606806393672870390779407 215410209590509305586169111)
  ·
    refine ⟨323115314385763958379253667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215410209590509305586169111 323115314385763958379253667)
    ·
      refine ⟨484672971578645937568880501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323115314385763958379253667 484672971578645937568880501)
      ·
        refine ⟨45438091085498056647082547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 484672971578645937568880501 45438091085498056647082547)
        ·
          refine ⟨68157136628247084970623821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45438091085498056647082547 68157136628247084970623821)
          ·
            refine ⟨25558926235592656863983933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68157136628247084970623821 25558926235592656863983933)
            ·
              refine ⟨9584597338347246323993975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25558926235592656863983933 9584597338347246323993975)
              ·
                refine ⟨14376896007520869485990963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9584597338347246323993975 14376896007520869485990963)
                ·
                  refine ⟨21565344011281304228986445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14376896007520869485990963 21565344011281304228986445)
                  ·
                    refine ⟨8087004004230489085869917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21565344011281304228986445 8087004004230489085869917)
                    ·
                      refine ⟨3032626501586433407201219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8087004004230489085869917 3032626501586433407201219)
                      ·
                        rfl

theorem cell23_5906019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_5906019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906019 prefixEnd_5906019 := by exact prefixLift 5906019
  have htrace : WordTrace (prefixWord ++ tailWord_5906019) baseStart_5906019 baseEnd_5906019 := by
    simpa [prefixWord, tailWord_5906019, baseEnd_5906019] using wordTrace_append hprefix tailTrace_5906019
  have hstable : (prefixWord ++ tailWord_5906019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906019).length < 2 ^ (prefixWord ++ tailWord_5906019).sum := by decide
  have hdescent : baseEnd_5906019 < baseStart_5906019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906032 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 5]
def baseStart_5906032 : Nat := 118140960795 + 5906032 * 2 ^ 59
def prefixEnd_5906032 : Nat := 4983230072969 + 3 ^ 40 * 5906032 * 2
def baseEnd_5906032 : Nat := 3032633176834941856338659

theorem tailTrace_5906032 : CollatzResearch.WordTrace tailWord_5906032 prefixEnd_5906032 3032633176834941856338659 := by
  unfold tailWord_5906032
  simp only [CollatzResearch.WordTrace]
  refine ⟨107705341869731104403196175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143607122492974805870928233 107705341869731104403196175)
  ·
    refine ⟨161558012804596656604794263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107705341869731104403196175 161558012804596656604794263)
    ·
      refine ⟨242337019206894984907191395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161558012804596656604794263 242337019206894984907191395)
      ·
        refine ⟨363505528810342477360787093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242337019206894984907191395 363505528810342477360787093)
        ·
          refine ⟨17039321662984803626286895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 363505528810342477360787093 17039321662984803626286895)
          ·
            refine ⟨25558982494477205439430343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17039321662984803626286895 25558982494477205439430343)
            ·
              refine ⟨38338473741715808159145515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25558982494477205439430343 38338473741715808159145515)
              ·
                refine ⟨57507710612573712238718273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38338473741715808159145515 57507710612573712238718273)
                ·
                  refine ⟨43130782959430284179038705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57507710612573712238718273 43130782959430284179038705)
                  ·
                    refine ⟨32348087219572713134279029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43130782959430284179038705 32348087219572713134279029)
                    ·
                      refine ⟨3032633176834941856338659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32348087219572713134279029 3032633176834941856338659)
                      ·
                        rfl

theorem cell23_5906032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_5906032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906032 prefixEnd_5906032 := by exact prefixLift 5906032
  have htrace : WordTrace (prefixWord ++ tailWord_5906032) baseStart_5906032 baseEnd_5906032 := by
    simpa [prefixWord, tailWord_5906032, baseEnd_5906032] using wordTrace_append hprefix tailTrace_5906032
  have hstable : (prefixWord ++ tailWord_5906032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906032).length < 2 ^ (prefixWord ++ tailWord_5906032).sum := by decide
  have hdescent : baseEnd_5906032 < baseStart_5906032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906037 : List Nat := [1, 3, 4, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_5906037 : Nat := 118140960795 + 5906037 * 2 ^ 59
def prefixEnd_5906037 : Nat := 4983230072969 + 3 ^ 40 * 5906037 * 2
def baseEnd_5906037 : Nat := 3032635744238214336776137

theorem tailTrace_5906037 : CollatzResearch.WordTrace tailWord_5906037 prefixEnd_5906037 3032635744238214336776137 := by
  unfold tailWord_5906037
  simp only [CollatzResearch.WordTrace]
  refine ⟨215410866104444094660324365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143607244069629396440216243 215410866104444094660324365)
  ·
    refine ⟨80779074789166535497621637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215410866104444094660324365 80779074789166535497621637)
    ·
      refine ⟨15146076522968725405804057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80779074789166535497621637 15146076522968725405804057)
      ·
        refine ⟨11359557392226544054353043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15146076522968725405804057 11359557392226544054353043)
        ·
          refine ⟨17039336088339816081529565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11359557392226544054353043 17039336088339816081529565)
          ·
            refine ⟨6389751033127431030573587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17039336088339816081529565 6389751033127431030573587)
            ·
              refine ⟨9584626549691146545860381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389751033127431030573587 9584626549691146545860381)
              ·
                refine ⟨3594234956134179954697643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9584626549691146545860381 3594234956134179954697643)
                ·
                  refine ⟨5391352434201269932046465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3594234956134179954697643 5391352434201269932046465)
                  ·
                    refine ⟨4043514325650952449034849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5391352434201269932046465 4043514325650952449034849)
                    ·
                      refine ⟨3032635744238214336776137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043514325650952449034849 3032635744238214336776137)
                      ·
                        rfl

theorem cell23_5906037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_5906037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906037 prefixEnd_5906037 := by exact prefixLift 5906037
  have htrace : WordTrace (prefixWord ++ tailWord_5906037) baseStart_5906037 baseEnd_5906037 := by
    simpa [prefixWord, tailWord_5906037, baseEnd_5906037] using wordTrace_append hprefix tailTrace_5906037
  have hstable : (prefixWord ++ tailWord_5906037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906037).length < 2 ^ (prefixWord ++ tailWord_5906037).sum := by decide
  have hdescent : baseEnd_5906037 < baseStart_5906037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906099 : List Nat := [1, 1, 1, 2, 3, 3, 2, 5, 5]
def baseStart_5906099 : Nat := 118140960795 + 5906099 * 2 ^ 59
def prefixEnd_5906099 : Nat := 4983230072969 + 3 ^ 40 * 5906099 * 2
def baseEnd_5906099 : Nat := 336963064448754788244539

theorem tailTrace_5906099 : CollatzResearch.WordTrace tailWord_5906099 prefixEnd_5906099 336963064448754788244539 := by
  unfold tailWord_5906099
  simp only [CollatzResearch.WordTrace]
  refine ⟨215413127430219479249081351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143608751620146319499387567 215413127430219479249081351)
  ·
    refine ⟨323119691145329218873622027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215413127430219479249081351 323119691145329218873622027)
    ·
      refine ⟨484679536717993828310433041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323119691145329218873622027 484679536717993828310433041)
      ·
        refine ⟨363509652538495371232824781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484679536717993828310433041 363509652538495371232824781)
        ·
          refine ⟨136316119701935764212309293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363509652538495371232824781 136316119701935764212309293)
          ·
            refine ⟨51118544888225911579615985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136316119701935764212309293 51118544888225911579615985)
            ·
              refine ⟨38338908666169433684711989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51118544888225911579615985 38338908666169433684711989)
              ·
                refine ⟨3594272687453384407941749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38338908666169433684711989 3594272687453384407941749)
                ·
                  refine ⟨336963064448754788244539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3594272687453384407941749 336963064448754788244539)
                  ·
                    rfl

theorem cell23_5906099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 5].length) (baseStart_5906099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906099 prefixEnd_5906099 := by exact prefixLift 5906099
  have htrace : WordTrace (prefixWord ++ tailWord_5906099) baseStart_5906099 baseEnd_5906099 := by
    simpa [prefixWord, tailWord_5906099, baseEnd_5906099] using wordTrace_append hprefix tailTrace_5906099
  have hstable : (prefixWord ++ tailWord_5906099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906099).length < 2 ^ (prefixWord ++ tailWord_5906099).sum := by decide
  have hdescent : baseEnd_5906099 < baseStart_5906099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906109 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 2, 3, 3]
def baseStart_5906109 : Nat := 118140960795 + 5906109 * 2 ^ 59
def prefixEnd_5906109 : Nat := 4983230072969 + 3 ^ 40 * 5906109 * 2
def baseEnd_5906109 : Nat := 3032672714845338055075805

theorem tailTrace_5906109 : CollatzResearch.WordTrace tailWord_5906109 prefixEnd_5906109 3032672714845338055075805 := by
  unfold tailWord_5906109
  simp only [CollatzResearch.WordTrace]
  refine ⟨215413492160183250956945381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143608994773455500637963587 215413492160183250956945381)
  ·
    refine ⟨40390029780034359554427259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215413492160183250956945381 40390029780034359554427259)
    ·
      refine ⟨60585044670051539331640889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40390029780034359554427259 60585044670051539331640889)
      ·
        refine ⟨45438783502538654498730667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60585044670051539331640889 45438783502538654498730667)
        ·
          refine ⟨68158175253807981748096001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45438783502538654498730667 68158175253807981748096001)
          ·
            refine ⟨51118631440355986311072001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68158175253807981748096001 51118631440355986311072001)
            ·
              refine ⟨38338973580266989733304001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51118631440355986311072001 38338973580266989733304001)
              ·
                refine ⟨28754230185200242299978001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38338973580266989733304001 28754230185200242299978001)
                ·
                  refine ⟨21565672638900181724983501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28754230185200242299978001 21565672638900181724983501)
                  ·
                    refine ⟨8087127239587568146868813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21565672638900181724983501 8087127239587568146868813)
                    ·
                      refine ⟨3032672714845338055075805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8087127239587568146868813 3032672714845338055075805)
                      ·
                        rfl

theorem cell23_5906109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_5906109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906109 prefixEnd_5906109 := by exact prefixLift 5906109
  have htrace : WordTrace (prefixWord ++ tailWord_5906109) baseStart_5906109 baseEnd_5906109 := by
    simpa [prefixWord, tailWord_5906109, baseEnd_5906109] using wordTrace_append hprefix tailTrace_5906109
  have hstable : (prefixWord ++ tailWord_5906109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906109).length < 2 ^ (prefixWord ++ tailWord_5906109).sum := by decide
  have hdescent : baseEnd_5906109 < baseStart_5906109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906110 : List Nat := [4, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2]
def baseStart_5906110 : Nat := 118140960795 + 5906110 * 2 ^ 59
def prefixEnd_5906110 : Nat := 4983230072969 + 3 ^ 40 * 5906110 * 2
def baseEnd_5906110 : Nat := 3032673228325992551163301

theorem tailTrace_5906110 : CollatzResearch.WordTrace tailWord_5906110 prefixEnd_5906110 3032673228325992551163301 := by
  unfold tailWord_5906110
  simp only [CollatzResearch.WordTrace]
  refine ⟨26926691079147453515966473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143609019088786418751821189 26926691079147453515966473)
  ·
    refine ⟨20195018309360590136974855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26926691079147453515966473 20195018309360590136974855)
    ·
      refine ⟨30292527464040885205462283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20195018309360590136974855 30292527464040885205462283)
      ·
        refine ⟨45438791196061327808193425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30292527464040885205462283 45438791196061327808193425)
        ·
          refine ⟨34079093397045995856145069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45438791196061327808193425 34079093397045995856145069)
          ·
            refine ⟨12779660023892248446054401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34079093397045995856145069 12779660023892248446054401)
            ·
              refine ⟨9584745017919186334540801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12779660023892248446054401 9584745017919186334540801)
              ·
                refine ⟨7188558763439389750905601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9584745017919186334540801 7188558763439389750905601)
                ·
                  refine ⟨5391419072579542313179201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7188558763439389750905601 5391419072579542313179201)
                  ·
                    refine ⟨4043564304434656734884401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5391419072579542313179201 4043564304434656734884401)
                    ·
                      refine ⟨3032673228325992551163301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043564304434656734884401 3032673228325992551163301)
                      ·
                        rfl

theorem cell23_5906110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_5906110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906110 prefixEnd_5906110 := by exact prefixLift 5906110
  have htrace : WordTrace (prefixWord ++ tailWord_5906110) baseStart_5906110 baseEnd_5906110 := by
    simpa [prefixWord, tailWord_5906110, baseEnd_5906110] using wordTrace_append hprefix tailTrace_5906110
  have hstable : (prefixWord ++ tailWord_5906110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906110).length < 2 ^ (prefixWord ++ tailWord_5906110).sum := by decide
  have hdescent : baseEnd_5906110 < baseStart_5906110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906116 : List Nat := [2, 3, 3, 1, 1, 1, 3, 4, 5]
def baseStart_5906116 : Nat := 118140960795 + 5906116 * 2 ^ 59
def prefixEnd_5906116 : Nat := 4983230072969 + 3 ^ 40 * 5906116 * 2
def baseEnd_5906116 : Nat := 336964034356657725298697

theorem tailTrace_5906116 : CollatzResearch.WordTrace tailWord_5906116 prefixEnd_5906116 336964034356657725298697 := by
  unfold tailWord_5906116
  simp only [CollatzResearch.WordTrace]
  refine ⟨107706873735578945576225101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143609164980771927434966801 107706873735578945576225101)
  ·
    refine ⟨40390077650842104591084413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107706873735578945576225101 40390077650842104591084413)
    ·
      refine ⟨15146279119065789221656655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40390077650842104591084413 15146279119065789221656655)
      ·
        refine ⟨22719418678598683832484983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15146279119065789221656655 22719418678598683832484983)
        ·
          refine ⟨34079128017898025748727475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22719418678598683832484983 34079128017898025748727475)
          ·
            refine ⟨51118692026847038623091213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34079128017898025748727475 51118692026847038623091213)
            ·
              refine ⟨19169509510067639483659205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51118692026847038623091213 19169509510067639483659205)
              ·
                refine ⟨3594283033137682403186101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19169509510067639483659205 3594283033137682403186101)
                ·
                  refine ⟨336964034356657725298697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3594283033137682403186101 336964034356657725298697)
                  ·
                    rfl

theorem cell23_5906116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_5906116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906116 prefixEnd_5906116 := by exact prefixLift 5906116
  have htrace : WordTrace (prefixWord ++ tailWord_5906116) baseStart_5906116 baseEnd_5906116 := by
    simpa [prefixWord, tailWord_5906116, baseEnd_5906116] using wordTrace_append hprefix tailTrace_5906116
  have hstable : (prefixWord ++ tailWord_5906116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906116).length < 2 ^ (prefixWord ++ tailWord_5906116).sum := by decide
  have hdescent : baseEnd_5906116 < baseStart_5906116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906119 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 1, 7, 2]
def baseStart_5906119 : Nat := 118140960795 + 5906119 * 2 ^ 59
def prefixEnd_5906119 : Nat := 4983230072969 + 3 ^ 40 * 5906119 * 2
def baseEnd_5906119 : Nat := 3032677849651883015950759

theorem tailTrace_5906119 : CollatzResearch.WordTrace tailWord_5906119 prefixEnd_5906119 3032677849651883015950759 := by
  unfold tailWord_5906119
  simp only [CollatzResearch.WordTrace]
  refine ⟨215413856890147022664809411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143609237926764681776539607 215413856890147022664809411)
  ·
    refine ⟨323120785335220533997214117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215413856890147022664809411 323120785335220533997214117)
    ·
      refine ⟨60585147250353850124477647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323120785335220533997214117 60585147250353850124477647)
      ·
        refine ⟨90877720875530775186716471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60585147250353850124477647 90877720875530775186716471)
        ·
          refine ⟨136316581313296162780074707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90877720875530775186716471 136316581313296162780074707)
          ·
            refine ⟨204474871969944244170112061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136316581313296162780074707 204474871969944244170112061)
            ·
              refine ⟨76678076988729091563792023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204474871969944244170112061 76678076988729091563792023)
              ·
                refine ⟨115017115483093637345688035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76678076988729091563792023 115017115483093637345688035)
                ·
                  refine ⟨172525673224640456018532053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115017115483093637345688035 172525673224640456018532053)
                  ·
                    refine ⟨4043570466202510687934345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 172525673224640456018532053 4043570466202510687934345)
                    ·
                      refine ⟨3032677849651883015950759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043570466202510687934345 3032677849651883015950759)
                      ·
                        rfl

theorem cell23_5906119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_5906119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906119 prefixEnd_5906119 := by exact prefixLift 5906119
  have htrace : WordTrace (prefixWord ++ tailWord_5906119) baseStart_5906119 baseEnd_5906119 := by
    simpa [prefixWord, tailWord_5906119, baseEnd_5906119] using wordTrace_append hprefix tailTrace_5906119
  have hstable : (prefixWord ++ tailWord_5906119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906119).length < 2 ^ (prefixWord ++ tailWord_5906119).sum := by decide
  have hdescent : baseEnd_5906119 < baseStart_5906119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906149 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 1, 3, 4]
def baseStart_5906149 : Nat := 118140960795 + 5906149 * 2 ^ 59
def prefixEnd_5906149 : Nat := 4983230072969 + 3 ^ 40 * 5906149 * 2
def baseEnd_5906149 : Nat := 3032693254071517898575621

theorem tailTrace_5906149 : CollatzResearch.WordTrace tailWord_5906149 prefixEnd_5906149 3032693254071517898575621 := by
  unfold tailWord_5906149
  simp only [CollatzResearch.WordTrace]
  refine ⟨215414951080038337788401501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143609967386692225192267667 215414951080038337788401501)
  ·
    refine ⟨80780606655014376670650563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215414951080038337788401501 80780606655014376670650563)
    ·
      refine ⟨121170909982521565005975845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80780606655014376670650563 121170909982521565005975845)
      ·
        refine ⟨22719545621722793438620471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121170909982521565005975845 22719545621722793438620471)
        ·
          refine ⟨34079318432584190157930707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22719545621722793438620471 34079318432584190157930707)
          ·
            refine ⟨51118977648876285236896061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34079318432584190157930707 51118977648876285236896061)
            ·
              refine ⟨19169616618328606963836023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51118977648876285236896061 19169616618328606963836023)
              ·
                refine ⟨28754424927492910445754035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19169616618328606963836023 28754424927492910445754035)
                ·
                  refine ⟨43131637391239365668631053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28754424927492910445754035 43131637391239365668631053)
                  ·
                    refine ⟨16174364021714762125736645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43131637391239365668631053 16174364021714762125736645)
                    ·
                      refine ⟨3032693254071517898575621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16174364021714762125736645 3032693254071517898575621)
                      ·
                        rfl

theorem cell23_5906149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_5906149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906149 prefixEnd_5906149 := by exact prefixLift 5906149
  have htrace : WordTrace (prefixWord ++ tailWord_5906149) baseStart_5906149 baseEnd_5906149 := by
    simpa [prefixWord, tailWord_5906149, baseEnd_5906149] using wordTrace_append hprefix tailTrace_5906149
  have hstable : (prefixWord ++ tailWord_5906149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906149).length < 2 ^ (prefixWord ++ tailWord_5906149).sum := by decide
  have hdescent : baseEnd_5906149 < baseStart_5906149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906159 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 5, 4]
def baseStart_5906159 : Nat := 118140960795 + 5906159 * 2 ^ 59
def prefixEnd_5906159 : Nat := 4983230072969 + 3 ^ 40 * 5906159 * 2
def baseEnd_5906159 : Nat := 1010899462959354286483525

theorem tailTrace_5906159 : CollatzResearch.WordTrace tailWord_5906159 prefixEnd_5906159 1010899462959354286483525 := by
  unfold tailWord_5906159
  simp only [CollatzResearch.WordTrace]
  refine ⟨215415315810002109496265531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143610210540001406330843687 215415315810002109496265531)
  ·
    refine ⟨323122973715003164244398297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215415315810002109496265531 323122973715003164244398297)
    ·
      refine ⟨242342230286252373183298723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323122973715003164244398297 242342230286252373183298723)
      ·
        refine ⟨363513345429378559774948085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242342230286252373183298723 363513345429378559774948085)
        ·
          refine ⟨34079376134004239978901383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 363513345429378559774948085 34079376134004239978901383)
          ·
            refine ⟨51119064201006359968352075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34079376134004239978901383 51119064201006359968352075)
            ·
              refine ⟨76678596301509539952528113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51119064201006359968352075 76678596301509539952528113)
              ·
                refine ⟨57508947226132154964396085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76678596301509539952528113 57508947226132154964396085)
                ·
                  refine ⟨5391463802449889527912133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57508947226132154964396085 5391463802449889527912133)
                  ·
                    refine ⟨1010899462959354286483525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5391463802449889527912133 1010899462959354286483525)
                    ·
                      rfl

theorem cell23_5906159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 4].length) (baseStart_5906159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906159 prefixEnd_5906159 := by exact prefixLift 5906159
  have htrace : WordTrace (prefixWord ++ tailWord_5906159) baseStart_5906159 baseEnd_5906159 := by
    simpa [prefixWord, tailWord_5906159, baseEnd_5906159] using wordTrace_append hprefix tailTrace_5906159
  have hstable : (prefixWord ++ tailWord_5906159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906159).length < 2 ^ (prefixWord ++ tailWord_5906159).sum := by decide
  have hdescent : baseEnd_5906159 < baseStart_5906159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906249 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 1, 6]
def baseStart_5906249 : Nat := 118140960795 + 5906249 * 2 ^ 59
def prefixEnd_5906249 : Nat := 4983230072969 + 3 ^ 40 * 5906249 * 2
def baseEnd_5906249 : Nat := 1010914867378989169108387

theorem tailTrace_5906249 : CollatzResearch.WordTrace tailWord_5906249 prefixEnd_5906249 1010914867378989169108387 := by
  unfold tailWord_5906249
  simp only [CollatzResearch.WordTrace]
  refine ⟨215418598379676054867041801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143612398919784036578027867 215418598379676054867041801)
  ·
    refine ⟨161563948784757041150281351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215418598379676054867041801 161563948784757041150281351)
    ·
      refine ⟨242345923177135561725422027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161563948784757041150281351 242345923177135561725422027)
      ·
        refine ⟨363518884765703342588133041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242345923177135561725422027 363518884765703342588133041)
        ·
          refine ⟨272639163574277506941099781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363518884765703342588133041 272639163574277506941099781)
          ·
            refine ⟨51119843170177032551456209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 272639163574277506941099781 51119843170177032551456209)
            ·
              refine ⟨38339882377632774413592157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51119843170177032551456209 38339882377632774413592157)
              ·
                refine ⟨14377455891612290405097059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38339882377632774413592157 14377455891612290405097059)
                ·
                  refine ⟨21566183837418435607645589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14377455891612290405097059 21566183837418435607645589)
                  ·
                    refine ⟨1010914867378989169108387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21566183837418435607645589 1010914867378989169108387)
                    ·
                      rfl

theorem cell23_5906249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 6].length) (baseStart_5906249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906249 prefixEnd_5906249 := by exact prefixLift 5906249
  have htrace : WordTrace (prefixWord ++ tailWord_5906249) baseStart_5906249 baseEnd_5906249 := by
    simpa [prefixWord, tailWord_5906249, baseEnd_5906249] using wordTrace_append hprefix tailTrace_5906249
  have hstable : (prefixWord ++ tailWord_5906249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906249).length < 2 ^ (prefixWord ++ tailWord_5906249).sum := by decide
  have hdescent : baseEnd_5906249 < baseStart_5906249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906253 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_5906253 : Nat := 118140960795 + 5906253 * 2 ^ 59
def prefixEnd_5906253 : Nat := 4983230072969 + 3 ^ 40 * 5906253 * 2
def baseEnd_5906253 : Nat := 1010915552019861830558381

theorem tailTrace_5906253 : CollatzResearch.WordTrace tailWord_5906253 prefixEnd_5906253 1010915552019861830558381 := by
  unfold tailWord_5906253
  simp only [CollatzResearch.WordTrace]
  refine ⟨215418744271661563550187413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143612496181107709033458275 215418744271661563550187413)
  ·
    refine ⟨10097753637734135791415035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 215418744271661563550187413 10097753637734135791415035)
    ·
      refine ⟨15146630456601203687122553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10097753637734135791415035 15146630456601203687122553)
      ·
        refine ⟨11359972842450902765341915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15146630456601203687122553 11359972842450902765341915)
        ·
          refine ⟨17039959263676354148012873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11359972842450902765341915 17039959263676354148012873)
          ·
            refine ⟨12779969447757265611009655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17039959263676354148012873 12779969447757265611009655)
            ·
              refine ⟨19169954171635898416514483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12779969447757265611009655 19169954171635898416514483)
              ·
                refine ⟨28754931257453847624771725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19169954171635898416514483 28754931257453847624771725)
                ·
                  refine ⟨10783099221545192859289397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28754931257453847624771725 10783099221545192859289397)
                  ·
                    refine ⟨1010915552019861830558381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10783099221545192859289397 1010915552019861830558381)
                    ·
                      rfl

theorem cell23_5906253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_5906253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906253 prefixEnd_5906253 := by exact prefixLift 5906253
  have htrace : WordTrace (prefixWord ++ tailWord_5906253) baseStart_5906253 baseEnd_5906253 := by
    simpa [prefixWord, tailWord_5906253, baseEnd_5906253] using wordTrace_append hprefix tailTrace_5906253
  have hstable : (prefixWord ++ tailWord_5906253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906253).length < 2 ^ (prefixWord ++ tailWord_5906253).sum := by decide
  have hdescent : baseEnd_5906253 < baseStart_5906253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906260 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 2, 3, 2]
def baseStart_5906260 : Nat := 118140960795 + 5906260 * 2 ^ 59
def prefixEnd_5906260 : Nat := 4983230072969 + 3 ^ 40 * 5906260 * 2
def baseEnd_5906260 : Nat := 3032750250424166964287611

theorem tailTrace_5906260 : CollatzResearch.WordTrace tailWord_5906260 prefixEnd_5906260 3032750250424166964287611 := by
  unfold tailWord_5906260
  simp only [CollatzResearch.WordTrace]
  refine ⟨107709499791318101872846117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143612666388424135830461489 107709499791318101872846117)
  ·
    refine ⟨20195531210872144101158647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107709499791318101872846117 20195531210872144101158647)
    ·
      refine ⟨30293296816308216151737971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20195531210872144101158647 30293296816308216151737971)
      ·
        refine ⟨45439945224462324227606957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30293296816308216151737971 45439945224462324227606957)
        ·
          refine ⟨17039979459173371585352609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45439945224462324227606957 17039979459173371585352609)
          ·
            refine ⟨12779984594380028689014457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17039979459173371585352609 12779984594380028689014457)
            ·
              refine ⟨9584988445785021516760843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12779984594380028689014457 9584988445785021516760843)
              ·
                refine ⟨14377482668677532275141265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9584988445785021516760843 14377482668677532275141265)
                ·
                  refine ⟨10783112001508149206355949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14377482668677532275141265 10783112001508149206355949)
                  ·
                    refine ⟨4043667000565555952383481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10783112001508149206355949 4043667000565555952383481)
                    ·
                      refine ⟨3032750250424166964287611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043667000565555952383481 3032750250424166964287611)
                      ·
                        rfl

theorem cell23_5906260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_5906260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906260 prefixEnd_5906260 := by exact prefixLift 5906260
  have htrace : WordTrace (prefixWord ++ tailWord_5906260) baseStart_5906260 baseEnd_5906260 := by
    simpa [prefixWord, tailWord_5906260, baseEnd_5906260] using wordTrace_append hprefix tailTrace_5906260
  have hstable : (prefixWord ++ tailWord_5906260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906260).length < 2 ^ (prefixWord ++ tailWord_5906260).sum := by decide
  have hdescent : baseEnd_5906260 < baseStart_5906260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906273 : List Nat := [1, 2, 3, 1, 1, 1, 7, 1, 1, 1, 4]
def baseStart_5906273 : Nat := 118140960795 + 5906273 * 2 ^ 59
def prefixEnd_5906273 : Nat := 4983230072969 + 3 ^ 40 * 5906273 * 2
def baseEnd_5906273 : Nat := 3032756925672675413425051

theorem tailTrace_5906273 : CollatzResearch.WordTrace tailWord_5906273 prefixEnd_5906273 3032756925672675413425051 := by
  unfold tailWord_5906273
  simp only [CollatzResearch.WordTrace]
  refine ⟨215419473731589106965915473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143612982487726071310610315 215419473731589106965915473)
  ·
    refine ⟨161564605298691830224436605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215419473731589106965915473 161564605298691830224436605)
    ·
      refine ⟨60586726987009436334163727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161564605298691830224436605 60586726987009436334163727)
      ·
        refine ⟨90880090480514154501245591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60586726987009436334163727 90880090480514154501245591)
        ·
          refine ⟨136320135720771231751868387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90880090480514154501245591 136320135720771231751868387)
          ·
            refine ⟨204480203581156847627802581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136320135720771231751868387 204480203581156847627802581)
            ·
              refine ⟨4792504771433363616276623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 204480203581156847627802581 4792504771433363616276623)
              ·
                refine ⟨7188757157150045424414935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4792504771433363616276623 7188757157150045424414935)
                ·
                  refine ⟨10783135735725068136622403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7188757157150045424414935 10783135735725068136622403)
                  ·
                    refine ⟨16174703603587602204933605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10783135735725068136622403 16174703603587602204933605)
                    ·
                      refine ⟨3032756925672675413425051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16174703603587602204933605 3032756925672675413425051)
                      ·
                        rfl

theorem cell23_5906273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_5906273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906273 prefixEnd_5906273 := by exact prefixLift 5906273
  have htrace : WordTrace (prefixWord ++ tailWord_5906273) baseStart_5906273 baseEnd_5906273 := by
    simpa [prefixWord, tailWord_5906273, baseEnd_5906273] using wordTrace_append hprefix tailTrace_5906273
  have hstable : (prefixWord ++ tailWord_5906273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906273).length < 2 ^ (prefixWord ++ tailWord_5906273).sum := by decide
  have hdescent : baseEnd_5906273 < baseStart_5906273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906309 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 2, 7]
def baseStart_5906309 : Nat := 118140960795 + 5906309 * 2 ^ 59
def prefixEnd_5906309 : Nat := 4983230072969 + 3 ^ 40 * 5906309 * 2
def baseEnd_5906309 : Nat := 1010925136992079090858295

theorem tailTrace_5906309 : CollatzResearch.WordTrace tailWord_5906309 prefixEnd_5906309 1010925136992079090858295 := by
  unfold tailWord_5906309
  simp only [CollatzResearch.WordTrace]
  refine ⟨215420786759458685114225981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143613857839639123409483987 215420786759458685114225981)
  ·
    refine ⟨80782795034797006917834743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215420786759458685114225981 80782795034797006917834743)
    ·
      refine ⟨121174192552195510376752115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80782795034797006917834743 121174192552195510376752115)
      ·
        refine ⟨181761288828293265565128173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121174192552195510376752115 181761288828293265565128173)
        ·
          refine ⟨68160483310609974586923065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181761288828293265565128173 68160483310609974586923065)
          ·
            refine ⟨51120362482957480940192299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68160483310609974586923065 51120362482957480940192299)
            ·
              refine ⟨76680543724436221410288449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51120362482957480940192299 76680543724436221410288449)
              ·
                refine ⟨57510407793327166057716337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76680543724436221410288449 57510407793327166057716337)
                ·
                  refine ⟨43132805844995374543287253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57510407793327166057716337 43132805844995374543287253)
                  ·
                    refine ⟨1010925136992079090858295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43132805844995374543287253 1010925136992079090858295)
                    ·
                      rfl

theorem cell23_5906309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_5906309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906309 prefixEnd_5906309 := by exact prefixLift 5906309
  have htrace : WordTrace (prefixWord ++ tailWord_5906309) baseStart_5906309 baseEnd_5906309 := by
    simpa [prefixWord, tailWord_5906309, baseEnd_5906309] using wordTrace_append hprefix tailTrace_5906309
  have hstable : (prefixWord ++ tailWord_5906309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906309).length < 2 ^ (prefixWord ++ tailWord_5906309).sum := by decide
  have hdescent : baseEnd_5906309 < baseStart_5906309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906324 : List Nat := [2, 4, 2, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_5906324 : Nat := 118140960795 + 5906324 * 2 ^ 59
def prefixEnd_5906324 : Nat := 4983230072969 + 3 ^ 40 * 5906324 * 2
def baseEnd_5906324 : Nat := 3032783113186054713887317

theorem tailTrace_5906324 : CollatzResearch.WordTrace tailWord_5906324 prefixEnd_5906324 3032783113186054713887317 := by
  unfold tailWord_5906324
  simp only [CollatzResearch.WordTrace]
  refine ⟨107710666927202171338011013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143614222569602895117348017 107710666927202171338011013)
  ·
    refine ⟨20195750048850407125877065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107710666927202171338011013 20195750048850407125877065)
    ·
      refine ⟨15146812536637805344407799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20195750048850407125877065 15146812536637805344407799)
      ·
        refine ⟨22720218804956708016611699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15146812536637805344407799 22720218804956708016611699)
        ·
          refine ⟨34080328207435062024917549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22720218804956708016611699 34080328207435062024917549)
          ·
            refine ⟨12780123077788148259344081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34080328207435062024917549 12780123077788148259344081)
            ·
              refine ⟨9585092308341111194508061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12780123077788148259344081 9585092308341111194508061)
              ·
                refine ⟨3594409615627916697940523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9585092308341111194508061 3594409615627916697940523)
                ·
                  refine ⟨5391614423441875046910785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3594409615627916697940523 5391614423441875046910785)
                  ·
                    refine ⟨4043710817581406285183089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5391614423441875046910785 4043710817581406285183089)
                    ·
                      refine ⟨3032783113186054713887317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043710817581406285183089 3032783113186054713887317)
                      ·
                        rfl

theorem cell23_5906324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_5906324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906324 prefixEnd_5906324 := by exact prefixLift 5906324
  have htrace : WordTrace (prefixWord ++ tailWord_5906324) baseStart_5906324 baseEnd_5906324 := by
    simpa [prefixWord, tailWord_5906324, baseEnd_5906324] using wordTrace_append hprefix tailTrace_5906324
  have hstable : (prefixWord ++ tailWord_5906324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906324).length < 2 ^ (prefixWord ++ tailWord_5906324).sum := by decide
  have hdescent : baseEnd_5906324 < baseStart_5906324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906334 : List Nat := [4, 3, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_5906334 : Nat := 118140960795 + 5906334 * 2 ^ 59
def prefixEnd_5906334 : Nat := 4983230072969 + 3 ^ 40 * 5906334 * 2
def baseEnd_5906334 : Nat := 1010929415997533224920757

theorem tailTrace_5906334 : CollatzResearch.WordTrace tailWord_5906334 prefixEnd_5906334 1010929415997533224920757 := by
  unfold tailWord_5906334
  simp only [CollatzResearch.WordTrace]
  refine ⟨26927712323046014297985757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143614465722912076255924037 26927712323046014297985757)
  ·
    refine ⟨10097892121142255361744659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26927712323046014297985757 10097892121142255361744659)
    ·
      refine ⟨15146838181713383042616989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10097892121142255361744659 15146838181713383042616989)
      ·
        refine ⟨5680064318142518640981371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15146838181713383042616989 5680064318142518640981371)
        ·
          refine ⟨8520096477213777961472057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5680064318142518640981371 8520096477213777961472057)
          ·
            refine ⟨6390072357910333471104043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8520096477213777961472057 6390072357910333471104043)
            ·
              refine ⟨9585108536865500206656065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6390072357910333471104043 9585108536865500206656065)
              ·
                refine ⟨7188831402649125154992049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9585108536865500206656065 7188831402649125154992049)
                ·
                  refine ⟨5391623551986843866244037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7188831402649125154992049 5391623551986843866244037)
                  ·
                    refine ⟨1010929415997533224920757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5391623551986843866244037 1010929415997533224920757)
                    ·
                      rfl

theorem cell23_5906334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_5906334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906334 prefixEnd_5906334 := by exact prefixLift 5906334
  have htrace : WordTrace (prefixWord ++ tailWord_5906334) baseStart_5906334 baseEnd_5906334 := by
    simpa [prefixWord, tailWord_5906334, baseEnd_5906334] using wordTrace_append hprefix tailTrace_5906334
  have hstable : (prefixWord ++ tailWord_5906334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906334).length < 2 ^ (prefixWord ++ tailWord_5906334).sum := by decide
  have hdescent : baseEnd_5906334 < baseStart_5906334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906340 : List Nat := [2, 3, 1, 2, 1, 3, 3, 2, 2, 1, 3]
def baseStart_5906340 : Nat := 118140960795 + 5906340 * 2 ^ 59
def prefixEnd_5906340 : Nat := 4983230072969 + 3 ^ 40 * 5906340 * 2
def baseEnd_5906340 : Nat := 3032791328876526651287243

theorem tailTrace_5906340 : CollatzResearch.WordTrace tailWord_5906340 prefixEnd_5906340 3032791328876526651287243 := by
  unfold tailWord_5906340
  simp only [CollatzResearch.WordTrace]
  refine ⟨107710958711173188704302237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143614611614897584939069649 107710958711173188704302237)
  ·
    refine ⟨40391609516689945764113339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107710958711173188704302237 40391609516689945764113339)
    ·
      refine ⟨60587414275034918646170009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40391609516689945764113339 60587414275034918646170009)
      ·
        refine ⟨45440560706276188984627507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60587414275034918646170009 45440560706276188984627507)
        ·
          refine ⟨68160841059414283476941261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45440560706276188984627507 68160841059414283476941261)
          ·
            refine ⟨25560315397280356303852973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68160841059414283476941261 25560315397280356303852973)
            ·
              refine ⟨9585118273980133613944865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25560315397280356303852973 9585118273980133613944865)
              ·
                refine ⟨7188838705485100210458649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9585118273980133613944865 7188838705485100210458649)
                ·
                  refine ⟨5391629029113825157843987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7188838705485100210458649 5391629029113825157843987)
                  ·
                    refine ⟨8087443543670737736765981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5391629029113825157843987 8087443543670737736765981)
                    ·
                      refine ⟨3032791328876526651287243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8087443543670737736765981 3032791328876526651287243)
                      ·
                        rfl

theorem cell23_5906340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_5906340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906340 prefixEnd_5906340 := by exact prefixLift 5906340
  have htrace : WordTrace (prefixWord ++ tailWord_5906340) baseStart_5906340 baseEnd_5906340 := by
    simpa [prefixWord, tailWord_5906340, baseEnd_5906340] using wordTrace_append hprefix tailTrace_5906340
  have hstable : (prefixWord ++ tailWord_5906340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906340).length < 2 ^ (prefixWord ++ tailWord_5906340).sum := by decide
  have hdescent : baseEnd_5906340 < baseStart_5906340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906357 : List Nat := [1, 3, 3, 2, 1, 3, 3, 1, 2, 1, 3]
def baseStart_5906357 : Nat := 118140960795 + 5906357 * 2 ^ 59
def prefixEnd_5906357 : Nat := 4983230072969 + 3 ^ 40 * 5906357 * 2
def baseEnd_5906357 : Nat := 3032800058047653084774665

theorem tailTrace_5906357 : CollatzResearch.WordTrace tailWord_5906357 prefixEnd_5906357 3032800058047653084774665 := by
  unfold tailWord_5906357
  simp only [CollatzResearch.WordTrace]
  refine ⟨215422537463284789311973325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143615024975523192874648883 215422537463284789311973325)
  ·
    refine ⟨80783451548731795991989997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215422537463284789311973325 80783451548731795991989997)
    ·
      refine ⟨30293794330774423496996249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80783451548731795991989997 30293794330774423496996249)
      ·
        refine ⟨22720345748080817622747187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30293794330774423496996249 22720345748080817622747187)
        ·
          refine ⟨34080518622121226434120781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22720345748080817622747187 34080518622121226434120781)
          ·
            refine ⟨12780194483295459912795293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34080518622121226434120781 12780194483295459912795293)
            ·
              refine ⟨4792572931235797467298235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12780194483295459912795293 4792572931235797467298235)
              ·
                refine ⟨7188859396853696200947353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4792572931235797467298235 7188859396853696200947353)
                ·
                  refine ⟨5391644547640272150710515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7188859396853696200947353 5391644547640272150710515)
                  ·
                    refine ⟨8087466821460408226065773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5391644547640272150710515 8087466821460408226065773)
                    ·
                      refine ⟨3032800058047653084774665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8087466821460408226065773 3032800058047653084774665)
                      ·
                        rfl

theorem cell23_5906357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_5906357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906357 prefixEnd_5906357 := by exact prefixLift 5906357
  have htrace : WordTrace (prefixWord ++ tailWord_5906357) baseStart_5906357 baseEnd_5906357 := by
    simpa [prefixWord, tailWord_5906357, baseEnd_5906357] using wordTrace_append hprefix tailTrace_5906357
  have hstable : (prefixWord ++ tailWord_5906357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906357).length < 2 ^ (prefixWord ++ tailWord_5906357).sum := by decide
  have hdescent : baseEnd_5906357 < baseStart_5906357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906363 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 6, 2, 2]
def baseStart_5906363 : Nat := 118140960795 + 5906363 * 2 ^ 59
def prefixEnd_5906363 : Nat := 4983230072969 + 3 ^ 40 * 5906363 * 2
def baseEnd_5906363 : Nat := 3032803138931580061299637

theorem tailTrace_5906363 : CollatzResearch.WordTrace tailWord_5906363 prefixEnd_5906363 3032803138931580061299637 := by
  unfold tailWord_5906363
  simp only [CollatzResearch.WordTrace]
  refine ⟨215422756301263052336691743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143615170867508701557794495 215422756301263052336691743)
  ·
    refine ⟨323134134451894578505037615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215422756301263052336691743 323134134451894578505037615)
    ·
      refine ⟨484701201677841867757556423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323134134451894578505037615 484701201677841867757556423)
      ·
        refine ⟨727051802516762801636334635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484701201677841867757556423 727051802516762801636334635)
        ·
          refine ⟨1090577703775144202454501953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727051802516762801636334635 1090577703775144202454501953)
          ·
            refine ⟨817933277831358151840876465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1090577703775144202454501953 817933277831358151840876465)
            ·
              refine ⟨613449958373518613880657349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817933277831358151840876465 613449958373518613880657349)
              ·
                refine ⟨115021867195034740102623253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 613449958373518613880657349 115021867195034740102623253)
                ·
                  refine ⟨5391650024767253442310465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115021867195034740102623253 5391650024767253442310465)
                  ·
                    refine ⟨4043737518575440081732849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5391650024767253442310465 4043737518575440081732849)
                    ·
                      refine ⟨3032803138931580061299637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043737518575440081732849 3032803138931580061299637)
                      ·
                        rfl

theorem cell23_5906363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 2, 2].length) (baseStart_5906363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906363 prefixEnd_5906363 := by exact prefixLift 5906363
  have htrace : WordTrace (prefixWord ++ tailWord_5906363) baseStart_5906363 baseEnd_5906363 := by
    simpa [prefixWord, tailWord_5906363, baseEnd_5906363] using wordTrace_append hprefix tailTrace_5906363
  have hstable : (prefixWord ++ tailWord_5906363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906363).length < 2 ^ (prefixWord ++ tailWord_5906363).sum := by decide
  have hdescent : baseEnd_5906363 < baseStart_5906363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906380 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 4, 2, 2]
def baseStart_5906380 : Nat := 118140960795 + 5906380 * 2 ^ 59
def prefixEnd_5906380 : Nat := 4983230072969 + 3 ^ 40 * 5906380 * 2
def baseEnd_5906380 : Nat := 3032811868102706494787059

theorem tailTrace_5906380 : CollatzResearch.WordTrace tailWord_5906380 prefixEnd_5906380 3032811868102706494787059 := by
  unfold tailWord_5906380
  simp only [CollatzResearch.WordTrace]
  refine ⟨107711688171100732120030297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143615584228134309493373729 107711688171100732120030297)
  ·
    refine ⟨80783766128325549090022723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107711688171100732120030297 80783766128325549090022723)
    ·
      refine ⟨121175649192488323635034085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80783766128325549090022723 121175649192488323635034085)
      ·
        refine ⟨22720434223591560681568891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121175649192488323635034085 22720434223591560681568891)
        ·
          refine ⟨34080651335387341022353337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22720434223591560681568891 34080651335387341022353337)
          ·
            refine ⟨25560488501540505766765003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34080651335387341022353337 25560488501540505766765003)
            ·
              refine ⟨38340732752310758650147505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25560488501540505766765003 38340732752310758650147505)
              ·
                refine ⟨28755549564233068987610629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38340732752310758650147505 28755549564233068987610629)
                ·
                  refine ⟨5391665543293700435176993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28755549564233068987610629 5391665543293700435176993)
                  ·
                    refine ⟨4043749157470275326382745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5391665543293700435176993 4043749157470275326382745)
                    ·
                      refine ⟨3032811868102706494787059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043749157470275326382745 3032811868102706494787059)
                      ·
                        rfl

theorem cell23_5906380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_5906380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906380 prefixEnd_5906380 := by exact prefixLift 5906380
  have htrace : WordTrace (prefixWord ++ tailWord_5906380) baseStart_5906380 baseEnd_5906380 := by
    simpa [prefixWord, tailWord_5906380, baseEnd_5906380] using wordTrace_append hprefix tailTrace_5906380
  have hstable : (prefixWord ++ tailWord_5906380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906380).length < 2 ^ (prefixWord ++ tailWord_5906380).sum := by decide
  have hdescent : baseEnd_5906380 < baseStart_5906380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906403 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 7]
def baseStart_5906403 : Nat := 118140960795 + 5906403 * 2 ^ 59
def prefixEnd_5906403 : Nat := 4983230072969 + 3 ^ 40 * 5906403 * 2
def baseEnd_5906403 : Nat := 336980408684195544977717

theorem tailTrace_5906403 : CollatzResearch.WordTrace tailWord_5906403 prefixEnd_5906403 336980408684195544977717 := by
  unfold tailWord_5906403
  simp only [CollatzResearch.WordTrace]
  refine ⟨215424215221118139168147863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143616143480745426112098575 215424215221118139168147863)
  ·
    refine ⟨323136322831677208752221795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215424215221118139168147863 323136322831677208752221795)
    ·
      refine ⟨484704484247515813128332693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323136322831677208752221795 484704484247515813128332693)
      ·
        refine ⟨22720522699102303740390595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 484704484247515813128332693 22720522699102303740390595)
        ·
          refine ⟨34080784048653455610585893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22720522699102303740390595 34080784048653455610585893)
          ·
            refine ⟨6390147009122522926984855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34080784048653455610585893 6390147009122522926984855)
            ·
              refine ⟨9585220513683784390477283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6390147009122522926984855 9585220513683784390477283)
              ·
                refine ⟨14377830770525676585715925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9585220513683784390477283 14377830770525676585715925)
                ·
                  refine ⟨336980408684195544977717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14377830770525676585715925 336980408684195544977717)
                  ·
                    rfl

theorem cell23_5906403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 7].length) (baseStart_5906403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906403 prefixEnd_5906403 := by exact prefixLift 5906403
  have htrace : WordTrace (prefixWord ++ tailWord_5906403) baseStart_5906403 baseEnd_5906403 := by
    simpa [prefixWord, tailWord_5906403, baseEnd_5906403] using wordTrace_append hprefix tailTrace_5906403
  have hstable : (prefixWord ++ tailWord_5906403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906403).length < 2 ^ (prefixWord ++ tailWord_5906403).sum := by decide
  have hdescent : baseEnd_5906403 < baseStart_5906403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906414 : List Nat := [4, 1, 2, 1, 3, 1, 4, 1, 2, 2, 2]
def baseStart_5906414 : Nat := 118140960795 + 5906414 * 2 ^ 59
def prefixEnd_5906414 : Nat := 4983230072969 + 3 ^ 40 * 5906414 * 2
def baseEnd_5906414 : Nat := 3032829326444959361761903

theorem tailTrace_5906414 : CollatzResearch.WordTrace tailWord_5906414 prefixEnd_5906414 3032829326444959361761903 := by
  unfold tailWord_5906414
  simp only [CollatzResearch.WordTrace]
  refine ⟨26928077053009786005849787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143616410949385525364532197 26928077053009786005849787)
  ·
    refine ⟨40392115579514679008774681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26928077053009786005849787 40392115579514679008774681)
    ·
      refine ⟨30294086684636009256581011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40392115579514679008774681 30294086684636009256581011)
      ·
        refine ⟨45441130026954013884871517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30294086684636009256581011 45441130026954013884871517)
        ·
          refine ⟨17040423760107755206826819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45441130026954013884871517 17040423760107755206826819)
          ·
            refine ⟨25560635640161632810240229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17040423760107755206826819 25560635640161632810240229)
            ·
              refine ⟨4792619182530306151920043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25560635640161632810240229 4792619182530306151920043)
              ·
                refine ⟨7188928773795459227880065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4792619182530306151920043 7188928773795459227880065)
                ·
                  refine ⟨5391696580346594420910049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7188928773795459227880065 5391696580346594420910049)
                  ·
                    refine ⟨4043772435259945815682537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5391696580346594420910049 4043772435259945815682537)
                    ·
                      refine ⟨3032829326444959361761903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043772435259945815682537 3032829326444959361761903)
                      ·
                        rfl

theorem cell23_5906414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_5906414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906414 prefixEnd_5906414 := by exact prefixLift 5906414
  have htrace : WordTrace (prefixWord ++ tailWord_5906414) baseStart_5906414 baseEnd_5906414 := by
    simpa [prefixWord, tailWord_5906414, baseEnd_5906414] using wordTrace_append hprefix tailTrace_5906414
  have hstable : (prefixWord ++ tailWord_5906414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906414).length < 2 ^ (prefixWord ++ tailWord_5906414).sum := by decide
  have hdescent : baseEnd_5906414 < baseStart_5906414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906433 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 2, 5]
def baseStart_5906433 : Nat := 118140960795 + 5906433 * 2 ^ 59
def prefixEnd_5906433 : Nat := 4983230072969 + 3 ^ 40 * 5906433 * 2
def baseEnd_5906433 : Nat := 1010946360859131595808105

theorem tailTrace_5906433 : CollatzResearch.WordTrace tailWord_5906433 prefixEnd_5906433 1010946360859131595808105 := by
  unfold tailWord_5906433
  simp only [CollatzResearch.WordTrace]
  refine ⟨215425309411009454291739953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143616872940672969527826635 215425309411009454291739953)
  ·
    refine ⟨161568982058257090718804965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215425309411009454291739953 161568982058257090718804965)
    ·
      refine ⟨30294184135923204509775931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161568982058257090718804965 30294184135923204509775931)
      ·
        refine ⟨45441276203884806764663897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30294184135923204509775931 45441276203884806764663897)
        ·
          refine ⟨34080957152913605073497923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45441276203884806764663897 34080957152913605073497923)
          ·
            refine ⟨51121435729370407610246885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34080957152913605073497923 51121435729370407610246885)
            ·
              refine ⟨9585269199256951426921291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51121435729370407610246885 9585269199256951426921291)
              ·
                refine ⟨14377903798885427140381937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9585269199256951426921291 14377903798885427140381937)
                ·
                  refine ⟨10783427849164070355286453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14377903798885427140381937 10783427849164070355286453)
                  ·
                    refine ⟨1010946360859131595808105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10783427849164070355286453 1010946360859131595808105)
                    ·
                      rfl

theorem cell23_5906433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_5906433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906433 prefixEnd_5906433 := by exact prefixLift 5906433
  have htrace : WordTrace (prefixWord ++ tailWord_5906433) baseStart_5906433 baseEnd_5906433 := by
    simpa [prefixWord, tailWord_5906433, baseEnd_5906433] using wordTrace_append hprefix tailTrace_5906433
  have hstable : (prefixWord ++ tailWord_5906433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906433).length < 2 ^ (prefixWord ++ tailWord_5906433).sum := by decide
  have hdescent : baseEnd_5906433 < baseStart_5906433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906456 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_5906456 : Nat := 118140960795 + 5906456 * 2 ^ 59
def prefixEnd_5906456 : Nat := 4983230072969 + 3 ^ 40 * 5906456 * 2
def baseEnd_5906456 : Nat := 3032850892632448197436709

theorem tailTrace_5906456 : CollatzResearch.WordTrace tailWord_5906456 prefixEnd_5906456 3032850892632448197436709 := by
  unfold tailWord_5906456
  simp only [CollatzResearch.WordTrace]
  refine ⟨107713074144963064609913611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143617432193284086146551481 107713074144963064609913611)
  ·
    refine ⟨161569611217444596914870417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107713074144963064609913611 161569611217444596914870417)
    ·
      refine ⟨121177208413083447686152813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161569611217444596914870417 121177208413083447686152813)
      ·
        refine ⟨45441453154906292882307305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121177208413083447686152813 45441453154906292882307305)
        ·
          refine ⟨34081089866179719661730479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45441453154906292882307305 34081089866179719661730479)
          ·
            refine ⟨51121634799269579492595719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34081089866179719661730479 51121634799269579492595719)
            ·
              refine ⟨76682452198904369238893579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51121634799269579492595719 76682452198904369238893579)
              ·
                refine ⟨115023678298356553858340369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76682452198904369238893579 115023678298356553858340369)
                ·
                  refine ⟨86267758723767415393755277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115023678298356553858340369 86267758723767415393755277)
                  ·
                    refine ⟨32350409521412780772658229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86267758723767415393755277 32350409521412780772658229)
                    ·
                      refine ⟨3032850892632448197436709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32350409521412780772658229 3032850892632448197436709)
                      ·
                        rfl

theorem cell23_5906456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_5906456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906456 prefixEnd_5906456 := by exact prefixLift 5906456
  have htrace : WordTrace (prefixWord ++ tailWord_5906456) baseStart_5906456 baseEnd_5906456 := by
    simpa [prefixWord, tailWord_5906456, baseEnd_5906456] using wordTrace_append hprefix tailTrace_5906456
  have hstable : (prefixWord ++ tailWord_5906456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906456).length < 2 ^ (prefixWord ++ tailWord_5906456).sum := by decide
  have hdescent : baseEnd_5906456 < baseStart_5906456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906463 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 3, 4]
def baseStart_5906463 : Nat := 118140960795 + 5906463 * 2 ^ 59
def prefixEnd_5906463 : Nat := 4983230072969 + 3 ^ 40 * 5906463 * 2
def baseEnd_5906463 : Nat := 1010951495665676556683059

theorem tailTrace_5906463 : CollatzResearch.WordTrace tailWord_5906463 prefixEnd_5906463 1010951495665676556683059 := by
  unfold tailWord_5906463
  simp only [CollatzResearch.WordTrace]
  refine ⟨215426403600900769415332043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143617602400600512943554695 215426403600900769415332043)
  ·
    refine ⟨323139605401351154122998065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215426403600900769415332043 323139605401351154122998065)
    ·
      refine ⟨242354704051013365592248549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323139605401351154122998065 242354704051013365592248549)
      ·
        refine ⟨45441507009565006048546603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242354704051013365592248549 45441507009565006048546603)
        ·
          refine ⟨68162260514347509072819905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45441507009565006048546603 68162260514347509072819905)
          ·
            refine ⟨51121695385760631804614929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68162260514347509072819905 51121695385760631804614929)
            ·
              refine ⟨38341271539320473853461197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51121695385760631804614929 38341271539320473853461197)
              ·
                refine ⟨14377976827245177695047949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38341271539320473853461197 14377976827245177695047949)
                ·
                  refine ⟨5391741310216941635642981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14377976827245177695047949 5391741310216941635642981)
                  ·
                    refine ⟨1010951495665676556683059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5391741310216941635642981 1010951495665676556683059)
                    ·
                      rfl

theorem cell23_5906463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 4].length) (baseStart_5906463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906463 prefixEnd_5906463 := by exact prefixLift 5906463
  have htrace : WordTrace (prefixWord ++ tailWord_5906463) baseStart_5906463 baseEnd_5906463 := by
    simpa [prefixWord, tailWord_5906463, baseEnd_5906463] using wordTrace_append hprefix tailTrace_5906463
  have hstable : (prefixWord ++ tailWord_5906463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906463).length < 2 ^ (prefixWord ++ tailWord_5906463).sum := by decide
  have hdescent : baseEnd_5906463 < baseStart_5906463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906484 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_5906484 : Nat := 118140960795 + 5906484 * 2 ^ 59
def prefixEnd_5906484 : Nat := 4983230072969 + 3 ^ 40 * 5906484 * 2
def baseEnd_5906484 : Nat := 1010955090030258029295527

theorem tailTrace_5906484 : CollatzResearch.WordTrace tailWord_5906484 prefixEnd_5906484 1010955090030258029295527 := by
  unfold tailWord_5906484
  simp only [CollatzResearch.WordTrace]
  refine ⟨107713584766912345000923253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143618113022549793334564337 107713584766912345000923253)
  ·
    refine ⟨10098148571898032343836555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107713584766912345000923253 10098148571898032343836555)
    ·
      refine ⟨15147222857847048515754833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10098148571898032343836555 15147222857847048515754833)
      ·
        refine ⟨11360417143385286386816125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15147222857847048515754833 11360417143385286386816125)
        ·
          refine ⟨4260156428769482395056047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11360417143385286386816125 4260156428769482395056047)
          ·
            refine ⟨6390234643154223592584071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4260156428769482395056047 6390234643154223592584071)
            ·
              refine ⟨9585351964731335388876107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6390234643154223592584071 9585351964731335388876107)
              ·
                refine ⟨14378027947097003083314161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9585351964731335388876107 14378027947097003083314161)
                ·
                  refine ⟨10783520960322752312485621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14378027947097003083314161 10783520960322752312485621)
                  ·
                    refine ⟨1010955090030258029295527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10783520960322752312485621 1010955090030258029295527)
                    ·
                      rfl

theorem cell23_5906484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_5906484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906484 prefixEnd_5906484 := by exact prefixLift 5906484
  have htrace : WordTrace (prefixWord ++ tailWord_5906484) baseStart_5906484 baseEnd_5906484 := by
    simpa [prefixWord, tailWord_5906484, baseEnd_5906484] using wordTrace_append hprefix tailTrace_5906484
  have hstable : (prefixWord ++ tailWord_5906484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906484).length < 2 ^ (prefixWord ++ tailWord_5906484).sum := by decide
  have hdescent : baseEnd_5906484 < baseStart_5906484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906497 : List Nat := [1, 2, 5, 1, 2, 1, 1, 5, 1, 4]
def baseStart_5906497 : Nat := 118140960795 + 5906497 * 2 ^ 59
def prefixEnd_5906497 : Nat := 4983230072969 + 3 ^ 40 * 5906497 * 2
def baseEnd_5906497 : Nat := 1010957315113094179008007

theorem tailTrace_5906497 : CollatzResearch.WordTrace tailWord_5906497 prefixEnd_5906497 1010957315113094179008007 := by
  unfold tailWord_5906497
  simp only [CollatzResearch.WordTrace]
  refine ⟨215427643682777593222069745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143618429121851728814713163 215427643682777593222069745)
  ·
    refine ⟨161570732762083194916552309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215427643682777593222069745 161570732762083194916552309)
    ·
      refine ⟨15147256196445299523426779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161570732762083194916552309 15147256196445299523426779)
      ·
        refine ⟨22720884294667949285140169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15147256196445299523426779 22720884294667949285140169)
        ·
          refine ⟨17040663221000961963855127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22720884294667949285140169 17040663221000961963855127)
          ·
            refine ⟨25560994831501442945782691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17040663221000961963855127 25560994831501442945782691)
            ·
              refine ⟨38341492247252164418674037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25560994831501442945782691 38341492247252164418674037)
              ·
                refine ⟨3594514898179890414250691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38341492247252164418674037 3594514898179890414250691)
                ·
                  refine ⟨5391772347269835621376037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3594514898179890414250691 5391772347269835621376037)
                  ·
                    refine ⟨1010957315113094179008007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5391772347269835621376037 1010957315113094179008007)
                    ·
                      rfl

theorem cell23_5906497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_5906497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906497 prefixEnd_5906497 := by exact prefixLift 5906497
  have htrace : WordTrace (prefixWord ++ tailWord_5906497) baseStart_5906497 baseEnd_5906497 := by
    simpa [prefixWord, tailWord_5906497, baseEnd_5906497] using wordTrace_append hprefix tailTrace_5906497
  have hstable : (prefixWord ++ tailWord_5906497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906497).length < 2 ^ (prefixWord ++ tailWord_5906497).sum := by decide
  have hdescent : baseEnd_5906497 < baseStart_5906497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906510 : List Nat := [4, 1, 1, 1, 1, 6, 1, 2, 6]
def baseStart_5906510 : Nat := 118140960795 + 5906510 * 2 ^ 59
def prefixEnd_5906510 : Nat := 4983230072969 + 3 ^ 40 * 5906510 * 2
def baseEnd_5906510 : Nat := 336986513398643442906829

theorem tailTrace_5906510 : CollatzResearch.WordTrace tailWord_5906510 prefixEnd_5906510 336986513398643442906829 := by
  unfold tailWord_5906510
  simp only [CollatzResearch.WordTrace]
  refine ⟨26928514728966312055286623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143618745221153664294861989 26928514728966312055286623)
  ·
    refine ⟨40392772093449468082929935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26928514728966312055286623 40392772093449468082929935)
    ·
      refine ⟨60589158140174202124394903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40392772093449468082929935 60589158140174202124394903)
      ·
        refine ⟨90883737210261303186592355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60589158140174202124394903 90883737210261303186592355)
        ·
          refine ⟨136325605815391954779888533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90883737210261303186592355 136325605815391954779888533)
          ·
            refine ⟨6390262772596497880307275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 136325605815391954779888533 6390262772596497880307275)
            ·
              refine ⟨9585394158894746820460913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6390262772596497880307275 9585394158894746820460913)
              ·
                refine ⟨7189045619171060115345685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9585394158894746820460913 7189045619171060115345685)
                ·
                  refine ⟨336986513398643442906829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7189045619171060115345685 336986513398643442906829)
                  ·
                    rfl

theorem cell23_5906510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_5906510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906510 prefixEnd_5906510 := by exact prefixLift 5906510
  have htrace : WordTrace (prefixWord ++ tailWord_5906510) baseStart_5906510 baseEnd_5906510 := by
    simpa [prefixWord, tailWord_5906510, baseEnd_5906510] using wordTrace_append hprefix tailTrace_5906510
  have hstable : (prefixWord ++ tailWord_5906510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906510).length < 2 ^ (prefixWord ++ tailWord_5906510).sum := by decide
  have hdescent : baseEnd_5906510 < baseStart_5906510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906520 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 3, 1, 3]
def baseStart_5906520 : Nat := 118140960795 + 5906520 * 2 ^ 59
def prefixEnd_5906520 : Nat := 4983230072969 + 3 ^ 40 * 5906520 * 2
def baseEnd_5906520 : Nat := 3032883755394335947036415

theorem tailTrace_5906520 : CollatzResearch.WordTrace tailWord_5906520 prefixEnd_5906520 3032883755394335947036415 := by
  unfold tailWord_5906520
  simp only [CollatzResearch.WordTrace]
  refine ⟨107714241280847134075078507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143618988374462845433438009 107714241280847134075078507)
  ·
    refine ⟨161571361921270701112617761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107714241280847134075078507 161571361921270701112617761)
    ·
      refine ⟨121178521440953025834463321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161571361921270701112617761 121178521440953025834463321)
      ·
        refine ⟨90883891080714769375847491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121178521440953025834463321 90883891080714769375847491)
        ·
          refine ⟨136325836621072154063771237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90883891080714769375847491 136325836621072154063771237)
          ·
            refine ⟨25561094366451028886957107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136325836621072154063771237 25561094366451028886957107)
            ·
              refine ⟨38341641549676543330435661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25561094366451028886957107 38341641549676543330435661)
              ·
                refine ⟨14378115581128703748913373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38341641549676543330435661 14378115581128703748913373)
                ·
                  refine ⟨5391793342923263905842515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14378115581128703748913373 5391793342923263905842515)
                  ·
                    refine ⟨8087690014384895858763773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5391793342923263905842515 8087690014384895858763773)
                    ·
                      refine ⟨3032883755394335947036415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8087690014384895858763773 3032883755394335947036415)
                      ·
                        rfl

theorem cell23_5906520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_5906520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906520 prefixEnd_5906520 := by exact prefixLift 5906520
  have htrace : WordTrace (prefixWord ++ tailWord_5906520) baseStart_5906520 baseEnd_5906520 := by
    simpa [prefixWord, tailWord_5906520, baseEnd_5906520] using wordTrace_append hprefix tailTrace_5906520
  have hstable : (prefixWord ++ tailWord_5906520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906520).length < 2 ^ (prefixWord ++ tailWord_5906520).sum := by decide
  have hdescent : baseEnd_5906520 < baseStart_5906520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906540 : List Nat := [2, 2, 1, 1, 3, 4, 2, 2, 1, 5]
def baseStart_5906540 : Nat := 118140960795 + 5906540 * 2 ^ 59
def prefixEnd_5906540 : Nat := 4983230072969 + 3 ^ 40 * 5906540 * 2
def baseEnd_5906540 : Nat := 1010964675002475289595441

theorem tailTrace_5906540 : CollatzResearch.WordTrace tailWord_5906540 prefixEnd_5906540 1010964675002475289595441 := by
  unfold tailWord_5906540
  simp only [CollatzResearch.WordTrace]
  refine ⟨107714606010810905782942537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143619474681081207710590049 107714606010810905782942537)
  ·
    refine ⟨80785954508108179337206903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107714606010810905782942537 80785954508108179337206903)
    ·
      refine ⟨121178931762162269005810355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80785954508108179337206903 121178931762162269005810355)
      ·
        refine ⟨181768397643243403508715533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121178931762162269005810355 181768397643243403508715533)
        ·
          refine ⟨68163149116216276315768325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181768397643243403508715533 68163149116216276315768325)
          ·
            refine ⟨12780590459290551809206561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68163149116216276315768325 12780590459290551809206561)
            ·
              refine ⟨9585442844467913856904921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12780590459290551809206561 9585442844467913856904921)
              ·
                refine ⟨7189082133350935392678691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9585442844467913856904921 7189082133350935392678691)
                ·
                  refine ⟨10783623200026403089018037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7189082133350935392678691 10783623200026403089018037)
                  ·
                    refine ⟨1010964675002475289595441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10783623200026403089018037 1010964675002475289595441)
                    ·
                      rfl

theorem cell23_5906540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_5906540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906540 prefixEnd_5906540 := by exact prefixLift 5906540
  have htrace : WordTrace (prefixWord ++ tailWord_5906540) baseStart_5906540 baseEnd_5906540 := by
    simpa [prefixWord, tailWord_5906540, baseEnd_5906540] using wordTrace_append hprefix tailTrace_5906540
  have hstable : (prefixWord ++ tailWord_5906540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906540).length < 2 ^ (prefixWord ++ tailWord_5906540).sum := by decide
  have hdescent : baseEnd_5906540 < baseStart_5906540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906563 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 5]
def baseStart_5906563 : Nat := 118140960795 + 5906563 * 2 ^ 59
def prefixEnd_5906563 : Nat := 4983230072969 + 3 ^ 40 * 5906563 * 2
def baseEnd_5906563 : Nat := 3032905835062479278798717

theorem tailTrace_5906563 : CollatzResearch.WordTrace tailWord_5906563 prefixEnd_5906563 3032905835062479278798717 := by
  unfold tailWord_5906563
  simp only [CollatzResearch.WordTrace]
  refine ⟨215430050900538486493972343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143620033933692324329314895 215430050900538486493972343)
  ·
    refine ⟨323145076350807729740958515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215430050900538486493972343 323145076350807729740958515)
    ·
      refine ⟨484717614526211594611437773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323145076350807729740958515 484717614526211594611437773)
      ·
        refine ⟨181769105447329347979289165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 484717614526211594611437773 181769105447329347979289165)
        ·
          refine ⟨68163414542748505492233437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181769105447329347979289165 68163414542748505492233437)
          ·
            refine ⟨25561280453530689559587539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68163414542748505492233437 25561280453530689559587539)
            ·
              refine ⟨38341920680296034339381309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25561280453530689559587539 38341920680296034339381309)
              ·
                refine ⟨14378220255111012877267991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38341920680296034339381309 14378220255111012877267991)
                ·
                  refine ⟨21567330382666519315901987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14378220255111012877267991 21567330382666519315901987)
                  ·
                    refine ⟨32350995573999778973852981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21567330382666519315901987 32350995573999778973852981)
                    ·
                      refine ⟨3032905835062479278798717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32350995573999778973852981 3032905835062479278798717)
                      ·
                        rfl

theorem cell23_5906563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_5906563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906563 prefixEnd_5906563 := by exact prefixLift 5906563
  have htrace : WordTrace (prefixWord ++ tailWord_5906563) baseStart_5906563 baseEnd_5906563 := by
    simpa [prefixWord, tailWord_5906563, baseEnd_5906563] using wordTrace_append hprefix tailTrace_5906563
  have hstable : (prefixWord ++ tailWord_5906563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906563).length < 2 ^ (prefixWord ++ tailWord_5906563).sum := by decide
  have hdescent : baseEnd_5906563 < baseStart_5906563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906570 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 4, 4]
def baseStart_5906570 : Nat := 118140960795 + 5906570 * 2 ^ 59
def prefixEnd_5906570 : Nat := 4983230072969 + 3 ^ 40 * 5906570 * 2
def baseEnd_5906570 : Nat := 1010969809809020250470395

theorem tailTrace_5906570 : CollatzResearch.WordTrace tailWord_5906570 prefixEnd_5906570 1010969809809020250470395 := by
  unfold tailWord_5906570
  simp only [CollatzResearch.WordTrace]
  refine ⟨53857576552878281672369291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143620204141008751126318109 53857576552878281672369291)
  ·
    refine ⟨80786364829317422508553937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53857576552878281672369291 80786364829317422508553937)
    ·
      refine ⟨60589773621988066881415453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80786364829317422508553937 60589773621988066881415453)
      ·
        refine ⟨22721165108245525080530795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60589773621988066881415453 22721165108245525080530795)
        ·
          refine ⟨34081747662368287620796193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22721165108245525080530795 34081747662368287620796193)
          ·
            refine ⟨25561310746776215715597145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34081747662368287620796193 25561310746776215715597145)
            ·
              refine ⟨19170983060082161786697859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25561310746776215715597145 19170983060082161786697859)
              ·
                refine ⟨28756474590123242680046789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19170983060082161786697859 28756474590123242680046789)
                ·
                  refine ⟨5391838985648108002508773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28756474590123242680046789 5391838985648108002508773)
                  ·
                    refine ⟨1010969809809020250470395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5391838985648108002508773 1010969809809020250470395)
                    ·
                      rfl

theorem cell23_5906570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_5906570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906570 prefixEnd_5906570 := by exact prefixLift 5906570
  have htrace : WordTrace (prefixWord ++ tailWord_5906570) baseStart_5906570 baseEnd_5906570 := by
    simpa [prefixWord, tailWord_5906570, baseEnd_5906570] using wordTrace_append hprefix tailTrace_5906570
  have hstable : (prefixWord ++ tailWord_5906570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906570).length < 2 ^ (prefixWord ++ tailWord_5906570).sum := by decide
  have hdescent : baseEnd_5906570 < baseStart_5906570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906594 : List Nat := [3, 3, 1, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_5906594 : Nat := 118140960795 + 5906594 * 2 ^ 59
def prefixEnd_5906594 : Nat := 4983230072969 + 3 ^ 40 * 5906594 * 2
def baseEnd_5906594 : Nat := 3032921752962768657511075

theorem tailTrace_5906594 : CollatzResearch.WordTrace tailWord_5906594 prefixEnd_5906594 3032921752962768657511075 := by
  unfold tailWord_5906594
  simp only [CollatzResearch.WordTrace]
  refine ⟨53857795390856544697087709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143620787708950785858900557 53857795390856544697087709)
  ·
    refine ⟨20196673271571204261407891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53857795390856544697087709 20196673271571204261407891)
    ·
      refine ⟨30295009907356806392111837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20196673271571204261407891 30295009907356806392111837)
      ·
        refine ⟨11360628715258802397041939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30295009907356806392111837 11360628715258802397041939)
        ·
          refine ⟨17040943072888203595562909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11360628715258802397041939 17040943072888203595562909)
          ·
            refine ⟨6390353652333076348336091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17040943072888203595562909 6390353652333076348336091)
            ·
              refine ⟨9585530478499614522504137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6390353652333076348336091 9585530478499614522504137)
              ·
                refine ⟨7189147858874710891878103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9585530478499614522504137 7189147858874710891878103)
                ·
                  refine ⟨10783721788312066337817155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7189147858874710891878103 10783721788312066337817155)
                  ·
                    refine ⟨16175582682468099506725733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10783721788312066337817155 16175582682468099506725733)
                    ·
                      refine ⟨3032921752962768657511075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16175582682468099506725733 3032921752962768657511075)
                      ·
                        rfl

theorem cell23_5906594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_5906594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906594 prefixEnd_5906594 := by exact prefixLift 5906594
  have htrace : WordTrace (prefixWord ++ tailWord_5906594) baseStart_5906594 baseEnd_5906594 := by
    simpa [prefixWord, tailWord_5906594, baseEnd_5906594] using wordTrace_append hprefix tailTrace_5906594
  have hstable : (prefixWord ++ tailWord_5906594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906594).length < 2 ^ (prefixWord ++ tailWord_5906594).sum := by decide
  have hdescent : baseEnd_5906594 < baseStart_5906594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906610 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3]
def baseStart_5906610 : Nat := 118140960795 + 5906610 * 2 ^ 59
def prefixEnd_5906610 : Nat := 4983230072969 + 3 ^ 40 * 5906610 * 2
def baseEnd_5906610 : Nat := 3032929968653240594911001

theorem tailTrace_5906610 : CollatzResearch.WordTrace tailWord_5906610 prefixEnd_5906610 3032929968653240594911001 := by
  unfold tailWord_5906610
  simp only [CollatzResearch.WordTrace]
  refine ⟨53857941282842053380233321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143621176754245475680622189 53857941282842053380233321)
  ·
    refine ⟨40393455962131540035174991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53857941282842053380233321 40393455962131540035174991)
    ·
      refine ⟨60590183943197310052762487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40393455962131540035174991 60590183943197310052762487)
      ·
        refine ⟨90885275914795965079143731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60590183943197310052762487 90885275914795965079143731)
        ·
          refine ⟨136327913872193947618715597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90885275914795965079143731 136327913872193947618715597)
          ·
            refine ⟨51122967702072730357018349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136327913872193947618715597 51122967702072730357018349)
            ·
              refine ⟨19171112888277273883881881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51122967702072730357018349 19171112888277273883881881)
              ·
                refine ⟨14378334666207955412911411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19171112888277273883881881 14378334666207955412911411)
                ·
                  refine ⟨21567501999311933119367117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14378334666207955412911411 21567501999311933119367117)
                  ·
                    refine ⟨8087813249741974919762669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21567501999311933119367117 8087813249741974919762669)
                    ·
                      refine ⟨3032929968653240594911001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8087813249741974919762669 3032929968653240594911001)
                      ·
                        rfl

theorem cell23_5906610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_5906610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906610 prefixEnd_5906610 := by exact prefixLift 5906610
  have htrace : WordTrace (prefixWord ++ tailWord_5906610) baseStart_5906610 baseEnd_5906610 := by
    simpa [prefixWord, tailWord_5906610, baseEnd_5906610] using wordTrace_append hprefix tailTrace_5906610
  have hstable : (prefixWord ++ tailWord_5906610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906610).length < 2 ^ (prefixWord ++ tailWord_5906610).sum := by decide
  have hdescent : baseEnd_5906610 < baseStart_5906610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906628 : List Nat := [2, 3, 3, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_5906628 : Nat := 118140960795 + 5906628 * 2 ^ 59
def prefixEnd_5906628 : Nat := 4983230072969 + 3 ^ 40 * 5906628 * 2
def baseEnd_5906628 : Nat := 3032939211305021524485919

theorem tailTrace_5906628 : CollatzResearch.WordTrace tailWord_5906628 prefixEnd_5906628 3032939211305021524485919 := by
  unfold tailWord_5906628
  simp only [CollatzResearch.WordTrace]
  refine ⟨107716210822651501297544269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143621614430202001730059025 107716210822651501297544269)
  ·
    refine ⟨40393579058494312986579101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107716210822651501297544269 40393579058494312986579101)
    ·
      refine ⟨15147592146935367369967163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40393579058494312986579101 15147592146935367369967163)
      ·
        refine ⟨22721388220403051054950745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15147592146935367369967163 22721388220403051054950745)
        ·
          refine ⟨17041041165302288291213059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22721388220403051054950745 17041041165302288291213059)
          ·
            refine ⟨25561561747953432436819589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17041041165302288291213059 25561561747953432436819589)
            ·
              refine ⟨4792792827741268581903673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25561561747953432436819589 4792792827741268581903673)
              ·
                refine ⟨3594594620805951436427755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4792792827741268581903673 3594594620805951436427755)
                ·
                  refine ⟨5391891931208927154641633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3594594620805951436427755 5391891931208927154641633)
                  ·
                    refine ⟨4043918948406695365981225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5391891931208927154641633 4043918948406695365981225)
                    ·
                      refine ⟨3032939211305021524485919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043918948406695365981225 3032939211305021524485919)
                      ·
                        rfl

theorem cell23_5906628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_5906628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906628 prefixEnd_5906628 := by exact prefixLift 5906628
  have htrace : WordTrace (prefixWord ++ tailWord_5906628) baseStart_5906628 baseEnd_5906628 := by
    simpa [prefixWord, tailWord_5906628, baseEnd_5906628] using wordTrace_append hprefix tailTrace_5906628
  have hstable : (prefixWord ++ tailWord_5906628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906628).length < 2 ^ (prefixWord ++ tailWord_5906628).sum := by decide
  have hdescent : baseEnd_5906628 < baseStart_5906628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906667 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 4, 2, 2]
def baseStart_5906667 : Nat := 118140960795 + 5906667 * 2 ^ 59
def prefixEnd_5906667 : Nat := 4983230072969 + 3 ^ 40 * 5906667 * 2
def baseEnd_5906667 : Nat := 3032959237050546871898239

theorem tailTrace_5906667 : CollatzResearch.WordTrace tailWord_5906667 prefixEnd_5906667 3032959237050546871898239 := by
  unfold tailWord_5906667
  simp only [CollatzResearch.WordTrace]
  refine ⟨215433844092161712255758255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143622562728107808170505503 215433844092161712255758255)
  ·
    refine ⟨323150766138242568383637383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215433844092161712255758255 323150766138242568383637383)
    ·
      refine ⟨484726149207363852575456075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323150766138242568383637383 484726149207363852575456075)
      ·
        refine ⟨727089223811045778863184113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484726149207363852575456075 727089223811045778863184113)
        ·
          refine ⟨545316917858284334147388085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 727089223811045778863184113 545316917858284334147388085)
          ·
            refine ⟨51123461049214156326317633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 545316917858284334147388085 51123461049214156326317633)
            ·
              refine ⟨38342595786910617244738225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51123461049214156326317633 38342595786910617244738225)
              ·
                refine ⟨28756946840182962933553669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38342595786910617244738225 28756946840182962933553669)
                ·
                  refine ⟨5391927532534305550041313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28756946840182962933553669 5391927532534305550041313)
                  ·
                    refine ⟨4043945649400729162530985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5391927532534305550041313 4043945649400729162530985)
                    ·
                      refine ⟨3032959237050546871898239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043945649400729162530985 3032959237050546871898239)
                      ·
                        rfl

theorem cell23_5906667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 2, 2].length) (baseStart_5906667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906667 prefixEnd_5906667 := by exact prefixLift 5906667
  have htrace : WordTrace (prefixWord ++ tailWord_5906667) baseStart_5906667 baseEnd_5906667 := by
    simpa [prefixWord, tailWord_5906667, baseEnd_5906667] using wordTrace_append hprefix tailTrace_5906667
  have hstable : (prefixWord ++ tailWord_5906667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906667).length < 2 ^ (prefixWord ++ tailWord_5906667).sum := by decide
  have hdescent : baseEnd_5906667 < baseStart_5906667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906671 : List Nat := [1, 1, 2, 1, 6, 3, 2, 1, 1, 3, 2]
def baseStart_5906671 : Nat := 118140960795 + 5906671 * 2 ^ 59
def prefixEnd_5906671 : Nat := 4983230072969 + 3 ^ 40 * 5906671 * 2
def baseEnd_5906671 : Nat := 3032961290973164856248221

theorem tailTrace_5906671 : CollatzResearch.WordTrace tailWord_5906671 prefixEnd_5906671 3032961290973164856248221 := by
  unfold tailWord_5906671
  simp only [CollatzResearch.WordTrace]
  refine ⟨215433989984147220938903867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143622659989431480625935911 215433989984147220938903867)
  ·
    refine ⟨323150984976220831408355801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215433989984147220938903867 323150984976220831408355801)
    ·
      refine ⟨242363238732165623556266851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323150984976220831408355801 242363238732165623556266851)
      ·
        refine ⟨363544858098248435334400277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242363238732165623556266851 363544858098248435334400277)
        ·
          refine ⟨17041165223355395406300013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 363544858098248435334400277 17041165223355395406300013)
          ·
            refine ⟨6390436958758273277362505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17041165223355395406300013 6390436958758273277362505)
            ·
              refine ⟨4792827719068704958021879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6390436958758273277362505 4792827719068704958021879)
              ·
                refine ⟨7189241578603057437032819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4792827719068704958021879 7189241578603057437032819)
                ·
                  refine ⟨10783862367904586155549229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7189241578603057437032819 10783862367904586155549229)
                  ·
                    refine ⟨4043948387964219808330961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10783862367904586155549229 4043948387964219808330961)
                    ·
                      refine ⟨3032961290973164856248221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043948387964219808330961 3032961290973164856248221)
                      ·
                        rfl

theorem cell23_5906671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 1, 3, 2].length) (baseStart_5906671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906671 prefixEnd_5906671 := by exact prefixLift 5906671
  have htrace : WordTrace (prefixWord ++ tailWord_5906671) baseStart_5906671 baseEnd_5906671 := by
    simpa [prefixWord, tailWord_5906671, baseEnd_5906671] using wordTrace_append hprefix tailTrace_5906671
  have hstable : (prefixWord ++ tailWord_5906671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906671).length < 2 ^ (prefixWord ++ tailWord_5906671).sum := by decide
  have hdescent : baseEnd_5906671 < baseStart_5906671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906684 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 4, 2, 2]
def baseStart_5906684 : Nat := 118140960795 + 5906684 * 2 ^ 59
def prefixEnd_5906684 : Nat := 4983230072969 + 3 ^ 40 * 5906684 * 2
def baseEnd_5906684 : Nat := 3032967966221673305385661

theorem tailTrace_5906684 : CollatzResearch.WordTrace tailWord_5906684 prefixEnd_5906684 3032967966221673305385661 := by
  unfold tailWord_5906684
  simp only [CollatzResearch.WordTrace]
  refine ⟨107717232066550062079563553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143622976088733416106084737 107717232066550062079563553)
  ·
    refine ⟨80787924049912546559672665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107717232066550062079563553 80787924049912546559672665)
    ·
      refine ⟨60590943037434409919754499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80787924049912546559672665 60590943037434409919754499)
      ·
        refine ⟨90886414556151614879631749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60590943037434409919754499 90886414556151614879631749)
        ·
          refine ⟨17041202729278427789930953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90886414556151614879631749 17041202729278427789930953)
          ·
            refine ⟨12780902046958820842448215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17041202729278427789930953 12780902046958820842448215)
            ·
              refine ⟨19171353070438231263672323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12780902046958820842448215 19171353070438231263672323)
              ·
                refine ⟨28757029605657346895508485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19171353070438231263672323 28757029605657346895508485)
                ·
                  refine ⟨5391943051060752542907841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28757029605657346895508485 5391943051060752542907841)
                  ·
                    refine ⟨4043957288295564407180881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5391943051060752542907841 4043957288295564407180881)
                    ·
                      refine ⟨3032967966221673305385661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4043957288295564407180881 3032967966221673305385661)
                      ·
                        rfl

theorem cell23_5906684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_5906684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906684 prefixEnd_5906684 := by exact prefixLift 5906684
  have htrace : WordTrace (prefixWord ++ tailWord_5906684) baseStart_5906684 baseEnd_5906684 := by
    simpa [prefixWord, tailWord_5906684, baseEnd_5906684] using wordTrace_append hprefix tailTrace_5906684
  have hstable : (prefixWord ++ tailWord_5906684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906684).length < 2 ^ (prefixWord ++ tailWord_5906684).sum := by decide
  have hdescent : baseEnd_5906684 < baseStart_5906684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906700 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 2, 3, 3]
def baseStart_5906700 : Nat := 118140960795 + 5906700 * 2 ^ 59
def prefixEnd_5906700 : Nat := 4983230072969 + 3 ^ 40 * 5906700 * 2
def baseEnd_5906700 : Nat := 3032976181912145242785587

theorem tailTrace_5906700 : CollatzResearch.WordTrace tailWord_5906700 prefixEnd_5906700 3032976181912145242785587 := by
  unfold tailWord_5906700
  simp only [CollatzResearch.WordTrace]
  refine ⟨107717523850521079445854777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143623365134028105927806369 107717523850521079445854777)
  ·
    refine ⟨80788142887890809584391083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107717523850521079445854777 80788142887890809584391083)
    ·
      refine ⟨121182214331836214376586625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80788142887890809584391083 121182214331836214376586625)
      ·
        refine ⟨90886660748877160782439969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121182214331836214376586625 90886660748877160782439969)
        ·
          refine ⟨68164995561657870586829977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90886660748877160782439969 68164995561657870586829977)
          ·
            refine ⟨51123746671243402940122483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68164995561657870586829977 51123746671243402940122483)
            ·
              refine ⟨76685620006865104410183725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51123746671243402940122483 76685620006865104410183725)
              ·
                refine ⟨28757107502574414153818897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76685620006865104410183725 28757107502574414153818897)
                ·
                  refine ⟨21567830626930810615364173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28757107502574414153818897 21567830626930810615364173)
                  ·
                    refine ⟨8087936485099053980761565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21567830626930810615364173 8087936485099053980761565)
                    ·
                      refine ⟨3032976181912145242785587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8087936485099053980761565 3032976181912145242785587)
                      ·
                        rfl

theorem cell23_5906700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_5906700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906700 prefixEnd_5906700 := by exact prefixLift 5906700
  have htrace : WordTrace (prefixWord ++ tailWord_5906700) baseStart_5906700 baseEnd_5906700 := by
    simpa [prefixWord, tailWord_5906700, baseEnd_5906700] using wordTrace_append hprefix tailTrace_5906700
  have hstable : (prefixWord ++ tailWord_5906700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906700).length < 2 ^ (prefixWord ++ tailWord_5906700).sum := by decide
  have hdescent : baseEnd_5906700 < baseStart_5906700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906720 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 1, 7]
def baseStart_5906720 : Nat := 118140960795 + 5906720 * 2 ^ 59
def prefixEnd_5906720 : Nat := 4983230072969 + 3 ^ 40 * 5906720 * 2
def baseEnd_5906720 : Nat := 1010995483841745054845165

theorem tailTrace_5906720 : CollatzResearch.WordTrace tailWord_5906720 prefixEnd_5906720 1010995483841745054845165 := by
  unfold tailWord_5906720
  simp only [CollatzResearch.WordTrace]
  refine ⟨107717888580484851153718807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143623851440646468204958409 107717888580484851153718807)
  ·
    refine ⟨161576832870727276730578211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107717888580484851153718807 161576832870727276730578211)
    ·
      refine ⟨242365249306090915095867317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161576832870727276730578211 242365249306090915095867317)
      ·
        refine ⟨22721742122446023290237561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242365249306090915095867317 22721742122446023290237561)
        ·
          refine ⟨17041306591834517467678171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22721742122446023290237561 17041306591834517467678171)
          ·
            refine ⟨25561959887751776201517257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17041306591834517467678171 25561959887751776201517257)
            ·
              refine ⟨19171469915813832151137943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25561959887751776201517257 19171469915813832151137943)
              ·
                refine ⟨28757204873720748226706915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19171469915813832151137943 28757204873720748226706915)
                ·
                  refine ⟨43135807310581122340060373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28757204873720748226706915 43135807310581122340060373)
                  ·
                    refine ⟨1010995483841745054845165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43135807310581122340060373 1010995483841745054845165)
                    ·
                      rfl

theorem cell23_5906720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 7].length) (baseStart_5906720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906720 prefixEnd_5906720 := by exact prefixLift 5906720
  have htrace : WordTrace (prefixWord ++ tailWord_5906720) baseStart_5906720 baseEnd_5906720 := by
    simpa [prefixWord, tailWord_5906720, baseEnd_5906720] using wordTrace_append hprefix tailTrace_5906720
  have hstable : (prefixWord ++ tailWord_5906720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906720).length < 2 ^ (prefixWord ++ tailWord_5906720).sum := by decide
  have hdescent : baseEnd_5906720 < baseStart_5906720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906724 : List Nat := [2, 3, 1, 3, 1, 4, 1, 3, 5]
def baseStart_5906724 : Nat := 118140960795 + 5906724 * 2 ^ 59
def prefixEnd_5906724 : Nat := 4983230072969 + 3 ^ 40 * 5906724 * 2
def baseEnd_5906724 : Nat := 336998722827539238765053

theorem tailTrace_5906724 : CollatzResearch.WordTrace tailWord_5906724 prefixEnd_5906724 336998722827539238765053 := by
  unfold tailWord_5906724
  simp only [CollatzResearch.WordTrace]
  refine ⟨107717961526477605495291613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143623948701970140660388817 107717961526477605495291613)
  ·
    refine ⟨40394235572429102060734355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107717961526477605495291613 40394235572429102060734355)
    ·
      refine ⟨60591353358643653091101533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40394235572429102060734355 60591353358643653091101533)
      ·
        refine ⟨22721757509491369909163075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60591353358643653091101533 22721757509491369909163075)
        ·
          refine ⟨34082636264237054863744613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22721757509491369909163075 34082636264237054863744613)
          ·
            refine ⟨6390494299544447786952115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34082636264237054863744613 6390494299544447786952115)
            ·
              refine ⟨9585741449316671680428173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6390494299544447786952115 9585741449316671680428173)
              ·
                refine ⟨3594653043493751880160565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9585741449316671680428173 3594653043493751880160565)
                ·
                  refine ⟨336998722827539238765053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3594653043493751880160565 336998722827539238765053)
                  ·
                    rfl

theorem cell23_5906724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_5906724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906724 prefixEnd_5906724 := by exact prefixLift 5906724
  have htrace : WordTrace (prefixWord ++ tailWord_5906724) baseStart_5906724 baseEnd_5906724 := by
    simpa [prefixWord, tailWord_5906724, baseEnd_5906724] using wordTrace_append hprefix tailTrace_5906724
  have hstable : (prefixWord ++ tailWord_5906724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906724).length < 2 ^ (prefixWord ++ tailWord_5906724).sum := by decide
  have hdescent : baseEnd_5906724 < baseStart_5906724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906737 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 2, 5]
def baseStart_5906737 : Nat := 118140960795 + 5906737 * 2 ^ 59
def prefixEnd_5906737 : Nat := 4983230072969 + 3 ^ 40 * 5906737 * 2
def baseEnd_5906737 : Nat := 1010998393565453866007639

theorem tailTrace_5906737 : CollatzResearch.WordTrace tailWord_5906737 prefixEnd_5906737 1010998393565453866007639 := by
  unfold tailWord_5906737
  simp only [CollatzResearch.WordTrace]
  refine ⟨215436397201908114210806465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143624264801272076140537643 215436397201908114210806465)
  ·
    refine ⟨161577297901431085658104849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215436397201908114210806465 161577297901431085658104849)
    ·
      refine ⟨121182973426073314243578637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161577297901431085658104849 121182973426073314243578637)
      ·
        refine ⟨45443615034777492841341989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121182973426073314243578637 45443615034777492841341989)
        ·
          refine ⟨8520677819020779907751623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45443615034777492841341989 8520677819020779907751623)
          ·
            refine ⟨12781016728531169861627435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8520677819020779907751623 12781016728531169861627435)
            ·
              refine ⟨19171525092796754792441153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12781016728531169861627435 19171525092796754792441153)
              ·
                refine ⟨14378643819597566094330865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19171525092796754792441153 14378643819597566094330865)
                ·
                  refine ⟨10783982864698174570748149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14378643819597566094330865 10783982864698174570748149)
                  ·
                    refine ⟨1010998393565453866007639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10783982864698174570748149 1010998393565453866007639)
                    ·
                      rfl

theorem cell23_5906737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_5906737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906737 prefixEnd_5906737 := by exact prefixLift 5906737
  have htrace : WordTrace (prefixWord ++ tailWord_5906737) baseStart_5906737 baseEnd_5906737 := by
    simpa [prefixWord, tailWord_5906737, baseEnd_5906737] using wordTrace_append hprefix tailTrace_5906737
  have hstable : (prefixWord ++ tailWord_5906737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906737).length < 2 ^ (prefixWord ++ tailWord_5906737).sum := by decide
  have hdescent : baseEnd_5906737 < baseStart_5906737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906760 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 3, 4, 3]
def baseStart_5906760 : Nat := 118140960795 + 5906760 * 2 ^ 59
def prefixEnd_5906760 : Nat := 4983230072969 + 3 ^ 40 * 5906760 * 2
def baseEnd_5906760 : Nat := 3033006990751415008035311

theorem tailTrace_5906760 : CollatzResearch.WordTrace tailWord_5906760 prefixEnd_5906760 3033006990751415008035311 := by
  unfold tailWord_5906760
  simp only [CollatzResearch.WordTrace]
  refine ⟨107718618040412394569446867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143624824053883192759262489 107718618040412394569446867)
  ·
    refine ⟨161577927060618591854170301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107718618040412394569446867 161577927060618591854170301)
    ·
      refine ⟨60591722647731971945313863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161577927060618591854170301 60591722647731971945313863)
      ·
        refine ⟨90887583971597957917970795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60591722647731971945313863 90887583971597957917970795)
        ·
          refine ⟨136331375957396936876956193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90887583971597957917970795 136331375957396936876956193)
          ·
            refine ⟨102248531968047702657717145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136331375957396936876956193 102248531968047702657717145)
            ·
              refine ⟨76686398976035776993287859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102248531968047702657717145 76686398976035776993287859)
              ·
                refine ⟨115029598464053665489931789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76686398976035776993287859 115029598464053665489931789)
                ·
                  refine ⟨43136099424020124558724421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115029598464053665489931789 43136099424020124558724421)
                  ·
                    refine ⟨8088018642003773354760829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43136099424020124558724421 8088018642003773354760829)
                    ·
                      refine ⟨3033006990751415008035311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8088018642003773354760829 3033006990751415008035311)
                      ·
                        rfl

theorem cell23_5906760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_5906760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906760 prefixEnd_5906760 := by exact prefixLift 5906760
  have htrace : WordTrace (prefixWord ++ tailWord_5906760) baseStart_5906760 baseEnd_5906760 := by
    simpa [prefixWord, tailWord_5906760, baseEnd_5906760] using wordTrace_append hprefix tailTrace_5906760
  have hstable : (prefixWord ++ tailWord_5906760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906760).length < 2 ^ (prefixWord ++ tailWord_5906760).sum := by decide
  have hdescent : baseEnd_5906760 < baseStart_5906760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906763 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 10]
def baseStart_5906763 : Nat := 118140960795 + 5906763 * 2 ^ 59
def prefixEnd_5906763 : Nat := 4983230072969 + 3 ^ 40 * 5906763 * 2
def baseEnd_5906763 : Nat := 337000947910375388477533

theorem tailTrace_5906763 : CollatzResearch.WordTrace tailWord_5906763 prefixEnd_5906763 337000947910375388477533 := by
  unfold tailWord_5906763
  simp only [CollatzResearch.WordTrace]
  refine ⟨215437345499813920651252943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143624896999875947100835295 215437345499813920651252943)
  ·
    refine ⟨323156018249720880976879415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215437345499813920651252943 323156018249720880976879415)
    ·
      refine ⟨484734027374581321465319123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323156018249720880976879415 484734027374581321465319123)
      ·
        refine ⟨727101041061871982197978685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484734027374581321465319123 727101041061871982197978685)
        ·
          refine ⟨272662890398201993324242007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 727101041061871982197978685 272662890398201993324242007)
          ·
            refine ⟨408994335597302989986363011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272662890398201993324242007 408994335597302989986363011)
            ·
              refine ⟨613491503395954484979544517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408994335597302989986363011 613491503395954484979544517)
              ·
                refine ⟨115029656886741465933664597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 613491503395954484979544517 115029656886741465933664597)
                ·
                  refine ⟨337000947910375388477533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 115029656886741465933664597 337000947910375388477533)
                  ·
                    rfl

theorem cell23_5906763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 10].length) (baseStart_5906763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906763 prefixEnd_5906763 := by exact prefixLift 5906763
  have htrace : WordTrace (prefixWord ++ tailWord_5906763) baseStart_5906763 baseEnd_5906763 := by
    simpa [prefixWord, tailWord_5906763, baseEnd_5906763] using wordTrace_append hprefix tailTrace_5906763
  have hstable : (prefixWord ++ tailWord_5906763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906763).length < 2 ^ (prefixWord ++ tailWord_5906763).sum := by decide
  have hdescent : baseEnd_5906763 < baseStart_5906763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906770 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_5906770 : Nat := 118140960795 + 5906770 * 2 ^ 59
def prefixEnd_5906770 : Nat := 4983230072969 + 3 ^ 40 * 5906770 * 2
def baseEnd_5906770 : Nat := 3033012125557959968910265

theorem tailTrace_5906770 : CollatzResearch.WordTrace tailWord_5906770 prefixEnd_5906770 3033012125557959968910265 := by
  unfold tailWord_5906770
  simp only [CollatzResearch.WordTrace]
  refine ⟨53859400202697140211689441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143625067207192373897838509 53859400202697140211689441)
  ·
    refine ⟨40394550152022855158767081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53859400202697140211689441 40394550152022855158767081)
    ·
      refine ⟨30295912614017141369075311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40394550152022855158767081 30295912614017141369075311)
      ·
        refine ⟨45443868921025712053612967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30295912614017141369075311 45443868921025712053612967)
        ·
          refine ⟨68165803381538568080419451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45443868921025712053612967 68165803381538568080419451)
          ·
            refine ⟨102248705072307852120629177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68165803381538568080419451 102248705072307852120629177)
            ·
              refine ⟨76686528804230889090471883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102248705072307852120629177 76686528804230889090471883)
              ·
                refine ⟨115029793206346333635707825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76686528804230889090471883 115029793206346333635707825)
                ·
                  refine ⟨86272344904759750226780869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115029793206346333635707825 86272344904759750226780869)
                  ·
                    refine ⟨16176064669642453167521413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86272344904759750226780869 16176064669642453167521413)
                    ·
                      refine ⟨3033012125557959968910265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16176064669642453167521413 3033012125557959968910265)
                      ·
                        rfl

theorem cell23_5906770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_5906770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906770 prefixEnd_5906770 := by exact prefixLift 5906770
  have htrace : WordTrace (prefixWord ++ tailWord_5906770) baseStart_5906770 baseEnd_5906770 := by
    simpa [prefixWord, tailWord_5906770, baseEnd_5906770] using wordTrace_append hprefix tailTrace_5906770
  have hstable : (prefixWord ++ tailWord_5906770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906770).length < 2 ^ (prefixWord ++ tailWord_5906770).sum := by decide
  have hdescent : baseEnd_5906770 < baseStart_5906770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906794 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_5906794 : Nat := 118140960795 + 5906794 * 2 ^ 59
def prefixEnd_5906794 : Nat := 4983230072969 + 3 ^ 40 * 5906794 * 2
def baseEnd_5906794 : Nat := 3033024449093667875010155

theorem tailTrace_5906794 : CollatzResearch.WordTrace tailWord_5906794 prefixEnd_5906794 3033024449093667875010155 := by
  unfold tailWord_5906794
  simp only [CollatzResearch.WordTrace]
  refine ⟨53859619040675403236407859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143625650775134408630420957 53859619040675403236407859)
  ·
    refine ⟨80789428561013104854611789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53859619040675403236407859 80789428561013104854611789)
    ·
      refine ⟨30296035710379914320479421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80789428561013104854611789 30296035710379914320479421)
      ·
        refine ⟨11361013391392467870179783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30296035710379914320479421 11361013391392467870179783)
        ·
          refine ⟨17041520087088701805269675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11361013391392467870179783 17041520087088701805269675)
          ·
            refine ⟨25562280130633052707904513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17041520087088701805269675 25562280130633052707904513)
            ·
              refine ⟨19171710097974789530928385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25562280130633052707904513 19171710097974789530928385)
              ·
                refine ⟨14378782573481092148196289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19171710097974789530928385 14378782573481092148196289)
                ·
                  refine ⟨10784086930110819111147217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14378782573481092148196289 10784086930110819111147217)
                  ·
                    refine ⟨8088065197583114333360413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10784086930110819111147217 8088065197583114333360413)
                    ·
                      refine ⟨3033024449093667875010155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8088065197583114333360413 3033024449093667875010155)
                      ·
                        rfl

theorem cell23_5906794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_5906794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906794 prefixEnd_5906794 := by exact prefixLift 5906794
  have htrace : WordTrace (prefixWord ++ tailWord_5906794) baseStart_5906794 baseEnd_5906794 := by
    simpa [prefixWord, tailWord_5906794, baseEnd_5906794] using wordTrace_append hprefix tailTrace_5906794
  have hstable : (prefixWord ++ tailWord_5906794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906794).length < 2 ^ (prefixWord ++ tailWord_5906794).sum := by decide
  have hdescent : baseEnd_5906794 < baseStart_5906794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906797 : List Nat := [1, 5, 1, 1, 1, 2, 4, 2, 6]
def baseStart_5906797 : Nat := 118140960795 + 5906797 * 2 ^ 59
def prefixEnd_5906797 : Nat := 4983230072969 + 3 ^ 40 * 5906797 * 2
def baseEnd_5906797 : Nat := 337002887726181262585849

theorem tailTrace_5906797 : CollatzResearch.WordTrace tailWord_5906797 prefixEnd_5906797 337002887726181262585849 := by
  unfold tailWord_5906797
  simp only [CollatzResearch.WordTrace]
  refine ⟨215438585581690744457990645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143625723721127162971993763 215438585581690744457990645)
  ·
    refine ⟨20197367398283507292936623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215438585581690744457990645 20197367398283507292936623)
    ·
      refine ⟨30296051097425260939404935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20197367398283507292936623 30296051097425260939404935)
      ·
        refine ⟨45444076646137891409107403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30296051097425260939404935 45444076646137891409107403)
        ·
          refine ⟨68166114969206837113661105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45444076646137891409107403 68166114969206837113661105)
          ·
            refine ⟨51124586226905127835245829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68166114969206837113661105 51124586226905127835245829)
            ·
              refine ⟨9585859917544711469108593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51124586226905127835245829 9585859917544711469108593)
              ·
                refine ⟨7189394938158533601831445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9585859917544711469108593 7189394938158533601831445)
                ·
                  refine ⟨337002887726181262585849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7189394938158533601831445 337002887726181262585849)
                  ·
                    rfl

theorem cell23_5906797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_5906797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906797 prefixEnd_5906797 := by exact prefixLift 5906797
  have htrace : WordTrace (prefixWord ++ tailWord_5906797) baseStart_5906797 baseEnd_5906797 := by
    simpa [prefixWord, tailWord_5906797, baseEnd_5906797] using wordTrace_append hprefix tailTrace_5906797
  have hstable : (prefixWord ++ tailWord_5906797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906797).length < 2 ^ (prefixWord ++ tailWord_5906797).sum := by decide
  have hdescent : baseEnd_5906797 < baseStart_5906797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906820 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_5906820 : Nat := 118140960795 + 5906820 * 2 ^ 59
def prefixEnd_5906820 : Nat := 4983230072969 + 3 ^ 40 * 5906820 * 2
def baseEnd_5906820 : Nat := 3033037799590684773285035

theorem tailTrace_5906820 : CollatzResearch.WordTrace tailWord_5906820 prefixEnd_5906820 3033037799590684773285035 := by
  unfold tailWord_5906820
  simp only [CollatzResearch.WordTrace]
  refine ⟨107719712230303709693038957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143626282973738279590718609 107719712230303709693038957)
  ·
    refine ⟨40394892086363891134889609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107719712230303709693038957 40394892086363891134889609)
    ·
      refine ⟨30296169064772918351167207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40394892086363891134889609 30296169064772918351167207)
      ·
        refine ⟨45444253597159377526750811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30296169064772918351167207 45444253597159377526750811)
        ·
          refine ⟨68166380395739066290126217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45444253597159377526750811 68166380395739066290126217)
          ·
            refine ⟨51124785296804299717594663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68166380395739066290126217 51124785296804299717594663)
            ·
              refine ⟨76687177945206449576391995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51124785296804299717594663 76687177945206449576391995)
              ·
                refine ⟨115030766917809674364587993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76687177945206449576391995 115030766917809674364587993)
                ·
                  refine ⟨86273075188357255773440995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115030766917809674364587993 86273075188357255773440995)
                  ·
                    refine ⟨129409612782535883660161493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86273075188357255773440995 129409612782535883660161493)
                    ·
                      refine ⟨3033037799590684773285035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129409612782535883660161493 3033037799590684773285035)
                      ·
                        rfl

theorem cell23_5906820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_5906820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906820 prefixEnd_5906820 := by exact prefixLift 5906820
  have htrace : WordTrace (prefixWord ++ tailWord_5906820) baseStart_5906820 baseEnd_5906820 := by
    simpa [prefixWord, tailWord_5906820, baseEnd_5906820] using wordTrace_append hprefix tailTrace_5906820
  have hstable : (prefixWord ++ tailWord_5906820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906820).length < 2 ^ (prefixWord ++ tailWord_5906820).sum := by decide
  have hdescent : baseEnd_5906820 < baseStart_5906820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906824 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 3, 1, 3]
def baseStart_5906824 : Nat := 118140960795 + 5906824 * 2 ^ 59
def prefixEnd_5906824 : Nat := 4983230072969 + 3 ^ 40 * 5906824 * 2
def baseEnd_5906824 : Nat := 3033039853513302757635017

theorem tailTrace_5906824 : CollatzResearch.WordTrace tailWord_5906824 prefixEnd_5906824 3033039853513302757635017 := by
  unfold tailWord_5906824
  simp only [CollatzResearch.WordTrace]
  refine ⟨107719785176296464034611763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143626380235061952046149017 107719785176296464034611763)
  ·
    refine ⟨161579677764444696051917645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107719785176296464034611763 161579677764444696051917645)
    ·
      refine ⟨60592379161666761019469117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161579677764444696051917645 60592379161666761019469117)
      ·
        refine ⟨22722142185625035382300919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60592379161666761019469117 22722142185625035382300919)
        ·
          refine ⟨34083213278437553073451379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22722142185625035382300919 34083213278437553073451379)
          ·
            refine ⟨51124819917656329610177069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34083213278437553073451379 51124819917656329610177069)
            ·
              refine ⟨19171807469121123603816401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51124819917656329610177069 19171807469121123603816401)
              ·
                refine ⟨14378855601840842702862301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19171807469121123603816401 14378855601840842702862301)
                ·
                  refine ⟨5392070850690316013573363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14378855601840842702862301 5392070850690316013573363)
                  ·
                    refine ⟨8088106276035474020360045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5392070850690316013573363 8088106276035474020360045)
                    ·
                      refine ⟨3033039853513302757635017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8088106276035474020360045 3033039853513302757635017)
                      ·
                        rfl

theorem cell23_5906824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_5906824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906824 prefixEnd_5906824 := by exact prefixLift 5906824
  have htrace : WordTrace (prefixWord ++ tailWord_5906824) baseStart_5906824 baseEnd_5906824 := by
    simpa [prefixWord, tailWord_5906824, baseEnd_5906824] using wordTrace_append hprefix tailTrace_5906824
  have hstable : (prefixWord ++ tailWord_5906824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906824).length < 2 ^ (prefixWord ++ tailWord_5906824).sum := by decide
  have hdescent : baseEnd_5906824 < baseStart_5906824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906841 : List Nat := [1, 2, 1, 2, 1, 4, 4, 3, 1, 1, 3]
def baseStart_5906841 : Nat := 118140960795 + 5906841 * 2 ^ 59
def prefixEnd_5906841 : Nat := 4983230072969 + 3 ^ 40 * 5906841 * 2
def baseEnd_5906841 : Nat := 3033048582684429191122439

theorem tailTrace_5906841 : CollatzResearch.WordTrace tailWord_5906841 prefixEnd_5906841 3033048582684429191122439 := by
  unfold tailWord_5906841
  simp only [CollatzResearch.WordTrace]
  refine ⟨215440190393531339972592377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143626793595687559981728251 215440190393531339972592377)
  ·
    refine ⟨161580142795148504979444283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215440190393531339972592377 161580142795148504979444283)
    ·
      refine ⟨242370214192722757469166425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161580142795148504979444283 242370214192722757469166425)
      ·
        refine ⟨181777660644542068101874819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242370214192722757469166425 181777660644542068101874819)
        ·
          refine ⟨272666490966813102152812229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181777660644542068101874819 272666490966813102152812229)
          ·
            refine ⟨51124967056277456653652293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 272666490966813102152812229 51124967056277456653652293)
            ·
              refine ⟨9585931323052023122559805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51124967056277456653652293 9585931323052023122559805)
              ·
                refine ⟨3594724246144508670959927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9585931323052023122559805 3594724246144508670959927)
                ·
                  refine ⟨5392086369216763006439891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3594724246144508670959927 5392086369216763006439891)
                  ·
                    refine ⟨8088129553825144509659837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5392086369216763006439891 8088129553825144509659837)
                    ·
                      refine ⟨3033048582684429191122439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8088129553825144509659837 3033048582684429191122439)
                      ·
                        rfl

theorem cell23_5906841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 1, 1, 3].length) (baseStart_5906841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906841 prefixEnd_5906841 := by exact prefixLift 5906841
  have htrace : WordTrace (prefixWord ++ tailWord_5906841) baseStart_5906841 baseEnd_5906841 := by
    simpa [prefixWord, tailWord_5906841, baseEnd_5906841] using wordTrace_append hprefix tailTrace_5906841
  have hstable : (prefixWord ++ tailWord_5906841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906841).length < 2 ^ (prefixWord ++ tailWord_5906841).sum := by decide
  have hdescent : baseEnd_5906841 < baseStart_5906841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906860 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 6]
def baseStart_5906860 : Nat := 118140960795 + 5906860 * 2 ^ 59
def prefixEnd_5906860 : Nat := 4983230072969 + 3 ^ 40 * 5906860 * 2
def baseEnd_5906860 : Nat := 3033058338816864616784851

theorem tailTrace_5906860 : CollatzResearch.WordTrace tailWord_5906860 prefixEnd_5906860 3033058338816864616784851 := by
  unfold tailWord_5906860
  simp only [CollatzResearch.WordTrace]
  refine ⟨107720441690231253108767017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143627255586975004145022689 107720441690231253108767017)
  ·
    refine ⟨80790331267673439831575263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107720441690231253108767017 80790331267673439831575263)
    ·
      refine ⟨121185496901510159747362895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80790331267673439831575263 121185496901510159747362895)
      ·
        refine ⟨181778245352265239621044343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121185496901510159747362895 181778245352265239621044343)
        ·
          refine ⟨272667368028397859431566515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181778245352265239621044343 272667368028397859431566515)
          ·
            refine ⟨409001052042596789147349773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272667368028397859431566515 409001052042596789147349773)
            ·
              refine ⟨153375394515973795930256165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 409001052042596789147349773 153375394515973795930256165)
              ·
                refine ⟨28757886471745086736923031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153375394515973795930256165 28757886471745086736923031)
                ·
                  refine ⟨43136829707617630105384547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28757886471745086736923031 43136829707617630105384547)
                  ·
                    refine ⟨64705244561426445158076821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43136829707617630105384547 64705244561426445158076821)
                    ·
                      refine ⟨3033058338816864616784851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64705244561426445158076821 3033058338816864616784851)
                      ·
                        rfl

theorem cell23_5906860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_5906860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906860 prefixEnd_5906860 := by exact prefixLift 5906860
  have htrace : WordTrace (prefixWord ++ tailWord_5906860) baseStart_5906860 baseEnd_5906860 := by
    simpa [prefixWord, tailWord_5906860, baseEnd_5906860] using wordTrace_append hprefix tailTrace_5906860
  have hstable : (prefixWord ++ tailWord_5906860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906860).length < 2 ^ (prefixWord ++ tailWord_5906860).sum := by decide
  have hdescent : baseEnd_5906860 < baseStart_5906860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906877 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_5906877 : Nat := 118140960795 + 5906877 * 2 ^ 59
def prefixEnd_5906877 : Nat := 4983230072969 + 3 ^ 40 * 5906877 * 2
def baseEnd_5906877 : Nat := 3033067067987991050272273

theorem tailTrace_5906877 : CollatzResearch.WordTrace tailWord_5906877 prefixEnd_5906877 3033067067987991050272273 := by
  unfold tailWord_5906877
  simp only [CollatzResearch.WordTrace]
  refine ⟨215441503421400918120902885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143627668947600612080601923 215441503421400918120902885)
  ·
    refine ⟨40395281891512672147669291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215441503421400918120902885 40395281891512672147669291)
    ·
      refine ⟨60592922837269008221503937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40395281891512672147669291 60592922837269008221503937)
      ·
        refine ⟨45444692127951756166127953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60592922837269008221503937 45444692127951756166127953)
        ·
          refine ⟨34083519095963817124595965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45444692127951756166127953 34083519095963817124595965)
          ·
            refine ⟨12781319660986431421723487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34083519095963817124595965 12781319660986431421723487)
            ·
              refine ⟨19171979491479647132585231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12781319660986431421723487 19171979491479647132585231)
              ·
                refine ⟨28757969237219470698877847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19171979491479647132585231 28757969237219470698877847)
                ·
                  refine ⟨43136953855829206048316771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28757969237219470698877847 43136953855829206048316771)
                  ·
                    refine ⟨64705430783743809072475157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43136953855829206048316771 64705430783743809072475157)
                    ·
                      refine ⟨3033067067987991050272273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64705430783743809072475157 3033067067987991050272273)
                      ·
                        rfl

theorem cell23_5906877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_5906877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906877 prefixEnd_5906877 := by exact prefixLift 5906877
  have htrace : WordTrace (prefixWord ++ tailWord_5906877) baseStart_5906877 baseEnd_5906877 := by
    simpa [prefixWord, tailWord_5906877, baseEnd_5906877] using wordTrace_append hprefix tailTrace_5906877
  have hstable : (prefixWord ++ tailWord_5906877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906877).length < 2 ^ (prefixWord ++ tailWord_5906877).sum := by decide
  have hdescent : baseEnd_5906877 < baseStart_5906877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906887 : List Nat := [1, 1, 4, 1, 1, 4, 4, 7]
def baseStart_5906887 : Nat := 118140960795 + 5906887 * 2 ^ 59
def prefixEnd_5906887 : Nat := 4983230072969 + 3 ^ 40 * 5906887 * 2
def baseEnd_5906887 : Nat := 112336007510908741153601

theorem tailTrace_5906887 : CollatzResearch.WordTrace tailWord_5906887 prefixEnd_5906887 112336007510908741153601 := by
  unfold tailWord_5906887
  simp only [CollatzResearch.WordTrace]
  refine ⟨215441868151364689828766915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143627912100909793219177943 215441868151364689828766915)
  ·
    refine ⟨323162802227047034743150373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215441868151364689828766915 323162802227047034743150373)
    ·
      refine ⟨60593025417571319014340695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323162802227047034743150373 60593025417571319014340695)
      ·
        refine ⟨90889538126356978521511043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60593025417571319014340695 90889538126356978521511043)
        ·
          refine ⟨136334307189535467782266565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90889538126356978521511043 136334307189535467782266565)
          ·
            refine ⟨25562682598037900209174981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136334307189535467782266565 25562682598037900209174981)
            ·
              refine ⟨4793002987132106289220309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25562682598037900209174981 4793002987132106289220309)
              ·
                refine ⟨112336007510908741153601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4793002987132106289220309 112336007510908741153601)
                ·
                  rfl

theorem cell23_5906887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 7].length) (baseStart_5906887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906887 prefixEnd_5906887 := by exact prefixLift 5906887
  have htrace : WordTrace (prefixWord ++ tailWord_5906887) baseStart_5906887 baseEnd_5906887 := by
    simpa [prefixWord, tailWord_5906887, baseEnd_5906887] using wordTrace_append hprefix tailTrace_5906887
  have hstable : (prefixWord ++ tailWord_5906887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906887).length < 2 ^ (prefixWord ++ tailWord_5906887).sum := by decide
  have hdescent : baseEnd_5906887 < baseStart_5906887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906897 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 1, 3, 3]
def baseStart_5906897 : Nat := 118140960795 + 5906897 * 2 ^ 59
def prefixEnd_5906897 : Nat := 4983230072969 + 3 ^ 40 * 5906897 * 2
def baseEnd_5906897 : Nat := 3033077337601080972022181

theorem tailTrace_5906897 : CollatzResearch.WordTrace tailWord_5906897 prefixEnd_5906897 3033077337601080972022181 := by
  unfold tailWord_5906897
  simp only [CollatzResearch.WordTrace]
  refine ⟨215442232881328461536630945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143628155254218974357753963 215442232881328461536630945)
  ·
    refine ⟨161581674660996346152473209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215442232881328461536630945 161581674660996346152473209)
    ·
      refine ⟨121186255995747259614354907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161581674660996346152473209 121186255995747259614354907)
      ·
        refine ⟨181779383993620889421532361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121186255995747259614354907 181779383993620889421532361)
        ·
          refine ⟨136334537995215667066149271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181779383993620889421532361 136334537995215667066149271)
          ·
            refine ⟨204501806992823500599223907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136334537995215667066149271 204501806992823500599223907)
            ·
              refine ⟨306752710489235250898835861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204501806992823500599223907 306752710489235250898835861)
              ·
                refine ⟨14379033304182902385882931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 306752710489235250898835861 14379033304182902385882931)
                ·
                  refine ⟨21568549956274353578824397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14379033304182902385882931 21568549956274353578824397)
                  ·
                    refine ⟨8088206233602882592059149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21568549956274353578824397 8088206233602882592059149)
                    ·
                      refine ⟨3033077337601080972022181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8088206233602882592059149 3033077337601080972022181)
                      ·
                        rfl

theorem cell23_5906897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_5906897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906897 prefixEnd_5906897 := by exact prefixLift 5906897
  have htrace : WordTrace (prefixWord ++ tailWord_5906897) baseStart_5906897 baseEnd_5906897 := by
    simpa [prefixWord, tailWord_5906897, baseEnd_5906897] using wordTrace_append hprefix tailTrace_5906897
  have hstable : (prefixWord ++ tailWord_5906897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906897).length < 2 ^ (prefixWord ++ tailWord_5906897).sum := by decide
  have hdescent : baseEnd_5906897 < baseStart_5906897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906915 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 3, 2, 2]
def baseStart_5906915 : Nat := 118140960795 + 5906915 * 2 ^ 59
def prefixEnd_5906915 : Nat := 4983230072969 + 3 ^ 40 * 5906915 * 2
def baseEnd_5906915 : Nat := 3033086580252861901597099

theorem tailTrace_5906915 : CollatzResearch.WordTrace tailWord_5906915 prefixEnd_5906915 3033086580252861901597099 := by
  unfold tailWord_5906915
  simp only [CollatzResearch.WordTrace]
  refine ⟨215442889395263250610786199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143628592930175500407190799 215442889395263250610786199)
  ·
    refine ⟨323164334092894875916179299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215442889395263250610786199 323164334092894875916179299)
    ·
      refine ⟨484746501139342313874268949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323164334092894875916179299 484746501139342313874268949)
      ·
        refine ⟨22722492240906670962856357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 484746501139342313874268949 22722492240906670962856357)
        ·
          refine ⟨4260467295170000805535567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22722492240906670962856357 4260467295170000805535567)
          ·
            refine ⟨6390700942755001208303351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4260467295170000805535567 6390700942755001208303351)
            ·
              refine ⟨9586051414132501812455027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6390700942755001208303351 9586051414132501812455027)
              ·
                refine ⟨14379077121198752718682541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9586051414132501812455027 14379077121198752718682541)
                ·
                  refine ⟨5392153920449532269505953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14379077121198752718682541 5392153920449532269505953)
                  ·
                    refine ⟨4044115440337149202129465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5392153920449532269505953 4044115440337149202129465)
                    ·
                      refine ⟨3033086580252861901597099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4044115440337149202129465 3033086580252861901597099)
                      ·
                        rfl

theorem cell23_5906915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_5906915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906915 prefixEnd_5906915 := by exact prefixLift 5906915
  have htrace : WordTrace (prefixWord ++ tailWord_5906915) baseStart_5906915 baseEnd_5906915 := by
    simpa [prefixWord, tailWord_5906915, baseEnd_5906915] using wordTrace_append hprefix tailTrace_5906915
  have hstable : (prefixWord ++ tailWord_5906915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906915).length < 2 ^ (prefixWord ++ tailWord_5906915).sum := by decide
  have hdescent : baseEnd_5906915 < baseStart_5906915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906924 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 3, 3, 2]
def baseStart_5906924 : Nat := 118140960795 + 5906924 * 2 ^ 59
def prefixEnd_5906924 : Nat := 4983230072969 + 3 ^ 40 * 5906924 * 2
def baseEnd_5906924 : Nat := 3033091201578752366384557

theorem tailTrace_5906924 : CollatzResearch.WordTrace tailWord_5906924 prefixEnd_5906924 3033091201578752366384557 := by
  unfold tailWord_5906924
  simp only [CollatzResearch.WordTrace]
  refine ⟨107721608826115322573931913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143628811768153763431909217 107721608826115322573931913)
  ·
    refine ⟨80791206619586491930448935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107721608826115322573931913 80791206619586491930448935)
    ·
      refine ⟨121186809929379737895673403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80791206619586491930448935 121186809929379737895673403)
      ·
        refine ⟨181780214894069606843510105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121186809929379737895673403 181780214894069606843510105)
        ·
          refine ⟨136335161170552205132632579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181780214894069606843510105 136335161170552205132632579)
          ·
            refine ⟨204502741755828307698948869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136335161170552205132632579 204502741755828307698948869)
            ·
              refine ⟨38344264079217807693552913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204502741755828307698948869 38344264079217807693552913)
              ·
                refine ⟨28758198059413355770164685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38344264079217807693552913 28758198059413355770164685)
                ·
                  refine ⟨10784324272280008413811757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28758198059413355770164685 10784324272280008413811757)
                  ·
                    refine ⟨4044121602105003155179409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10784324272280008413811757 4044121602105003155179409)
                    ·
                      refine ⟨3033091201578752366384557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4044121602105003155179409 3033091201578752366384557)
                      ·
                        rfl

theorem cell23_5906924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 3, 2].length) (baseStart_5906924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906924 prefixEnd_5906924 := by exact prefixLift 5906924
  have htrace : WordTrace (prefixWord ++ tailWord_5906924) baseStart_5906924 baseEnd_5906924 := by
    simpa [prefixWord, tailWord_5906924, baseEnd_5906924] using wordTrace_append hprefix tailTrace_5906924
  have hstable : (prefixWord ++ tailWord_5906924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906924).length < 2 ^ (prefixWord ++ tailWord_5906924).sum := by decide
  have hdescent : baseEnd_5906924 < baseStart_5906924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906977 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 7]
def baseStart_5906977 : Nat := 118140960795 + 5906977 * 2 ^ 59
def prefixEnd_5906977 : Nat := 4983230072969 + 3 ^ 40 * 5906977 * 2
def baseEnd_5906977 : Nat := 337013157339271184335757

theorem tailTrace_5906977 : CollatzResearch.WordTrace tailWord_5906977 prefixEnd_5906977 337013157339271184335757 := by
  unfold tailWord_5906977
  simp only [CollatzResearch.WordTrace]
  refine ⟨215445150721038635199543185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143630100480692423466362123 215445150721038635199543185)
  ·
    refine ⟨161583863040778976399657389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215445150721038635199543185 161583863040778976399657389)
    ·
      refine ⟨60593948640292116149871521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161583863040778976399657389 60593948640292116149871521)
      ·
        refine ⟨45445461480219087112403641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60593948640292116149871521 45445461480219087112403641)
        ·
          refine ⟨34084096110164315334302731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45445461480219087112403641 34084096110164315334302731)
          ·
            refine ⟨51126144165246473001454097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34084096110164315334302731 51126144165246473001454097)
            ·
              refine ⟨38344608123934854751090573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51126144165246473001454097 38344608123934854751090573)
              ·
                refine ⟨14379228046475570531658965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38344608123934854751090573 14379228046475570531658965)
                ·
                  refine ⟨337013157339271184335757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14379228046475570531658965 337013157339271184335757)
                  ·
                    rfl

theorem cell23_5906977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 7].length) (baseStart_5906977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906977 prefixEnd_5906977 := by exact prefixLift 5906977
  have htrace : WordTrace (prefixWord ++ tailWord_5906977) baseStart_5906977 baseEnd_5906977 := by
    simpa [prefixWord, tailWord_5906977, baseEnd_5906977] using wordTrace_append hprefix tailTrace_5906977
  have hstable : (prefixWord ++ tailWord_5906977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906977).length < 2 ^ (prefixWord ++ tailWord_5906977).sum := by decide
  have hdescent : baseEnd_5906977 < baseStart_5906977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5906984 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_5906984 : Nat := 118140960795 + 5906984 * 2 ^ 59
def prefixEnd_5906984 : Nat := 4983230072969 + 3 ^ 40 * 5906984 * 2
def baseEnd_5906984 : Nat := 3033122010418022131634281

theorem tailTrace_5906984 : CollatzResearch.WordTrace tailWord_5906984 prefixEnd_5906984 3033122010418022131634281 := by
  unfold tailWord_5906984
  simp only [CollatzResearch.WordTrace]
  refine ⟨107722703016006637697524003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143630270688008850263365337 107722703016006637697524003)
  ·
    refine ⟨161584054524009956546286005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107722703016006637697524003 161584054524009956546286005)
    ·
      refine ⟨15148505111625933426214313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161584054524009956546286005 15148505111625933426214313)
      ·
        refine ⟨11361378833719450069660735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15148505111625933426214313 11361378833719450069660735)
        ·
          refine ⟨17042068250579175104491103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11361378833719450069660735 17042068250579175104491103)
          ·
            refine ⟨25563102375868762656736655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17042068250579175104491103 25563102375868762656736655)
            ·
              refine ⟨38344653563803143985104983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25563102375868762656736655 38344653563803143985104983)
              ·
                refine ⟨57516980345704715977657475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38344653563803143985104983 57516980345704715977657475)
                ·
                  refine ⟨86275470518557073966486213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57516980345704715977657475 86275470518557073966486213)
                  ·
                    refine ⟨16176650722229451368716165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86275470518557073966486213 16176650722229451368716165)
                    ·
                      refine ⟨3033122010418022131634281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16176650722229451368716165 3033122010418022131634281)
                      ·
                        rfl

theorem cell23_5906984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_5906984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5906984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5906984 prefixEnd_5906984 := by exact prefixLift 5906984
  have htrace : WordTrace (prefixWord ++ tailWord_5906984) baseStart_5906984 baseEnd_5906984 := by
    simpa [prefixWord, tailWord_5906984, baseEnd_5906984] using wordTrace_append hprefix tailTrace_5906984
  have hstable : (prefixWord ++ tailWord_5906984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5906984).length < 2 ^ (prefixWord ++ tailWord_5906984).sum := by decide
  have hdescent : baseEnd_5906984 < baseStart_5906984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5906984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907007 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 1, 7]
def baseStart_5907007 : Nat := 118140960795 + 5907007 * 2 ^ 59
def prefixEnd_5907007 : Nat := 4983230072969 + 3 ^ 40 * 5907007 * 2
def baseEnd_5907007 : Nat := 1011044606824358513882225

theorem tailTrace_5907007 : CollatzResearch.WordTrace tailWord_5907007 prefixEnd_5907007 1011044606824358513882225 := by
  unfold tailWord_5907007
  simp only [CollatzResearch.WordTrace]
  refine ⟨215446244910929950323135275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143630829940619966882090183 215446244910929950323135275)
  ·
    refine ⟨323169367366394925484702913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215446244910929950323135275 323169367366394925484702913)
    ·
      refine ⟨242377025524796194113527185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323169367366394925484702913 242377025524796194113527185)
      ·
        refine ⟨181782769143597145585145389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242377025524796194113527185 181782769143597145585145389)
        ·
          refine ⟨68168538428848929594429521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181782769143597145585145389 68168538428848929594429521)
          ·
            refine ⟨51126403821636697195822141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68168538428848929594429521 51126403821636697195822141)
            ·
              refine ⟨19172401433113761448433303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51126403821636697195822141 19172401433113761448433303)
              ·
                refine ⟨28758602149670642172649955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19172401433113761448433303 28758602149670642172649955)
                ·
                  refine ⟨43137903224505963258974933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28758602149670642172649955 43137903224505963258974933)
                  ·
                    refine ⟨1011044606824358513882225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43137903224505963258974933 1011044606824358513882225)
                    ·
                      rfl

theorem cell23_5907007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 7].length) (baseStart_5907007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907007 prefixEnd_5907007 := by exact prefixLift 5907007
  have htrace : WordTrace (prefixWord ++ tailWord_5907007) baseStart_5907007 baseEnd_5907007 := by
    simpa [prefixWord, tailWord_5907007, baseEnd_5907007] using wordTrace_append hprefix tailTrace_5907007
  have hstable : (prefixWord ++ tailWord_5907007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907007).length < 2 ^ (prefixWord ++ tailWord_5907007).sum := by decide
  have hdescent : baseEnd_5907007 < baseStart_5907007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907021 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_5907021 : Nat := 118140960795 + 5907021 * 2 ^ 59
def prefixEnd_5907021 : Nat := 4983230072969 + 3 ^ 40 * 5907021 * 2
def baseEnd_5907021 : Nat := 3033141009202238486871611

theorem tailTrace_5907021 : CollatzResearch.WordTrace tailWord_5907021 prefixEnd_5907021 3033141009202238486871611 := by
  unfold tailWord_5907021
  simp only [CollatzResearch.WordTrace]
  refine ⟨215446755532879230714144917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143631170355252820476096611 215446755532879230714144917)
  ·
    refine ⟨10099066665603713939725543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 215446755532879230714144917 10099066665603713939725543)
    ·
      refine ⟨15148599998405570909588315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10099066665603713939725543 15148599998405570909588315)
      ·
        refine ⟨22722899997608356364382473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15148599998405570909588315 22722899997608356364382473)
        ·
          refine ⟨17042174998206267273286855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22722899997608356364382473 17042174998206267273286855)
          ·
            refine ⟨25563262497309400909930283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17042174998206267273286855 25563262497309400909930283)
            ·
              refine ⟨38344893745964101364895425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25563262497309400909930283 38344893745964101364895425)
              ·
                refine ⟨28758670309473076023671569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38344893745964101364895425 28758670309473076023671569)
                ·
                  refine ⟨21569002732104807017753677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28758670309473076023671569 21569002732104807017753677)
                  ·
                    refine ⟨8088376024539302631657629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21569002732104807017753677 8088376024539302631657629)
                    ·
                      refine ⟨3033141009202238486871611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8088376024539302631657629 3033141009202238486871611)
                      ·
                        rfl

theorem cell23_5907021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_5907021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907021 prefixEnd_5907021 := by exact prefixLift 5907021
  have htrace : WordTrace (prefixWord ++ tailWord_5907021) baseStart_5907021 baseEnd_5907021 := by
    simpa [prefixWord, tailWord_5907021, baseEnd_5907021] using wordTrace_append hprefix tailTrace_5907021
  have hstable : (prefixWord ++ tailWord_5907021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907021).length < 2 ^ (prefixWord ++ tailWord_5907021).sum := by decide
  have hdescent : baseEnd_5907021 < baseStart_5907021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907071 : List Nat := [1, 1, 2, 2, 1, 1, 1, 9, 1, 4]
def baseStart_5907071 : Nat := 118140960795 + 5907071 * 2 ^ 59
def prefixEnd_5907071 : Nat := 4983230072969 + 3 ^ 40 * 5907071 * 2
def baseEnd_5907071 : Nat := 1011055561078321097082127

theorem tailTrace_5907071 : CollatzResearch.WordTrace tailWord_5907071 prefixEnd_5907071 1011055561078321097082127 := by
  unfold tailWord_5907071
  simp only [CollatzResearch.WordTrace]
  refine ⟨215448579182698089253465067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143632386121798726168976711 215448579182698089253465067)
  ·
    refine ⟨323172868774047133880197601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215448579182698089253465067 323172868774047133880197601)
    ·
      refine ⟨242379651580535350410148201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323172868774047133880197601 242379651580535350410148201)
      ·
        refine ⟨181784738685401512807611151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242379651580535350410148201 181784738685401512807611151)
        ·
          refine ⟨272677108028102269211416727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181784738685401512807611151 272677108028102269211416727)
          ·
            refine ⟨409015662042153403817125091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272677108028102269211416727 409015662042153403817125091)
            ·
              refine ⟨613523493063230105725687637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409015662042153403817125091 613523493063230105725687637)
              ·
                refine ⟨3594864217167363900736451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 613523493063230105725687637 3594864217167363900736451)
                ·
                  refine ⟨5392296325751045851104677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3594864217167363900736451 5392296325751045851104677)
                  ·
                    refine ⟨1011055561078321097082127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5392296325751045851104677 1011055561078321097082127)
                    ·
                      rfl

theorem cell23_5907071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 1, 4].length) (baseStart_5907071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907071 prefixEnd_5907071 := by exact prefixLift 5907071
  have htrace : WordTrace (prefixWord ++ tailWord_5907071) baseStart_5907071 baseEnd_5907071 := by
    simpa [prefixWord, tailWord_5907071, baseEnd_5907071] using wordTrace_append hprefix tailTrace_5907071
  have hstable : (prefixWord ++ tailWord_5907071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907071).length < 2 ^ (prefixWord ++ tailWord_5907071).sum := by decide
  have hdescent : baseEnd_5907071 < baseStart_5907071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907101 : List Nat := [1, 4, 2, 1, 1, 1, 6, 1, 6]
def baseStart_5907101 : Nat := 118140960795 + 5907101 * 2 ^ 59
def prefixEnd_5907101 : Nat := 4983230072969 + 3 ^ 40 * 5907101 * 2
def baseEnd_5907101 : Nat := 337020231961622019319027

theorem tailTrace_5907101 : CollatzResearch.WordTrace tailWord_5907101 prefixEnd_5907101 337020231961622019319027 := by
  unfold tailWord_5907101
  simp only [CollatzResearch.WordTrace]
  refine ⟨215449673372589404377057157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143633115581726269584704771 215449673372589404377057157)
  ·
    refine ⟨40396813757360513320698217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215449673372589404377057157 40396813757360513320698217)
    ·
      refine ⟨30297610318020384990523663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40396813757360513320698217 30297610318020384990523663)
      ·
        refine ⟨45446415477030577485785495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30297610318020384990523663 45446415477030577485785495)
        ·
          refine ⟨68169623215545866228678243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45446415477030577485785495 68169623215545866228678243)
          ·
            refine ⟨102254434823318799343017365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68169623215545866228678243 102254434823318799343017365)
            ·
              refine ⟨4793176632343068719203939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102254434823318799343017365 4793176632343068719203939)
              ·
                refine ⟨7189764948514603078805909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4793176632343068719203939 7189764948514603078805909)
                ·
                  refine ⟨337020231961622019319027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7189764948514603078805909 337020231961622019319027)
                  ·
                    rfl

theorem cell23_5907101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_5907101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907101 prefixEnd_5907101 := by exact prefixLift 5907101
  have htrace : WordTrace (prefixWord ++ tailWord_5907101) baseStart_5907101 baseEnd_5907101 := by
    simpa [prefixWord, tailWord_5907101, baseEnd_5907101] using wordTrace_append hprefix tailTrace_5907101
  have hstable : (prefixWord ++ tailWord_5907101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907101).length < 2 ^ (prefixWord ++ tailWord_5907101).sum := by decide
  have hdescent : baseEnd_5907101 < baseStart_5907101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907107 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 7]
def baseStart_5907107 : Nat := 118140960795 + 5907107 * 2 ^ 59
def prefixEnd_5907107 : Nat := 4983230072969 + 3 ^ 40 * 5907107 * 2
def baseEnd_5907107 : Nat := 3033185168538525150396215

theorem tailTrace_5907107 : CollatzResearch.WordTrace tailWord_5907107 prefixEnd_5907107 3033185168538525150396215 := by
  unfold tailWord_5907107
  simp only [CollatzResearch.WordTrace]
  refine ⟨215449892210567667401775575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143633261473711778267850383 215449892210567667401775575)
  ·
    refine ⟨323174838315851501102663363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215449892210567667401775575 323174838315851501102663363)
    ·
      refine ⟨484762257473777251653995045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323174838315851501102663363 484762257473777251653995045)
      ·
        refine ⟨90892923276333234685124071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 484762257473777251653995045 90892923276333234685124071)
        ·
          refine ⟨136339384914499852027686107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90892923276333234685124071 136339384914499852027686107)
          ·
            refine ⟨204509077371749778041529161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136339384914499852027686107 204509077371749778041529161)
            ·
              refine ⟨153381808028812333531146871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204509077371749778041529161 153381808028812333531146871)
              ·
                refine ⟨230072712043218500296720307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153381808028812333531146871 230072712043218500296720307)
                ·
                  refine ⟨345109068064827750445080461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230072712043218500296720307 345109068064827750445080461)
                  ·
                    refine ⟨129415900524310406416905173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 345109068064827750445080461 129415900524310406416905173)
                    ·
                      refine ⟨3033185168538525150396215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129415900524310406416905173 3033185168538525150396215)
                      ·
                        rfl

theorem cell23_5907107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_5907107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907107 prefixEnd_5907107 := by exact prefixLift 5907107
  have htrace : WordTrace (prefixWord ++ tailWord_5907107) baseStart_5907107 baseEnd_5907107 := by
    simpa [prefixWord, tailWord_5907107, baseEnd_5907107] using wordTrace_append hprefix tailTrace_5907107
  have hstable : (prefixWord ++ tailWord_5907107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907107).length < 2 ^ (prefixWord ++ tailWord_5907107).sum := by decide
  have hdescent : baseEnd_5907107 < baseStart_5907107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907161 : List Nat := [1, 2, 1, 2, 3, 2, 1, 5, 2, 4]
def baseStart_5907161 : Nat := 118140960795 + 5907161 * 2 ^ 59
def prefixEnd_5907161 : Nat := 4983230072969 + 3 ^ 40 * 5907161 * 2
def baseEnd_5907161 : Nat := 1011070965497955979706989

theorem tailTrace_5907161 : CollatzResearch.WordTrace tailWord_5907161 prefixEnd_5907161 1011070965497955979706989 := by
  unfold tailWord_5907161
  simp only [CollatzResearch.WordTrace]
  refine ⟨215451861752372034624241337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143634574501581356416160891 215451861752372034624241337)
  ·
    refine ⟨161588896314279025968181003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215451861752372034624241337 161588896314279025968181003)
    ·
      refine ⟨242383344471418538952271505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161588896314279025968181003 242383344471418538952271505)
      ·
        refine ⟨181787508353563904214203629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242383344471418538952271505 181787508353563904214203629)
        ·
          refine ⟨68170315632586464080326361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181787508353563904214203629 68170315632586464080326361)
          ·
            refine ⟨51127736724439848060244771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68170315632586464080326361 51127736724439848060244771)
            ·
              refine ⟨76691605086659772090367157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51127736724439848060244771 76691605086659772090367157)
              ·
                refine ⟨7189837976874353633471921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76691605086659772090367157 7189837976874353633471921)
                ·
                  refine ⟨5392378482655765225103941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7189837976874353633471921 5392378482655765225103941)
                  ·
                    refine ⟨1011070965497955979706989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5392378482655765225103941 1011070965497955979706989)
                    ·
                      rfl

theorem cell23_5907161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 4].length) (baseStart_5907161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907161 prefixEnd_5907161 := by exact prefixLift 5907161
  have htrace : WordTrace (prefixWord ++ tailWord_5907161) baseStart_5907161 baseEnd_5907161 := by
    simpa [prefixWord, tailWord_5907161, baseEnd_5907161] using wordTrace_append hprefix tailTrace_5907161
  have hstable : (prefixWord ++ tailWord_5907161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907161).length < 2 ^ (prefixWord ++ tailWord_5907161).sum := by decide
  have hdescent : baseEnd_5907161 < baseStart_5907161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907181 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_5907181 : Nat := 118140960795 + 5907181 * 2 ^ 59
def prefixEnd_5907181 : Nat := 4983230072969 + 3 ^ 40 * 5907181 * 2
def baseEnd_5907181 : Nat := 3033223166106957860870875

theorem tailTrace_5907181 : CollatzResearch.WordTrace tailWord_5907181 prefixEnd_5907181 3033223166106957860870875 := by
  unfold tailWord_5907181
  simp only [CollatzResearch.WordTrace]
  refine ⟨215452591212299578039969397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143635060808199718693312931 215452591212299578039969397)
  ·
    refine ⟨20198680426153085441247131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215452591212299578039969397 20198680426153085441247131)
    ·
      refine ⟨30298020639229628161870697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20198680426153085441247131 30298020639229628161870697)
      ·
        refine ⟨22723515479422221121403023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30298020639229628161870697 22723515479422221121403023)
        ·
          refine ⟨34085273219133331682104535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22723515479422221121403023 34085273219133331682104535)
          ·
            refine ⟨51127909828699997523156803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34085273219133331682104535 51127909828699997523156803)
            ·
              refine ⟨76691864743049996284735205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51127909828699997523156803 76691864743049996284735205)
              ·
                refine ⟨14379724639321874303387851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76691864743049996284735205 14379724639321874303387851)
                ·
                  refine ⟨21569586958982811455081777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14379724639321874303387851 21569586958982811455081777)
                  ·
                    refine ⟨16177190219237108591311333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21569586958982811455081777 16177190219237108591311333)
                    ·
                      refine ⟨3033223166106957860870875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16177190219237108591311333 3033223166106957860870875)
                      ·
                        rfl

theorem cell23_5907181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_5907181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907181 prefixEnd_5907181 := by exact prefixLift 5907181
  have htrace : WordTrace (prefixWord ++ tailWord_5907181) baseStart_5907181 baseEnd_5907181 := by
    simpa [prefixWord, tailWord_5907181, baseEnd_5907181] using wordTrace_append hprefix tailTrace_5907181
  have hstable : (prefixWord ++ tailWord_5907181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907181).length < 2 ^ (prefixWord ++ tailWord_5907181).sum := by decide
  have hdescent : baseEnd_5907181 < baseStart_5907181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907202 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_5907202 : Nat := 118140960795 + 5907202 * 2 ^ 59
def prefixEnd_5907202 : Nat := 4983230072969 + 3 ^ 40 * 5907202 * 2
def baseEnd_5907202 : Nat := 3033233949200702278708279

theorem tailTrace_5907202 : CollatzResearch.WordTrace tailWord_5907202 prefixEnd_5907202 3033233949200702278708279 := by
  unfold tailWord_5907202
  simp only [CollatzResearch.WordTrace]
  refine ⟨53863339286305874656620965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143635571430148999084322573 53863339286305874656620965)
  ·
    refine ⟨10099376116182351498116431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53863339286305874656620965 10099376116182351498116431)
    ·
      refine ⟨15149064174273527247174647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10099376116182351498116431 15149064174273527247174647)
      ·
        refine ⟨22723596261410290870761971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15149064174273527247174647 22723596261410290870761971)
        ·
          refine ⟨34085394392115436306142957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22723596261410290870761971 34085394392115436306142957)
          ·
            refine ⟨12782022897043288614803609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34085394392115436306142957 12782022897043288614803609)
            ·
              refine ⟨9586517172782466461102707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12782022897043288614803609 9586517172782466461102707)
              ·
                refine ⟨14379775759173699691654061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9586517172782466461102707 14379775759173699691654061)
                ·
                  refine ⟨5392415909690137384370273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14379775759173699691654061 5392415909690137384370273)
                  ·
                    refine ⟨4044311932267603038277705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5392415909690137384370273 4044311932267603038277705)
                    ·
                      refine ⟨3033233949200702278708279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4044311932267603038277705 3033233949200702278708279)
                      ·
                        rfl

theorem cell23_5907202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_5907202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907202 prefixEnd_5907202 := by exact prefixLift 5907202
  have htrace : WordTrace (prefixWord ++ tailWord_5907202) baseStart_5907202 baseEnd_5907202 := by
    simpa [prefixWord, tailWord_5907202, baseEnd_5907202] using wordTrace_append hprefix tailTrace_5907202
  have hstable : (prefixWord ++ tailWord_5907202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907202).length < 2 ^ (prefixWord ++ tailWord_5907202).sum := by decide
  have hdescent : baseEnd_5907202 < baseStart_5907202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907236 : List Nat := [2, 3, 1, 3, 4, 1, 1, 3, 1, 2, 2]
def baseStart_5907236 : Nat := 118140960795 + 5907236 * 2 ^ 59
def prefixEnd_5907236 : Nat := 4983230072969 + 3 ^ 40 * 5907236 * 2
def baseEnd_5907236 : Nat := 3033251407542955145683123

theorem tailTrace_5907236 : CollatzResearch.WordTrace tailWord_5907236 prefixEnd_5907236 3033251407542955145683123 := by
  unfold tailWord_5907236
  simp only [CollatzResearch.WordTrace]
  refine ⟨107727298613550161216610781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143636398151400214955481041 107727298613550161216610781)
  ·
    refine ⟨40397736980081310456229043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107727298613550161216610781 40397736980081310456229043)
    ·
      refine ⟨60596605470121965684343565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40397736980081310456229043 60596605470121965684343565)
      ·
        refine ⟨22723727051295737131628837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60596605470121965684343565 22723727051295737131628837)
        ·
          refine ⟨4260698822117950712180407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22723727051295737131628837 4260698822117950712180407)
          ·
            refine ⟨6391048233176926068270611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4260698822117950712180407 6391048233176926068270611)
            ·
              refine ⟨9586572349765389102405917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6391048233176926068270611 9586572349765389102405917)
              ·
                refine ⟨3594964631162020913402219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9586572349765389102405917 3594964631162020913402219)
                ·
                  refine ⟨5392446946743031370103329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3594964631162020913402219 5392446946743031370103329)
                  ·
                    refine ⟨4044335210057273527577497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5392446946743031370103329 4044335210057273527577497)
                    ·
                      refine ⟨3033251407542955145683123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4044335210057273527577497 3033251407542955145683123)
                      ·
                        rfl

theorem cell23_5907236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_5907236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907236 prefixEnd_5907236 := by exact prefixLift 5907236
  have htrace : WordTrace (prefixWord ++ tailWord_5907236) baseStart_5907236 baseEnd_5907236 := by
    simpa [prefixWord, tailWord_5907236, baseEnd_5907236] using wordTrace_append hprefix tailTrace_5907236
  have hstable : (prefixWord ++ tailWord_5907236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907236).length < 2 ^ (prefixWord ++ tailWord_5907236).sum := by decide
  have hdescent : baseEnd_5907236 < baseStart_5907236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907321 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 1, 2, 5]
def baseStart_5907321 : Nat := 118140960795 + 5907321 * 2 ^ 59
def prefixEnd_5907321 : Nat := 4983230072969 + 3 ^ 40 * 5907321 * 2
def baseEnd_5907321 : Nat := 3033295053398587313120231

theorem tailTrace_5907321 : CollatzResearch.WordTrace tailWord_5907321 prefixEnd_5907321 3033295053398587313120231 := by
  unfold tailWord_5907321
  simp only [CollatzResearch.WordTrace]
  refine ⟨215457697431792381950065817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143638464954528254633377211 215457697431792381950065817)
  ·
    refine ⟨161593273073844286462549363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215457697431792381950065817 161593273073844286462549363)
    ·
      refine ⟨242389909610766429693824045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161593273073844286462549363 242389909610766429693824045)
      ·
        refine ⟨90896216104037411135184017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242389909610766429693824045 90896216104037411135184017)
        ·
          refine ⟨68172162078028058351388013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90896216104037411135184017 68172162078028058351388013)
          ·
            refine ⟨25564560779260521881770505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68172162078028058351388013 25564560779260521881770505)
            ·
              refine ⟨19173420584445391411327879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25564560779260521881770505 19173420584445391411327879)
              ·
                refine ⟨28760130876668087116991819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19173420584445391411327879 28760130876668087116991819)
                ·
                  refine ⟨43140196315002130675487729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28760130876668087116991819 43140196315002130675487729)
                  ·
                    refine ⟨32355147236251598006615797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43140196315002130675487729 32355147236251598006615797)
                    ·
                      refine ⟨3033295053398587313120231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32355147236251598006615797 3033295053398587313120231)
                      ·
                        rfl

theorem cell23_5907321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_5907321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907321 prefixEnd_5907321 := by exact prefixLift 5907321
  have htrace : WordTrace (prefixWord ++ tailWord_5907321) baseStart_5907321 baseEnd_5907321 := by
    simpa [prefixWord, tailWord_5907321, baseEnd_5907321] using wordTrace_append hprefix tailTrace_5907321
  have hstable : (prefixWord ++ tailWord_5907321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907321).length < 2 ^ (prefixWord ++ tailWord_5907321).sum := by decide
  have hdescent : baseEnd_5907321 < baseStart_5907321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907331 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 4]
def baseStart_5907331 : Nat := 118140960795 + 5907331 * 2 ^ 59
def prefixEnd_5907331 : Nat := 4983230072969 + 3 ^ 40 * 5907331 * 2
def baseEnd_5907331 : Nat := 3033300188205132273995185

theorem tailTrace_5907331 : CollatzResearch.WordTrace tailWord_5907331 prefixEnd_5907331 3033300188205132273995185 := by
  unfold tailWord_5907331
  simp only [CollatzResearch.WordTrace]
  refine ⟨215458062161756153657929847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143638708107837435771953231 215458062161756153657929847)
  ·
    refine ⟨323187093242634230486894771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215458062161756153657929847 323187093242634230486894771)
    ·
      refine ⟨484780639863951345730342157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323187093242634230486894771 484780639863951345730342157)
      ·
        refine ⟨181792739948981754648878309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 484780639863951345730342157 181792739948981754648878309)
        ·
          refine ⟨34086138740434078996664683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181792739948981754648878309 34086138740434078996664683)
          ·
            refine ⟨51129208110651118494997025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34086138740434078996664683 51129208110651118494997025)
            ·
              refine ⟨38346906082988338871247769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51129208110651118494997025 38346906082988338871247769)
              ·
                refine ⟨28760179562241254153435827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38346906082988338871247769 28760179562241254153435827)
                ·
                  refine ⟨43140269343361881230153741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28760179562241254153435827 43140269343361881230153741)
                  ·
                    refine ⟨16177601003760705461307653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43140269343361881230153741 16177601003760705461307653)
                    ·
                      refine ⟨3033300188205132273995185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16177601003760705461307653 3033300188205132273995185)
                      ·
                        rfl

theorem cell23_5907331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_5907331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907331 prefixEnd_5907331 := by exact prefixLift 5907331
  have htrace : WordTrace (prefixWord ++ tailWord_5907331) baseStart_5907331 baseEnd_5907331 := by
    simpa [prefixWord, tailWord_5907331, baseEnd_5907331] using wordTrace_append hprefix tailTrace_5907331
  have hstable : (prefixWord ++ tailWord_5907331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907331).length < 2 ^ (prefixWord ++ tailWord_5907331).sum := by decide
  have hdescent : baseEnd_5907331 < baseStart_5907331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907348 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_5907348 : Nat := 118140960795 + 5907348 * 2 ^ 59
def prefixEnd_5907348 : Nat := 4983230072969 + 3 ^ 40 * 5907348 * 2
def baseEnd_5907348 : Nat := 3033308917376258707482607

theorem tailTrace_5907348 : CollatzResearch.WordTrace tailWord_5907348 prefixEnd_5907348 3033308917376258707482607 := by
  unfold tailWord_5907348
  simp only [CollatzResearch.WordTrace]
  refine ⟨107729341101347282780649349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143639121468463043707532465 107729341101347282780649349)
  ·
    refine ⟨20199251456502615521371753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107729341101347282780649349 20199251456502615521371753)
    ·
      refine ⟨15149438592376961641028815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20199251456502615521371753 15149438592376961641028815)
      ·
        refine ⟨22724157888565442461543223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15149438592376961641028815 22724157888565442461543223)
        ·
          refine ⟨34086236832848163692314835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22724157888565442461543223 34086236832848163692314835)
          ·
            refine ⟨51129355249272245538472253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34086236832848163692314835 51129355249272245538472253)
            ·
              refine ⟨19173508218477092076927095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51129355249272245538472253 19173508218477092076927095)
              ·
                refine ⟨28760262327715638115390643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19173508218477092076927095 28760262327715638115390643)
                ·
                  refine ⟨43140393491573457173085965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28760262327715638115390643 43140393491573457173085965)
                  ·
                    refine ⟨16177647559340046439907237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43140393491573457173085965 16177647559340046439907237)
                    ·
                      refine ⟨3033308917376258707482607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16177647559340046439907237 3033308917376258707482607)
                      ·
                        rfl

theorem cell23_5907348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_5907348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907348 prefixEnd_5907348 := by exact prefixLift 5907348
  have htrace : WordTrace (prefixWord ++ tailWord_5907348) baseStart_5907348 baseEnd_5907348 := by
    simpa [prefixWord, tailWord_5907348, baseEnd_5907348] using wordTrace_append hprefix tailTrace_5907348
  have hstable : (prefixWord ++ tailWord_5907348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907348).length < 2 ^ (prefixWord ++ tailWord_5907348).sum := by decide
  have hdescent : baseEnd_5907348 < baseStart_5907348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907426 : List Nat := [3, 3, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_5907426 : Nat := 118140960795 + 5907426 * 2 ^ 59
def prefixEnd_5907426 : Nat := 4983230072969 + 3 ^ 40 * 5907426 * 2
def baseEnd_5907426 : Nat := 1011116322955769800769083

theorem tailTrace_5907426 : CollatzResearch.WordTrace tailWord_5907426 prefixEnd_5907426 1011116322955769800769083 := by
  unfold tailWord_5907426
  simp only [CollatzResearch.WordTrace]
  refine ⟨53865381774102996220659533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143641018064274656588425421 53865381774102996220659533)
  ·
    refine ⟨20199518165288623582747325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53865381774102996220659533 20199518165288623582747325)
    ·
      refine ⟨7574819311983233843530247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20199518165288623582747325 7574819311983233843530247)
      ·
        refine ⟨11362228967974850765295371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7574819311983233843530247 11362228967974850765295371)
        ·
          refine ⟨17043343451962276147943057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11362228967974850765295371 17043343451962276147943057)
          ·
            refine ⟨12782507588971707110957293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17043343451962276147943057 12782507588971707110957293)
            ·
              refine ⟨4793440345864390166608985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12782507588971707110957293 4793440345864390166608985)
              ·
                refine ⟨3595080259398292624956739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4793440345864390166608985 3595080259398292624956739)
                ·
                  refine ⟨5392620389097438937435109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595080259398292624956739 5392620389097438937435109)
                  ·
                    refine ⟨1011116322955769800769083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5392620389097438937435109 1011116322955769800769083)
                    ·
                      rfl

theorem cell23_5907426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_5907426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907426 prefixEnd_5907426 := by exact prefixLift 5907426
  have htrace : WordTrace (prefixWord ++ tailWord_5907426) baseStart_5907426 baseEnd_5907426 := by
    simpa [prefixWord, tailWord_5907426, baseEnd_5907426] using wordTrace_append hprefix tailTrace_5907426
  have hstable : (prefixWord ++ tailWord_5907426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907426).length < 2 ^ (prefixWord ++ tailWord_5907426).sum := by decide
  have hdescent : baseEnd_5907426 < baseStart_5907426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907432 : List Nat := [2, 1, 4, 1, 1, 1, 2, 6, 1, 1, 3]
def baseStart_5907432 : Nat := 118140960795 + 5907432 * 2 ^ 59
def prefixEnd_5907432 : Nat := 4983230072969 + 3 ^ 40 * 5907432 * 2
def baseEnd_5907432 : Nat := 3033352049751236378832221

theorem tailTrace_5907432 : CollatzResearch.WordTrace tailWord_5907432 prefixEnd_5907432 3033352049751236378832221 := by
  unfold tailWord_5907432
  simp only [CollatzResearch.WordTrace]
  refine ⟨107730872967195123953678275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143641163956260165271571033 107730872967195123953678275)
  ·
    refine ⟨161596309450792685930517413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107730872967195123953678275 161596309450792685930517413)
    ·
      refine ⟨30299308022023628611972015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161596309450792685930517413 30299308022023628611972015)
      ·
        refine ⟨45448962033035442917958023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30299308022023628611972015 45448962033035442917958023)
        ·
          refine ⟨68173443049553164376937035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45448962033035442917958023 68173443049553164376937035)
          ·
            refine ⟨102260164574329746565405553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68173443049553164376937035 102260164574329746565405553)
            ·
              refine ⟨76695123430747309924054165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102260164574329746565405553 76695123430747309924054165)
              ·
                refine ⟨3595083910816280152690039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76695123430747309924054165 3595083910816280152690039)
                ·
                  refine ⟨5392625866224420229035059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595083910816280152690039 5392625866224420229035059)
                  ·
                    refine ⟨8088938799336630343552589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5392625866224420229035059 8088938799336630343552589)
                    ·
                      refine ⟨3033352049751236378832221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8088938799336630343552589 3033352049751236378832221)
                      ·
                        rfl

theorem cell23_5907432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_5907432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907432 prefixEnd_5907432 := by exact prefixLift 5907432
  have htrace : WordTrace (prefixWord ++ tailWord_5907432) baseStart_5907432 baseEnd_5907432 := by
    simpa [prefixWord, tailWord_5907432, baseEnd_5907432] using wordTrace_append hprefix tailTrace_5907432
  have hstable : (prefixWord ++ tailWord_5907432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907432).length < 2 ^ (prefixWord ++ tailWord_5907432).sum := by decide
  have hdescent : baseEnd_5907432 < baseStart_5907432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907461 : List Nat := [1, 3, 1, 1, 2, 3, 1, 11]
def baseStart_5907461 : Nat := 118140960795 + 5907461 * 2 ^ 59
def prefixEnd_5907461 : Nat := 4983230072969 + 3 ^ 40 * 5907461 * 2
def baseEnd_5907461 : Nat := 112346923729267287606281

theorem tailTrace_5907461 : CollatzResearch.WordTrace tailWord_5907461 prefixEnd_5907461 112346923729267287606281 := by
  unfold tailWord_5907461
  simp only [CollatzResearch.WordTrace]
  refine ⟨215462803651285185860162237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143641869100856790573441491 215462803651285185860162237)
  ·
    refine ⟨80798551369231944697560839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215462803651285185860162237 80798551369231944697560839)
    ·
      refine ⟨121197827053847917046341259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80798551369231944697560839 121197827053847917046341259)
      ·
        refine ⟨181796740580771875569511889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121197827053847917046341259 181796740580771875569511889)
        ·
          refine ⟨136347555435578906677133917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181796740580771875569511889 136347555435578906677133917)
          ·
            refine ⟨51130333288342090003925219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136347555435578906677133917 51130333288342090003925219)
            ·
              refine ⟨76695499932513135005887829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51130333288342090003925219 76695499932513135005887829)
              ·
                refine ⟨112346923729267287606281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 76695499932513135005887829 112346923729267287606281)
                ·
                  rfl

theorem cell23_5907461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 11].length) (baseStart_5907461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907461 prefixEnd_5907461 := by exact prefixLift 5907461
  have htrace : WordTrace (prefixWord ++ tailWord_5907461) baseStart_5907461 baseEnd_5907461 := by
    simpa [prefixWord, tailWord_5907461, baseEnd_5907461] using wordTrace_append hprefix tailTrace_5907461
  have hstable : (prefixWord ++ tailWord_5907461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907461).length < 2 ^ (prefixWord ++ tailWord_5907461).sum := by decide
  have hdescent : baseEnd_5907461 < baseStart_5907461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907468 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 3, 2, 4]
def baseStart_5907468 : Nat := 118140960795 + 5907468 * 2 ^ 59
def prefixEnd_5907468 : Nat := 4983230072969 + 3 ^ 40 * 5907468 * 2
def baseEnd_5907468 : Nat := 3033370535054798237982055

theorem tailTrace_5907468 : CollatzResearch.WordTrace tailWord_5907468 prefixEnd_5907468 3033370535054798237982055 := by
  unfold tailWord_5907468
  simp only [CollatzResearch.WordTrace]
  refine ⟨107731529481129913027833529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143642039308173217370444705 107731529481129913027833529)
  ·
    refine ⟨80798647110847434770875147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107731529481129913027833529 80798647110847434770875147)
    ·
      refine ⟨121197970666271152156312721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80798647110847434770875147 121197970666271152156312721)
      ·
        refine ⟨90898477999703364117234541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121197970666271152156312721 90898477999703364117234541)
        ·
          refine ⟨34086929249888761543962953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90898477999703364117234541 34086929249888761543962953)
          ·
            refine ⟨25565196937416571157972215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34086929249888761543962953 25565196937416571157972215)
            ·
              refine ⟨38347795406124856736958323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25565196937416571157972215 38347795406124856736958323)
              ·
                refine ⟨57521693109187285105437485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38347795406124856736958323 57521693109187285105437485)
                ·
                  refine ⟨21570634915945231914539057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57521693109187285105437485 21570634915945231914539057)
                  ·
                    refine ⟨16177976186958923935904293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21570634915945231914539057 16177976186958923935904293)
                    ·
                      refine ⟨3033370535054798237982055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16177976186958923935904293 3033370535054798237982055)
                      ·
                        rfl

theorem cell23_5907468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_5907468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907468 prefixEnd_5907468 := by exact prefixLift 5907468
  have htrace : WordTrace (prefixWord ++ tailWord_5907468) baseStart_5907468 baseEnd_5907468 := by
    simpa [prefixWord, tailWord_5907468, baseEnd_5907468] using wordTrace_append hprefix tailTrace_5907468
  have hstable : (prefixWord ++ tailWord_5907468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907468).length < 2 ^ (prefixWord ++ tailWord_5907468).sum := by decide
  have hdescent : baseEnd_5907468 < baseStart_5907468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907495 : List Nat := [1, 1, 7, 1, 1, 1, 3, 8]
def baseStart_5907495 : Nat := 118140960795 + 5907495 * 2 ^ 59
def prefixEnd_5907495 : Nat := 4983230072969 + 3 ^ 40 * 5907495 * 2
def baseEnd_5907495 : Nat := 112347570334535912309053

theorem tailTrace_5907495 : CollatzResearch.WordTrace tailWord_5907495 prefixEnd_5907495 112347570334535912309053 := by
  unfold tailWord_5907495
  simp only [CollatzResearch.WordTrace]
  refine ⟨215464043733162009666899939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143642695822108006444599959 215464043733162009666899939)
  ·
    refine ⟨323196065599743014500349909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215464043733162009666899939 323196065599743014500349909)
    ·
      refine ⟨7574907787493976902351951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 323196065599743014500349909 7574907787493976902351951)
      ·
        refine ⟨11362361681240965353527927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7574907787493976902351951 11362361681240965353527927)
        ·
          refine ⟨17043542521861448030291891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11362361681240965353527927 17043542521861448030291891)
          ·
            refine ⟨25565313782792172045437837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17043542521861448030291891 25565313782792172045437837)
            ·
              refine ⟨9586992668547064517039189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25565313782792172045437837 9586992668547064517039189)
              ·
                refine ⟨112347570334535912309053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9586992668547064517039189 112347570334535912309053)
                ·
                  rfl

theorem cell23_5907495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 8].length) (baseStart_5907495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907495 prefixEnd_5907495 := by exact prefixLift 5907495
  have htrace : WordTrace (prefixWord ++ tailWord_5907495) baseStart_5907495 baseEnd_5907495 := by
    simpa [prefixWord, tailWord_5907495, baseEnd_5907495] using wordTrace_append hprefix tailTrace_5907495
  have hstable : (prefixWord ++ tailWord_5907495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907495).length < 2 ^ (prefixWord ++ tailWord_5907495).sum := by decide
  have hdescent : baseEnd_5907495 < baseStart_5907495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907505 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 1, 3, 3]
def baseStart_5907505 : Nat := 118140960795 + 5907505 * 2 ^ 59
def prefixEnd_5907505 : Nat := 4983230072969 + 3 ^ 40 * 5907505 * 2
def baseEnd_5907505 : Nat := 3033389533839014593219385

theorem tailTrace_5907505 : CollatzResearch.WordTrace tailWord_5907505 prefixEnd_5907505 3033389533839014593219385 := by
  unfold tailWord_5907505
  simp only [CollatzResearch.WordTrace]
  refine ⟨215464408463125781374763969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143642938975417187583175979 215464408463125781374763969)
  ·
    refine ⟨161598306347344336031072977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215464408463125781374763969 161598306347344336031072977)
    ·
      refine ⟨121198729760508252023304733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161598306347344336031072977 121198729760508252023304733)
      ·
        refine ⟨45449523660190594508739275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121198729760508252023304733 45449523660190594508739275)
        ·
          refine ⟨68174285490285891763108913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45449523660190594508739275 68174285490285891763108913)
          ·
            refine ⟨51130714117714418822331685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68174285490285891763108913 51130714117714418822331685)
            ·
              refine ⟨9587008897071453529187191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51130714117714418822331685 9587008897071453529187191)
              ·
                refine ⟨14380513345607180293780787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9587008897071453529187191 14380513345607180293780787)
                ·
                  refine ⟨21570770018410770440671181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14380513345607180293780787 21570770018410770440671181)
                  ·
                    refine ⟨8089038756904038915251693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21570770018410770440671181 8089038756904038915251693)
                    ·
                      refine ⟨3033389533839014593219385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8089038756904038915251693 3033389533839014593219385)
                      ·
                        rfl

theorem cell23_5907505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_5907505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907505 prefixEnd_5907505 := by exact prefixLift 5907505
  have htrace : WordTrace (prefixWord ++ tailWord_5907505) baseStart_5907505 baseEnd_5907505 := by
    simpa [prefixWord, tailWord_5907505, baseEnd_5907505] using wordTrace_append hprefix tailTrace_5907505
  have hstable : (prefixWord ++ tailWord_5907505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907505).length < 2 ^ (prefixWord ++ tailWord_5907505).sum := by decide
  have hdescent : baseEnd_5907505 < baseStart_5907505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907526 : List Nat := [6, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_5907526 : Nat := 118140960795 + 5907526 * 2 ^ 59
def prefixEnd_5907526 : Nat := 4983230072969 + 3 ^ 40 * 5907526 * 2
def baseEnd_5907526 : Nat := 3033400316932759011056789

theorem tailTrace_5907526 : CollatzResearch.WordTrace tailWord_5907526 prefixEnd_5907526 3033400316932759011056789 := by
  unfold tailWord_5907526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6733286699876553186289951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143643449597366467974185621 6733286699876553186289951)
  ·
    refine ⟨10099930049814829779434927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6733286699876553186289951 10099930049814829779434927)
    ·
      refine ⟨15149895074722244669152391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10099930049814829779434927 15149895074722244669152391)
      ·
        refine ⟨22724842612083367003728587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15149895074722244669152391 22724842612083367003728587)
        ·
          refine ⟨34087263918125050505592881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22724842612083367003728587 34087263918125050505592881)
          ·
            refine ⟨25565447938593787879194661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34087263918125050505592881 25565447938593787879194661)
            ·
              refine ⟨4793521488486335227348999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25565447938593787879194661 4793521488486335227348999)
              ·
                refine ⟨7190282232729502841023499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4793521488486335227348999 7190282232729502841023499)
                ·
                  refine ⟨10785423349094254261535249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7190282232729502841023499 10785423349094254261535249)
                  ·
                    refine ⟨8089067511820690696151437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10785423349094254261535249 8089067511820690696151437)
                    ·
                      refine ⟨3033400316932759011056789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8089067511820690696151437 3033400316932759011056789)
                      ·
                        rfl

theorem cell23_5907526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_5907526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907526 prefixEnd_5907526 := by exact prefixLift 5907526
  have htrace : WordTrace (prefixWord ++ tailWord_5907526) baseStart_5907526 baseEnd_5907526 := by
    simpa [prefixWord, tailWord_5907526, baseEnd_5907526] using wordTrace_append hprefix tailTrace_5907526
  have hstable : (prefixWord ++ tailWord_5907526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907526).length < 2 ^ (prefixWord ++ tailWord_5907526).sum := by decide
  have hdescent : baseEnd_5907526 < baseStart_5907526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907568 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 7]
def baseStart_5907568 : Nat := 118140960795 + 5907568 * 2 ^ 59
def prefixEnd_5907568 : Nat := 4983230072969 + 3 ^ 40 * 5907568 * 2
def baseEnd_5907568 : Nat := 337046875902249760747955

theorem tailTrace_5907568 : CollatzResearch.WordTrace tailWord_5907568 prefixEnd_5907568 337046875902249760747955 := by
  unfold tailWord_5907568
  simp only [CollatzResearch.WordTrace]
  refine ⟨107733353130948771567153679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143644470841265028756204905 107733353130948771567153679)
  ·
    refine ⟨161600029696423157350730519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107733353130948771567153679 161600029696423157350730519)
    ·
      refine ⟨242400044544634736026095779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161600029696423157350730519 242400044544634736026095779)
      ·
        refine ⟨363600066816952104039143669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242400044544634736026095779 363600066816952104039143669)
        ·
          refine ⟨34087506264089259753669719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 363600066816952104039143669 34087506264089259753669719)
          ·
            refine ⟨51131259396133889630504579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34087506264089259753669719 51131259396133889630504579)
            ·
              refine ⟨76696889094200834445756869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51131259396133889630504579 76696889094200834445756869)
              ·
                refine ⟨14380666705162656458579413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76696889094200834445756869 14380666705162656458579413)
                ·
                  refine ⟨337046875902249760747955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14380666705162656458579413 337046875902249760747955)
                  ·
                    rfl

theorem cell23_5907568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 7].length) (baseStart_5907568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907568 prefixEnd_5907568 := by exact prefixLift 5907568
  have htrace : WordTrace (prefixWord ++ tailWord_5907568) baseStart_5907568 baseEnd_5907568 := by
    simpa [prefixWord, tailWord_5907568, baseEnd_5907568] using wordTrace_append hprefix tailTrace_5907568
  have hstable : (prefixWord ++ tailWord_5907568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907568).length < 2 ^ (prefixWord ++ tailWord_5907568).sum := by decide
  have hdescent : baseEnd_5907568 < baseStart_5907568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907602 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 7]
def baseStart_5907602 : Nat := 118140960795 + 5907602 * 2 ^ 59
def prefixEnd_5907602 : Nat := 4983230072969 + 3 ^ 40 * 5907602 * 2
def baseEnd_5907602 : Nat := 337048815718055634856271

theorem tailTrace_5907602 : CollatzResearch.WordTrace tailWord_5907602 prefixEnd_5907602 337048815718055634856271 := by
  unfold tailWord_5907602
  simp only [CollatzResearch.WordTrace]
  refine ⟨53866986585943591735261265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143645297562516244627363373 53866986585943591735261265)
  ·
    refine ⟨40400239939457693801445949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53866986585943591735261265 40400239939457693801445949)
    ·
      refine ⟨15150089977296635175542231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40400239939457693801445949 15150089977296635175542231)
      ·
        refine ⟨22725134965944952763313347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15150089977296635175542231 22725134965944952763313347)
        ·
          refine ⟨34087702448917429144970021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22725134965944952763313347 34087702448917429144970021)
          ·
            refine ⟨6391444209172017964681879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34087702448917429144970021 6391444209172017964681879)
            ·
              refine ⟨9587166313758026947022819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6391444209172017964681879 9587166313758026947022819)
              ·
                refine ⟨14380749470637040420534229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9587166313758026947022819 14380749470637040420534229)
                ·
                  refine ⟨337048815718055634856271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14380749470637040420534229 337048815718055634856271)
                  ·
                    rfl

theorem cell23_5907602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_5907602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907602 prefixEnd_5907602 := by exact prefixLift 5907602
  have htrace : WordTrace (prefixWord ++ tailWord_5907602) baseStart_5907602 baseEnd_5907602 := by
    simpa [prefixWord, tailWord_5907602, baseEnd_5907602] using wordTrace_append hprefix tailTrace_5907602
  have hstable : (prefixWord ++ tailWord_5907602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907602).length < 2 ^ (prefixWord ++ tailWord_5907602).sum := by decide
  have hdescent : baseEnd_5907602 < baseStart_5907602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907635 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 4]
def baseStart_5907635 : Nat := 118140960795 + 5907635 * 2 ^ 59
def prefixEnd_5907635 : Nat := 4983230072969 + 3 ^ 40 * 5907635 * 2
def baseEnd_5907635 : Nat := 3033456286324099084593787

theorem tailTrace_5907635 : CollatzResearch.WordTrace tailWord_5907635 prefixEnd_5907635 3033456286324099084593787 := by
  unfold tailWord_5907635
  simp only [CollatzResearch.WordTrace]
  refine ⟨215469149952654813576996359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143646099968436542384664239 215469149952654813576996359)
  ·
    refine ⟨323203724928982220365494539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215469149952654813576996359 323203724928982220365494539)
    ·
      refine ⟨484805587393473330548241809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323203724928982220365494539 484805587393473330548241809)
      ·
        refine ⟨363604190545104997911181357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484805587393473330548241809 363604190545104997911181357)
        ·
          refine ⟨136351571454414374216693009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363604190545104997911181357 136351571454414374216693009)
          ·
            refine ⟨102263678590810780662519757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136351571454414374216693009 102263678590810780662519757)
            ·
              refine ⟨38348879471554042748444909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102263678590810780662519757 38348879471554042748444909)
              ·
                refine ⟨14380829801832766030666841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38348879471554042748444909 14380829801832766030666841)
                ·
                  refine ⟨10785622351374574523000131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14380829801832766030666841 10785622351374574523000131)
                  ·
                    refine ⟨16178433527061861784500197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10785622351374574523000131 16178433527061861784500197)
                    ·
                      refine ⟨3033456286324099084593787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16178433527061861784500197 3033456286324099084593787)
                      ·
                        rfl

theorem cell23_5907635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_5907635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907635 prefixEnd_5907635 := by exact prefixLift 5907635
  have htrace : WordTrace (prefixWord ++ tailWord_5907635) baseStart_5907635 baseEnd_5907635 := by
    simpa [prefixWord, tailWord_5907635, baseEnd_5907635] using wordTrace_append hprefix tailTrace_5907635
  have hstable : (prefixWord ++ tailWord_5907635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907635).length < 2 ^ (prefixWord ++ tailWord_5907635).sum := by decide
  have hdescent : baseEnd_5907635 < baseStart_5907635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907669 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 2, 4, 2]
def baseStart_5907669 : Nat := 118140960795 + 5907669 * 2 ^ 59
def prefixEnd_5907669 : Nat := 4983230072969 + 3 ^ 40 * 5907669 * 2
def baseEnd_5907669 : Nat := 3033473744666351951568631

theorem tailTrace_5907669 : CollatzResearch.WordTrace tailWord_5907669 prefixEnd_5907669 3033473744666351951568631 := by
  unfold tailWord_5907669
  simp only [CollatzResearch.WordTrace]
  refine ⟨215470390034531637383734061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143646926689687758255822707 215470390034531637383734061)
  ·
    refine ⟨80801396262949364018900273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215470390034531637383734061 80801396262949364018900273)
    ·
      refine ⟨60601047197212023014175205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80801396262949364018900273 60601047197212023014175205)
      ·
        refine ⟨11362696349477254315157851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60601047197212023014175205 11362696349477254315157851)
        ·
          refine ⟨17044044524215881472736777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11362696349477254315157851 17044044524215881472736777)
          ·
            refine ⟨12783033393161911104552583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17044044524215881472736777 12783033393161911104552583)
            ·
              refine ⟨19174550089742866656828875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12783033393161911104552583 19174550089742866656828875)
              ·
                refine ⟨28761825134614299985243313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19174550089742866656828875 28761825134614299985243313)
                ·
                  refine ⟨21571368850960724988932485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28761825134614299985243313 21571368850960724988932485)
                  ·
                    refine ⟨4044631659555135935424841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21571368850960724988932485 4044631659555135935424841)
                    ·
                      refine ⟨3033473744666351951568631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4044631659555135935424841 3033473744666351951568631)
                      ·
                        rfl

theorem cell23_5907669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_5907669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907669 prefixEnd_5907669 := by exact prefixLift 5907669
  have htrace : WordTrace (prefixWord ++ tailWord_5907669) baseStart_5907669 baseEnd_5907669 := by
    simpa [prefixWord, tailWord_5907669, baseEnd_5907669] using wordTrace_append hprefix tailTrace_5907669
  have hstable : (prefixWord ++ tailWord_5907669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907669).length < 2 ^ (prefixWord ++ tailWord_5907669).sum := by decide
  have hdescent : baseEnd_5907669 < baseStart_5907669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907712 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 4, 3, 2]
def baseStart_5907712 : Nat := 118140960795 + 5907712 * 2 ^ 59
def prefixEnd_5907712 : Nat := 4983230072969 + 3 ^ 40 * 5907712 * 2
def baseEnd_5907712 : Nat := 3033495824334495283330933

theorem tailTrace_5907712 : CollatzResearch.WordTrace tailWord_5907712 prefixEnd_5907712 3033495824334495283330933 := by
  unfold tailWord_5907712
  simp only [CollatzResearch.WordTrace]
  refine ⟨107735979186687927863774695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143647972248917237151699593 107735979186687927863774695)
  ·
    refine ⟨161603968780031891795662043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107735979186687927863774695 161603968780031891795662043)
    ·
      refine ⟨242405953170047837693493065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161603968780031891795662043 242405953170047837693493065)
      ·
        refine ⟨181804464877535878270119799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242405953170047837693493065 181804464877535878270119799)
        ·
          refine ⟨272706697316303817405179699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181804464877535878270119799 272706697316303817405179699)
          ·
            refine ⟨409060045974455726107769549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272706697316303817405179699 409060045974455726107769549)
            ·
              refine ⟨153397517240420897290413581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 409060045974455726107769549 153397517240420897290413581)
              ·
                refine ⟨57524068965157836483905093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153397517240420897290413581 57524068965157836483905093)
                ·
                  refine ⟨10785762930967094340732205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57524068965157836483905093 10785762930967094340732205)
                  ·
                    refine ⟨4044661099112660377774577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10785762930967094340732205 4044661099112660377774577)
                    ·
                      refine ⟨3033495824334495283330933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4044661099112660377774577 3033495824334495283330933)
                      ·
                        rfl

theorem cell23_5907712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 4, 3, 2].length) (baseStart_5907712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907712 prefixEnd_5907712 := by exact prefixLift 5907712
  have htrace : WordTrace (prefixWord ++ tailWord_5907712) baseStart_5907712 baseEnd_5907712 := by
    simpa [prefixWord, tailWord_5907712, baseEnd_5907712] using wordTrace_append hprefix tailTrace_5907712
  have hstable : (prefixWord ++ tailWord_5907712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907712).length < 2 ^ (prefixWord ++ tailWord_5907712).sum := by decide
  have hdescent : baseEnd_5907712 < baseStart_5907712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907745 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_5907745 : Nat := 118140960795 + 5907745 * 2 ^ 59
def prefixEnd_5907745 : Nat := 4983230072969 + 3 ^ 40 * 5907745 * 2
def baseEnd_5907745 : Nat := 3033512769196093654218281

theorem tailTrace_5907745 : CollatzResearch.WordTrace tailWord_5907745 prefixEnd_5907745 3033512769196093654218281 := by
  unfold tailWord_5907745
  simp only [CollatzResearch.WordTrace]
  refine ⟨215473161982256302363500689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143648774654837534909000459 215473161982256302363500689)
  ·
    refine ⟨161604871486692226772625517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215473161982256302363500689 161604871486692226772625517)
    ·
      refine ⟨60601826807509585039734569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161604871486692226772625517 60601826807509585039734569)
      ·
        refine ⟨45451370105632188779800927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60601826807509585039734569 45451370105632188779800927)
        ·
          refine ⟨68177055158448283169701391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45451370105632188779800927 68177055158448283169701391)
          ·
            refine ⟨102265582737672424754552087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68177055158448283169701391 102265582737672424754552087)
            ·
              refine ⟨153398374106508637131828131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102265582737672424754552087 153398374106508637131828131)
              ·
                refine ⟨230097561159762955697742197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153398374106508637131828131 230097561159762955697742197)
                ·
                  refine ⟨21571646358727777096663331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 230097561159762955697742197 21571646358727777096663331)
                  ·
                    refine ⟨32357469538091665644994997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21571646358727777096663331 32357469538091665644994997)
                    ·
                      refine ⟨3033512769196093654218281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32357469538091665644994997 3033512769196093654218281)
                      ·
                        rfl

theorem cell23_5907745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_5907745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907745 prefixEnd_5907745 := by exact prefixLift 5907745
  have htrace : WordTrace (prefixWord ++ tailWord_5907745) baseStart_5907745 baseEnd_5907745 := by
    simpa [prefixWord, tailWord_5907745, baseEnd_5907745] using wordTrace_append hprefix tailTrace_5907745
  have hstable : (prefixWord ++ tailWord_5907745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907745).length < 2 ^ (prefixWord ++ tailWord_5907745).sum := by decide
  have hdescent : baseEnd_5907745 < baseStart_5907745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907762 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_5907762 : Nat := 118140960795 + 5907762 * 2 ^ 59
def prefixEnd_5907762 : Nat := 4983230072969 + 3 ^ 40 * 5907762 * 2
def baseEnd_5907762 : Nat := 3033521498367220087705703

theorem tailTrace_5907762 : CollatzResearch.WordTrace tailWord_5907762 prefixEnd_5907762 3033521498367220087705703 := by
  unfold tailWord_5907762
  simp only [CollatzResearch.WordTrace]
  refine ⟨53868445505798678566717385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143649188015463142844579693 53868445505798678566717385)
  ·
    refine ⟨40401334129349008925038039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53868445505798678566717385 40401334129349008925038039)
    ·
      refine ⟨60602001194023513387557059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40401334129349008925038039 60602001194023513387557059)
      ·
        refine ⟨90903001791035270081335589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60602001194023513387557059 90903001791035270081335589)
        ·
          refine ⟨17044312835819113140250423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90903001791035270081335589 17044312835819113140250423)
          ·
            refine ⟨25566469253728669710375635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17044312835819113140250423 25566469253728669710375635)
            ·
              refine ⟨38349703880593004565563453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25566469253728669710375635 38349703880593004565563453)
              ·
                refine ⟨14381138955222376712086295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38349703880593004565563453 14381138955222376712086295)
                ·
                  refine ⟨21571708432833565068129443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14381138955222376712086295 21571708432833565068129443)
                  ·
                    refine ⟨32357562649250347602194165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21571708432833565068129443 32357562649250347602194165)
                    ·
                      refine ⟨3033521498367220087705703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32357562649250347602194165 3033521498367220087705703)
                      ·
                        rfl

theorem cell23_5907762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_5907762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907762 prefixEnd_5907762 := by exact prefixLift 5907762
  have htrace : WordTrace (prefixWord ++ tailWord_5907762) baseStart_5907762 baseEnd_5907762 := by
    simpa [prefixWord, tailWord_5907762, baseEnd_5907762] using wordTrace_append hprefix tailTrace_5907762
  have hstable : (prefixWord ++ tailWord_5907762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907762).length < 2 ^ (prefixWord ++ tailWord_5907762).sum := by decide
  have hdescent : baseEnd_5907762 < baseStart_5907762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907765 : List Nat := [1, 3, 3, 1, 2, 2, 11]
def baseStart_5907765 : Nat := 118140960795 + 5907765 * 2 ^ 59
def prefixEnd_5907765 : Nat := 4983230072969 + 3 ^ 40 * 5907765 * 2
def baseEnd_5907765 : Nat := 37450901713693624394669

theorem tailTrace_5907765 : CollatzResearch.WordTrace tailWord_5907765 prefixEnd_5907765 37450901713693624394669 := by
  unfold tailWord_5907765
  simp only [CollatzResearch.WordTrace]
  refine ⟨215473891442183845779228749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143649260961455897186152499 215473891442183845779228749)
  ·
    refine ⟨80802709290818942167210781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215473891442183845779228749 80802709290818942167210781)
    ·
      refine ⟨30301015984057103312704043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80802709290818942167210781 30301015984057103312704043)
      ·
        refine ⟨45451523976085654969056065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30301015984057103312704043 45451523976085654969056065)
        ·
          refine ⟨34088642982064241226792049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45451523976085654969056065 34088642982064241226792049)
          ·
            refine ⟨25566482236548180920094037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34088642982064241226792049 25566482236548180920094037)
            ·
              refine ⟨37450901713693624394669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25566482236548180920094037 37450901713693624394669)
              ·
                rfl

theorem cell23_5907765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 11].length) (baseStart_5907765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907765 prefixEnd_5907765 := by exact prefixLift 5907765
  have htrace : WordTrace (prefixWord ++ tailWord_5907765) baseStart_5907765 baseEnd_5907765 := by
    simpa [prefixWord, tailWord_5907765, baseEnd_5907765] using wordTrace_append hprefix tailTrace_5907765
  have hstable : (prefixWord ++ tailWord_5907765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907765).length < 2 ^ (prefixWord ++ tailWord_5907765).sum := by decide
  have hdescent : baseEnd_5907765 < baseStart_5907765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907792 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 3]
def baseStart_5907792 : Nat := 118140960795 + 5907792 * 2 ^ 59
def prefixEnd_5907792 : Nat := 4983230072969 + 3 ^ 40 * 5907792 * 2
def baseEnd_5907792 : Nat := 3033536902786854970330565

theorem tailTrace_5907792 : CollatzResearch.WordTrace tailWord_5907792 prefixEnd_5907792 3033536902786854970330565 := by
  unfold tailWord_5907792
  simp only [CollatzResearch.WordTrace]
  refine ⟨107737438106543014695230815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143649917475390686260307753 107737438106543014695230815)
  ·
    refine ⟨161606157159814522042846223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107737438106543014695230815 161606157159814522042846223)
    ·
      refine ⟨242409235739721783064269335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161606157159814522042846223 242409235739721783064269335)
      ·
        refine ⟨363613853609582674596404003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242409235739721783064269335 363613853609582674596404003)
        ·
          refine ⟨545420780414374011894606005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363613853609582674596404003 545420780414374011894606005)
          ·
            refine ⟨51133198163847563615119313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 545420780414374011894606005 51133198163847563615119313)
            ·
              refine ⟨38349898622885672711339485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51133198163847563615119313 38349898622885672711339485)
              ·
                refine ⟨14381211983582127266752307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38349898622885672711339485 14381211983582127266752307)
                ·
                  refine ⟨21571817975373190900128461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14381211983582127266752307 21571817975373190900128461)
                  ·
                    refine ⟨8089431740764946587548173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21571817975373190900128461 8089431740764946587548173)
                    ·
                      refine ⟨3033536902786854970330565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8089431740764946587548173 3033536902786854970330565)
                      ·
                        rfl

theorem cell23_5907792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 3].length) (baseStart_5907792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907792 prefixEnd_5907792 := by exact prefixLift 5907792
  have htrace : WordTrace (prefixWord ++ tailWord_5907792) baseStart_5907792 baseEnd_5907792 := by
    simpa [prefixWord, tailWord_5907792, baseEnd_5907792] using wordTrace_append hprefix tailTrace_5907792
  have hstable : (prefixWord ++ tailWord_5907792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907792).length < 2 ^ (prefixWord ++ tailWord_5907792).sum := by decide
  have hdescent : baseEnd_5907792 < baseStart_5907792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907826 : List Nat := [3, 2, 1, 2, 1, 2, 4, 2, 2, 1, 3]
def baseStart_5907826 : Nat := 118140960795 + 5907826 * 2 ^ 59
def prefixEnd_5907826 : Nat := 4983230072969 + 3 ^ 40 * 5907826 * 2
def baseEnd_5907826 : Nat := 3033554361129107837305409

theorem tailTrace_5907826 : CollatzResearch.WordTrace tailWord_5907826 prefixEnd_5907826 3033554361129107837305409 := by
  unfold tailWord_5907826
  simp only [CollatzResearch.WordTrace]
  refine ⟨53869029073740713299299833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143650744196641902131466221 53869029073740713299299833)
  ·
    refine ⟨40401771805305534974474875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53869029073740713299299833 40401771805305534974474875)
    ·
      refine ⟨60602657707958302461712313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40401771805305534974474875 60602657707958302461712313)
      ·
        refine ⟨45451993280968726846284235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60602657707958302461712313 45451993280968726846284235)
        ·
          refine ⟨68177989921453090269426353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45451993280968726846284235 68177989921453090269426353)
          ·
            refine ⟨51133492441089817702069765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68177989921453090269426353 51133492441089817702069765)
            ·
              refine ⟨9587529832704340819138081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51133492441089817702069765 9587529832704340819138081)
              ·
                refine ⟨7190647374528255614353561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9587529832704340819138081 7190647374528255614353561)
                ·
                  refine ⟨5392985530896191710765171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7190647374528255614353561 5392985530896191710765171)
                  ·
                    refine ⟨8089478296344287566147757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5392985530896191710765171 8089478296344287566147757)
                    ·
                      refine ⟨3033554361129107837305409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8089478296344287566147757 3033554361129107837305409)
                      ·
                        rfl

theorem cell23_5907826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_5907826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907826 prefixEnd_5907826 := by exact prefixLift 5907826
  have htrace : WordTrace (prefixWord ++ tailWord_5907826) baseStart_5907826 baseEnd_5907826 := by
    simpa [prefixWord, tailWord_5907826, baseEnd_5907826] using wordTrace_append hprefix tailTrace_5907826
  have hstable : (prefixWord ++ tailWord_5907826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907826).length < 2 ^ (prefixWord ++ tailWord_5907826).sum := by decide
  have hdescent : baseEnd_5907826 < baseStart_5907826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907852 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 2, 4, 3]
def baseStart_5907852 : Nat := 118140960795 + 5907852 * 2 ^ 59
def prefixEnd_5907852 : Nat := 4983230072969 + 3 ^ 40 * 5907852 * 2
def baseEnd_5907852 : Nat := 3033567711626124735580289

theorem tailTrace_5907852 : CollatzResearch.WordTrace tailWord_5907852 prefixEnd_5907852 3033567711626124735580289 := by
  unfold tailWord_5907852
  simp only [CollatzResearch.WordTrace]
  refine ⟨107738532296434329818822905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143651376395245773091763873 107738532296434329818822905)
  ·
    refine ⟨80803899222325747364117179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107738532296434329818822905 80803899222325747364117179)
    ·
      refine ⟨121205848833488621046175769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80803899222325747364117179 121205848833488621046175769)
      ·
        refine ⟨90904386625116465784631827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121205848833488621046175769 90904386625116465784631827)
        ·
          refine ⟨136356579937674698676947741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90904386625116465784631827 136356579937674698676947741)
          ·
            refine ⟨51133717476628012003855403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136356579937674698676947741 51133717476628012003855403)
            ·
              refine ⟨76700576214942018005783105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51133717476628012003855403 76700576214942018005783105)
              ·
                refine ⟨57525432161206513504337329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76700576214942018005783105 57525432161206513504337329)
                ·
                  refine ⟨43144074120904885128252997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57525432161206513504337329 43144074120904885128252997)
                  ·
                    refine ⟨8089513897669665961547437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43144074120904885128252997 8089513897669665961547437)
                    ·
                      refine ⟨3033567711626124735580289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8089513897669665961547437 3033567711626124735580289)
                      ·
                        rfl

theorem cell23_5907852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_5907852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907852 prefixEnd_5907852 := by exact prefixLift 5907852
  have htrace : WordTrace (prefixWord ++ tailWord_5907852) baseStart_5907852 baseEnd_5907852 := by
    simpa [prefixWord, tailWord_5907852, baseEnd_5907852] using wordTrace_append hprefix tailTrace_5907852
  have hstable : (prefixWord ++ tailWord_5907852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907852).length < 2 ^ (prefixWord ++ tailWord_5907852).sum := by decide
  have hdescent : baseEnd_5907852 < baseStart_5907852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907866 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2]
def baseStart_5907866 : Nat := 118140960795 + 5907866 * 2 ^ 59
def prefixEnd_5907866 : Nat := 4983230072969 + 3 ^ 40 * 5907866 * 2
def baseEnd_5907866 : Nat := 3033574900355287680805225

theorem tailTrace_5907866 : CollatzResearch.WordTrace tailWord_5907866 prefixEnd_5907866 3033574900355287680805225 := by
  unfold tailWord_5907866
  simp only [CollatzResearch.WordTrace]
  refine ⟨53869393803704485007163863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143651716809878626685770301 53869393803704485007163863)
  ·
    refine ⟨80804090705556727510745795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53869393803704485007163863 80804090705556727510745795)
    ·
      refine ⟨121206136058335091266118693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80804090705556727510745795 121206136058335091266118693)
      ·
        refine ⟨22726150510937829612397255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121206136058335091266118693 22726150510937829612397255)
        ·
          refine ⟨34089225766406744418595883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22726150510937829612397255 34089225766406744418595883)
          ·
            refine ⟨51133838649610116627893825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34089225766406744418595883 51133838649610116627893825)
            ·
              refine ⟨38350378987207587470920369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51133838649610116627893825 38350378987207587470920369)
              ·
                refine ⟨28762784240405690603190277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38350378987207587470920369 28762784240405690603190277)
                ·
                  refine ⟨5393022045076066988098177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28762784240405690603190277 5393022045076066988098177)
                  ·
                    refine ⟨4044766533807050241073633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5393022045076066988098177 4044766533807050241073633)
                    ·
                      refine ⟨3033574900355287680805225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4044766533807050241073633 3033574900355287680805225)
                      ·
                        rfl

theorem cell23_5907866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_5907866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907866 prefixEnd_5907866 := by exact prefixLift 5907866
  have htrace : WordTrace (prefixWord ++ tailWord_5907866) baseStart_5907866 baseEnd_5907866 := by
    simpa [prefixWord, tailWord_5907866, baseEnd_5907866] using wordTrace_append hprefix tailTrace_5907866
  have hstable : (prefixWord ++ tailWord_5907866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907866).length < 2 ^ (prefixWord ++ tailWord_5907866).sum := by decide
  have hdescent : baseEnd_5907866 < baseStart_5907866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907870 : List Nat := [4, 3, 1, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_5907870 : Nat := 118140960795 + 5907870 * 2 ^ 59
def prefixEnd_5907870 : Nat := 4983230072969 + 3 ^ 40 * 5907870 * 2
def baseEnd_5907870 : Nat := 3033576954277905665155207

theorem tailTrace_5907870 : CollatzResearch.WordTrace tailWord_5907870 prefixEnd_5907870 3033576954277905665155207 := by
  unfold tailWord_5907870
  simp only [CollatzResearch.WordTrace]
  refine ⟨26934715138350431088975133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143651814071202299141200709 26934715138350431088975133)
  ·
    refine ⟨10100518176881411658365675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26934715138350431088975133 10100518176881411658365675)
    ·
      refine ⟨15150777265322117487548513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10100518176881411658365675 15150777265322117487548513)
      ·
        refine ⟨11363082948991588115661385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15150777265322117487548513 11363082948991588115661385)
        ·
          refine ⟨8522312211743691086746039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11363082948991588115661385 8522312211743691086746039)
          ·
            refine ⟨12783468317615536630119059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8522312211743691086746039 12783468317615536630119059)
            ·
              refine ⟨19175202476423304945178589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12783468317615536630119059 19175202476423304945178589)
              ·
                refine ⟨7190700928658739354441971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19175202476423304945178589 7190700928658739354441971)
                ·
                  refine ⟨10786051392988109031662957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7190700928658739354441971 10786051392988109031662957)
                  ·
                    refine ⟨4044769272370540886873609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10786051392988109031662957 4044769272370540886873609)
                    ·
                      refine ⟨3033576954277905665155207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4044769272370540886873609 3033576954277905665155207)
                      ·
                        rfl

theorem cell23_5907870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_5907870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907870 prefixEnd_5907870 := by exact prefixLift 5907870
  have htrace : WordTrace (prefixWord ++ tailWord_5907870) baseStart_5907870 baseEnd_5907870 := by
    simpa [prefixWord, tailWord_5907870, baseEnd_5907870] using wordTrace_append hprefix tailTrace_5907870
  have hstable : (prefixWord ++ tailWord_5907870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907870).length < 2 ^ (prefixWord ++ tailWord_5907870).sum := by decide
  have hdescent : baseEnd_5907870 < baseStart_5907870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907889 : List Nat := [1, 2, 2, 4, 1, 1, 1, 6, 5]
def baseStart_5907889 : Nat := 118140960795 + 5907889 * 2 ^ 59
def prefixEnd_5907889 : Nat := 4983230072969 + 3 ^ 40 * 5907889 * 2
def baseEnd_5907889 : Nat := 337065190045593454535291

theorem tailTrace_5907889 : CollatzResearch.WordTrace tailWord_5907889 prefixEnd_5907889 337065190045593454535291 := by
  unfold tailWord_5907889
  simp only [CollatzResearch.WordTrace]
  refine ⟨215478414093734614956742721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143652276062489743304495147 215478414093734614956742721)
  ·
    refine ⟨161608810570300961217557041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215478414093734614956742721 161608810570300961217557041)
    ·
      refine ⟨121206607927725720913167781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161608810570300961217557041 121206607927725720913167781)
      ·
        refine ⟨22726238986448572671218959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121206607927725720913167781 22726238986448572671218959)
        ·
          refine ⟨34089358479672859006828439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22726238986448572671218959 34089358479672859006828439)
          ·
            refine ⟨51134037719509288510242659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34089358479672859006828439 51134037719509288510242659)
            ·
              refine ⟨76701056579263932765363989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51134037719509288510242659 76701056579263932765363989)
              ·
                refine ⟨3595362027152996848376437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76701056579263932765363989 3595362027152996848376437)
                ·
                  refine ⟨337065190045593454535291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3595362027152996848376437 337065190045593454535291)
                  ·
                    rfl

theorem cell23_5907889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 5].length) (baseStart_5907889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907889 prefixEnd_5907889 := by exact prefixLift 5907889
  have htrace : WordTrace (prefixWord ++ tailWord_5907889) baseStart_5907889 baseEnd_5907889 := by
    simpa [prefixWord, tailWord_5907889, baseEnd_5907889] using wordTrace_append hprefix tailTrace_5907889
  have hstable : (prefixWord ++ tailWord_5907889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907889).length < 2 ^ (prefixWord ++ tailWord_5907889).sum := by decide
  have hdescent : baseEnd_5907889 < baseStart_5907889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907900 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 1, 4, 2]
def baseStart_5907900 : Nat := 118140960795 + 5907900 * 2 ^ 59
def prefixEnd_5907900 : Nat := 4983230072969 + 3 ^ 40 * 5907900 * 2
def baseEnd_5907900 : Nat := 3033592358697540547780069

theorem tailTrace_5907900 : CollatzResearch.WordTrace tailWord_5907900 prefixEnd_5907900 3033592358697540547780069 := by
  unfold tailWord_5907900
  simp only [CollatzResearch.WordTrace]
  refine ⟨107739407648347381917696577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143652543531129842556928769 107739407648347381917696577)
  ·
    refine ⟨80804555736260536438272433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107739407648347381917696577 80804555736260536438272433)
    ·
      refine ⟨60603416802195402328704325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80804555736260536438272433 60603416802195402328704325)
      ·
        refine ⟨11363140650411637936632061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60603416802195402328704325 11363140650411637936632061)
        ·
          refine ⟨4261177743904364226237023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11363140650411637936632061 4261177743904364226237023)
          ·
            refine ⟨6391766615856546339355535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4261177743904364226237023 6391766615856546339355535)
            ·
              refine ⟨9587649923784819509033303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6391766615856546339355535 9587649923784819509033303)
              ·
                refine ⟨14381474885677229263549955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9587649923784819509033303 14381474885677229263549955)
                ·
                  refine ⟨21572212328515843895324933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14381474885677229263549955 21572212328515843895324933)
                  ·
                    refine ⟨4044789811596720730373425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21572212328515843895324933 4044789811596720730373425)
                    ·
                      refine ⟨3033592358697540547780069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4044789811596720730373425 3033592358697540547780069)
                      ·
                        rfl

theorem cell23_5907900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_5907900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907900 prefixEnd_5907900 := by exact prefixLift 5907900
  have htrace : WordTrace (prefixWord ++ tailWord_5907900) baseStart_5907900 baseEnd_5907900 := by
    simpa [prefixWord, tailWord_5907900, baseEnd_5907900] using wordTrace_append hprefix tailTrace_5907900
  have hstable : (prefixWord ++ tailWord_5907900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907900).length < 2 ^ (prefixWord ++ tailWord_5907900).sum := by decide
  have hdescent : baseEnd_5907900 < baseStart_5907900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5907939 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 4]
def baseStart_5907939 : Nat := 118140960795 + 5907939 * 2 ^ 59
def prefixEnd_5907939 : Nat := 4983230072969 + 3 ^ 40 * 5907939 * 2
def baseEnd_5907939 : Nat := 3033612384443065895192389

theorem tailTrace_5907939 : CollatzResearch.WordTrace tailWord_5907939 prefixEnd_5907939 3033612384443065895192389 := by
  unfold tailWord_5907939
  simp only [CollatzResearch.WordTrace]
  refine ⟨215480237743553473496062871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143653491829035648997375247 215480237743553473496062871)
  ·
    refine ⟨323220356615330210244094307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215480237743553473496062871 323220356615330210244094307)
    ·
      refine ⟨484830534922995315366141461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323220356615330210244094307 484830534922995315366141461)
      ·
        refine ⟨22726431324515405407787881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 484830534922995315366141461 22726431324515405407787881)
        ·
          refine ⟨17044823493386554055840911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22726431324515405407787881 17044823493386554055840911)
          ·
            refine ⟨25567235240079831083761367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17044823493386554055840911 25567235240079831083761367)
            ·
              refine ⟨38350852860119746625642051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25567235240079831083761367 38350852860119746625642051)
              ·
                refine ⟨57526279290179619938463077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38350852860119746625642051 57526279290179619938463077)
                ·
                  refine ⟨10786177366908678738461827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57526279290179619938463077 10786177366908678738461827)
                  ·
                    refine ⟨16179266050363018107692741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10786177366908678738461827 16179266050363018107692741)
                    ·
                      refine ⟨3033612384443065895192389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16179266050363018107692741 3033612384443065895192389)
                      ·
                        rfl

theorem cell23_5907939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_5907939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5907939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5907939 prefixEnd_5907939 := by exact prefixLift 5907939
  have htrace : WordTrace (prefixWord ++ tailWord_5907939) baseStart_5907939 baseEnd_5907939 := by
    simpa [prefixWord, tailWord_5907939, baseEnd_5907939] using wordTrace_append hprefix tailTrace_5907939
  have hstable : (prefixWord ++ tailWord_5907939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5907939).length < 2 ^ (prefixWord ++ tailWord_5907939).sum := by decide
  have hdescent : baseEnd_5907939 < baseStart_5907939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5907939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908000 : List Nat := [2, 1, 1, 6, 1, 1, 4, 2, 1, 4]
def baseStart_5908000 : Nat := 118140960795 + 5908000 * 2 ^ 59
def prefixEnd_5908000 : Nat := 4983230072969 + 3 ^ 40 * 5908000 * 2
def baseEnd_5908000 : Nat := 1011214568920996718843203

theorem tailTrace_5908000 : CollatzResearch.WordTrace tailWord_5908000 prefixEnd_5908000 1011214568920996718843203 := by
  unfold tailWord_5908000
  simp only [CollatzResearch.WordTrace]
  refine ⟨107741231298166240457016727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143654975064221653942688969 107741231298166240457016727)
  ·
    refine ⟨161611846947249360685525091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107741231298166240457016727 161611846947249360685525091)
    ·
      refine ⟨242417770420874041028287637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161611846947249360685525091 242417770420874041028287637)
      ·
        refine ⟨11363332988478470673200983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 242417770420874041028287637 11363332988478470673200983)
        ·
          refine ⟨17044999482717706009801475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11363332988478470673200983 17044999482717706009801475)
          ·
            refine ⟨25567499224076559014702213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17044999482717706009801475 25567499224076559014702213)
            ·
              refine ⟨4793906104514354815256665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25567499224076559014702213 4793906104514354815256665)
              ·
                refine ⟨3595429578385766111442499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4793906104514354815256665 3595429578385766111442499)
                ·
                  refine ⟨5393144367578649167163749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595429578385766111442499 5393144367578649167163749)
                  ·
                    refine ⟨1011214568920996718843203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5393144367578649167163749 1011214568920996718843203)
                    ·
                      rfl

theorem cell23_5908000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 1, 4].length) (baseStart_5908000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908000 prefixEnd_5908000 := by exact prefixLift 5908000
  have htrace : WordTrace (prefixWord ++ tailWord_5908000) baseStart_5908000 baseEnd_5908000 := by
    simpa [prefixWord, tailWord_5908000, baseEnd_5908000] using wordTrace_append hprefix tailTrace_5908000
  have hstable : (prefixWord ++ tailWord_5908000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908000).length < 2 ^ (prefixWord ++ tailWord_5908000).sum := by decide
  have hdescent : baseEnd_5908000 < baseStart_5908000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908049 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 1, 1, 5]
def baseStart_5908049 : Nat := 118140960795 + 5908049 * 2 ^ 59
def prefixEnd_5908049 : Nat := 4983230072969 + 3 ^ 40 * 5908049 * 2
def baseEnd_5908049 : Nat := 3033668867315060464816883

theorem tailTrace_5908049 : CollatzResearch.WordTrace tailWord_5908049 prefixEnd_5908049 3033668867315060464816883 := by
  unfold tailWord_5908049
  simp only [CollatzResearch.WordTrace]
  refine ⟨215484249773154962282567201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143656166515436641521711467 215484249773154962282567201)
  ·
    refine ⟨161613187329866221711925401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215484249773154962282567201 161613187329866221711925401)
    ·
      refine ⟨121209890497399666283944051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161613187329866221711925401 121209890497399666283944051)
      ·
        refine ⟨181814835746099499425916077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121209890497399666283944051 181814835746099499425916077)
        ·
          refine ⟨68180563404787312284718529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181814835746099499425916077 68180563404787312284718529)
          ·
            refine ⟨51135422553590484213538897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68180563404787312284718529 51135422553590484213538897)
            ·
              refine ⟨38351566915192863160154173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51135422553590484213538897 38351566915192863160154173)
              ·
                refine ⟨14381837593197323685057815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38351566915192863160154173 14381837593197323685057815)
                ·
                  refine ⟨21572756389795985527586723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14381837593197323685057815 21572756389795985527586723)
                  ·
                    refine ⟨32359134584693978291380085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21572756389795985527586723 32359134584693978291380085)
                    ·
                      refine ⟨3033668867315060464816883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32359134584693978291380085 3033668867315060464816883)
                      ·
                        rfl

theorem cell23_5908049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_5908049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908049 prefixEnd_5908049 := by exact prefixLift 5908049
  have htrace : WordTrace (prefixWord ++ tailWord_5908049) baseStart_5908049 baseEnd_5908049 := by
    simpa [prefixWord, tailWord_5908049, baseEnd_5908049] using wordTrace_append hprefix tailTrace_5908049
  have hstable : (prefixWord ++ tailWord_5908049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908049).length < 2 ^ (prefixWord ++ tailWord_5908049).sum := by decide
  have hdescent : baseEnd_5908049 < baseStart_5908049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908086 : List Nat := [5, 1, 1, 2, 2, 2, 1, 9]
def baseStart_5908086 : Nat := 118140960795 + 5908086 * 2 ^ 59
def prefixEnd_5908086 : Nat := 4983230072969 + 3 ^ 40 * 5908086 * 2
def baseEnd_5908086 : Nat := 112358809855528771113119

theorem tailTrace_5908086 : CollatzResearch.WordTrace tailWord_5908086 prefixEnd_5908086 112358809855528771113119 := by
  unfold tailWord_5908086
  simp only [CollatzResearch.WordTrace]
  refine ⟨13467849954626307350104007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143657066182680611734442741 13467849954626307350104007)
  ·
    refine ⟨20201774931939461025156011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13467849954626307350104007 20201774931939461025156011)
    ·
      refine ⟨30302662397909191537734017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20201774931939461025156011 30302662397909191537734017)
      ·
        refine ⟨22726996798431893653300513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30302662397909191537734017 22726996798431893653300513)
        ·
          refine ⟨17045247598823920239975385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22726996798431893653300513 17045247598823920239975385)
          ·
            refine ⟨12783935699117940179981539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17045247598823920239975385 12783935699117940179981539)
            ·
              refine ⟨19175903548676910269972309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12783935699117940179981539 19175903548676910269972309)
              ·
                refine ⟨112358809855528771113119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19175903548676910269972309 112358809855528771113119)
                ·
                  rfl

theorem cell23_5908086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_5908086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908086 prefixEnd_5908086 := by exact prefixLift 5908086
  have htrace : WordTrace (prefixWord ++ tailWord_5908086) baseStart_5908086 baseEnd_5908086 := by
    simpa [prefixWord, tailWord_5908086, baseEnd_5908086] using wordTrace_append hprefix tailTrace_5908086
  have hstable : (prefixWord ++ tailWord_5908086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908086).length < 2 ^ (prefixWord ++ tailWord_5908086).sum := by decide
  have hdescent : baseEnd_5908086 < baseStart_5908086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908096 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 6, 1, 3]
def baseStart_5908096 : Nat := 118140960795 + 5908096 * 2 ^ 59
def prefixEnd_5908096 : Nat := 4983230072969 + 3 ^ 40 * 5908096 * 2
def baseEnd_5908096 : Nat := 3033693000905821780929167

theorem tailTrace_5908096 : CollatzResearch.WordTrace tailWord_5908096 prefixEnd_5908096 3033693000905821780929167 := by
  unfold tailWord_5908096
  simp only [CollatzResearch.WordTrace]
  refine ⟨107742982001992344654764071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143657309335989792873018761 107742982001992344654764071)
  ·
    refine ⟨161614473002988516982146107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107742982001992344654764071 161614473002988516982146107)
    ·
      refine ⟨242421709504482775473219161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161614473002988516982146107 242421709504482775473219161)
      ·
        refine ⟨181816282128362081604914371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242421709504482775473219161 181816282128362081604914371)
        ·
          refine ⟨272724423192543122407371557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181816282128362081604914371 272724423192543122407371557)
          ·
            refine ⟨51135829348601835451382167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 272724423192543122407371557 51135829348601835451382167)
            ·
              refine ⟨76703744022902753177073251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51135829348601835451382167 76703744022902753177073251)
              ·
                refine ⟨115055616034354129765609877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76703744022902753177073251 115055616034354129765609877)
                ·
                  refine ⟨5393232001610349832762963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115055616034354129765609877 5393232001610349832762963)
                  ·
                    refine ⟨8089848002415524749144445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5393232001610349832762963 8089848002415524749144445)
                    ·
                      refine ⟨3033693000905821780929167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8089848002415524749144445 3033693000905821780929167)
                      ·
                        rfl

theorem cell23_5908096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_5908096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908096 prefixEnd_5908096 := by exact prefixLift 5908096
  have htrace : WordTrace (prefixWord ++ tailWord_5908096) baseStart_5908096 baseEnd_5908096 := by
    simpa [prefixWord, tailWord_5908096, baseEnd_5908096] using wordTrace_append hprefix tailTrace_5908096
  have hstable : (prefixWord ++ tailWord_5908096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908096).length < 2 ^ (prefixWord ++ tailWord_5908096).sum := by decide
  have hdescent : baseEnd_5908096 < baseStart_5908096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908097 : List Nat := [1, 2, 4, 2, 1, 2, 3, 3, 1, 2, 2]
def baseStart_5908097 : Nat := 118140960795 + 5908097 * 2 ^ 59
def prefixEnd_5908097 : Nat := 4983230072969 + 3 ^ 40 * 5908097 * 2
def baseEnd_5908097 : Nat := 3033693514386476277016663

theorem tailTrace_5908097 : CollatzResearch.WordTrace tailWord_5908097 prefixEnd_5908097 3033693514386476277016663 := by
  unfold tailWord_5908097
  simp only [CollatzResearch.WordTrace]
  refine ⟨215486000476981066480314545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143657333651320710986876363 215486000476981066480314545)
  ·
    refine ⟨161614500357735799860235909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215486000476981066480314545 161614500357735799860235909)
    ·
      refine ⟨30302718817075462473794233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161614500357735799860235909 30302718817075462473794233)
      ·
        refine ⟨22727039112806596855345675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30302718817075462473794233 22727039112806596855345675)
        ·
          refine ⟨34090558669209895283018513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22727039112806596855345675 34090558669209895283018513)
          ·
            refine ⟨25567919001907421462263885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34090558669209895283018513 25567919001907421462263885)
            ·
              refine ⟨9587969625715283048348957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25567919001907421462263885 9587969625715283048348957)
              ·
                refine ⟨3595488609643231143130859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9587969625715283048348957 3595488609643231143130859)
                ·
                  refine ⟨5393232914464846714696289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595488609643231143130859 5393232914464846714696289)
                  ·
                    refine ⟨4044924685848635036022217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5393232914464846714696289 4044924685848635036022217)
                    ·
                      refine ⟨3033693514386476277016663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4044924685848635036022217 3033693514386476277016663)
                      ·
                        rfl

theorem cell23_5908097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_5908097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908097 prefixEnd_5908097 := by exact prefixLift 5908097
  have htrace : WordTrace (prefixWord ++ tailWord_5908097) baseStart_5908097 baseEnd_5908097 := by
    simpa [prefixWord, tailWord_5908097, baseEnd_5908097] using wordTrace_append hprefix tailTrace_5908097
  have hstable : (prefixWord ++ tailWord_5908097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908097).length < 2 ^ (prefixWord ++ tailWord_5908097).sum := by decide
  have hdescent : baseEnd_5908097 < baseStart_5908097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908114 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_5908114 : Nat := 118140960795 + 5908114 * 2 ^ 59
def prefixEnd_5908114 : Nat := 4983230072969 + 3 ^ 40 * 5908114 * 2
def baseEnd_5908114 : Nat := 3033702243557602710504085

theorem tailTrace_5908114 : CollatzResearch.WordTrace tailWord_5908114 prefixEnd_5908114 3033702243557602710504085 := by
  unfold tailWord_5908114
  simp only [CollatzResearch.WordTrace]
  refine ⟨53871655129479869595920849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143657747011946318922455597 53871655129479869595920849)
  ·
    refine ⟨40403741347109902196940637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53871655129479869595920849 40403741347109902196940637)
    ·
      refine ⟨15151403005166213323852739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40403741347109902196940637 15151403005166213323852739)
      ·
        refine ⟨22727104507749319985779109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15151403005166213323852739 22727104507749319985779109)
        ·
          refine ⟨4261332095202997497333583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22727104507749319985779109 4261332095202997497333583)
          ·
            refine ⟨6391998142804496246000375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4261332095202997497333583 6391998142804496246000375)
            ·
              refine ⟨9587997214206744369000563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6391998142804496246000375 9587997214206744369000563)
              ·
                refine ⟨14381995821310116553500845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9587997214206744369000563 14381995821310116553500845)
                ·
                  refine ⟨5393248432991293707562817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14381995821310116553500845 5393248432991293707562817)
                  ·
                    refine ⟨4044936324743470280672113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5393248432991293707562817 4044936324743470280672113)
                    ·
                      refine ⟨3033702243557602710504085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4044936324743470280672113 3033702243557602710504085)
                      ·
                        rfl

theorem cell23_5908114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_5908114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908114 prefixEnd_5908114 := by exact prefixLift 5908114
  have htrace : WordTrace (prefixWord ++ tailWord_5908114) baseStart_5908114 baseEnd_5908114 := by
    simpa [prefixWord, tailWord_5908114, baseEnd_5908114] using wordTrace_append hprefix tailTrace_5908114
  have hstable : (prefixWord ++ tailWord_5908114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908114).length < 2 ^ (prefixWord ++ tailWord_5908114).sum := by decide
  have hdescent : baseEnd_5908114 < baseStart_5908114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908153 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 6, 2, 2]
def baseStart_5908153 : Nat := 118140960795 + 5908153 * 2 ^ 59
def prefixEnd_5908153 : Nat := 4983230072969 + 3 ^ 40 * 5908153 * 2
def baseEnd_5908153 : Nat := 3033722269303128057916405

theorem tailTrace_5908153 : CollatzResearch.WordTrace tailWord_5908153 prefixEnd_5908153 3033722269303128057916405 := by
  unfold tailWord_5908153
  simp only [CollatzResearch.WordTrace]
  refine ⟨215488042964778188044353113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143658695309852125362902075 215488042964778188044353113)
  ·
    refine ⟨161616032223583641033264835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215488042964778188044353113 161616032223583641033264835)
    ·
      refine ⟨242424048335375461549897253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161616032223583641033264835 242424048335375461549897253)
      ·
        refine ⟨45454509062882899040605735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242424048335375461549897253 45454509062882899040605735)
        ·
          refine ⟨68181763594324348560908603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45454509062882899040605735 68181763594324348560908603)
          ·
            refine ⟨102272645391486522841362905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68181763594324348560908603 102272645391486522841362905)
            ·
              refine ⟨76704484043614892131022179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102272645391486522841362905 76704484043614892131022179)
              ·
                refine ⟨115056726065422338196533269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76704484043614892131022179 115056726065422338196533269)
                ·
                  refine ⟨5393284034316672102962497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115056726065422338196533269 5393284034316672102962497)
                  ·
                    refine ⟨4044963025737504077221873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5393284034316672102962497 4044963025737504077221873)
                    ·
                      refine ⟨3033722269303128057916405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4044963025737504077221873 3033722269303128057916405)
                      ·
                        rfl

theorem cell23_5908153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_5908153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908153 prefixEnd_5908153 := by exact prefixLift 5908153
  have htrace : WordTrace (prefixWord ++ tailWord_5908153) baseStart_5908153 baseEnd_5908153 := by
    simpa [prefixWord, tailWord_5908153, baseEnd_5908153] using wordTrace_append hprefix tailTrace_5908153
  have hstable : (prefixWord ++ tailWord_5908153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908153).length < 2 ^ (prefixWord ++ tailWord_5908153).sum := by decide
  have hdescent : baseEnd_5908153 < baseStart_5908153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908156 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_5908156 : Nat := 118140960795 + 5908156 * 2 ^ 59
def prefixEnd_5908156 : Nat := 4983230072969 + 3 ^ 40 * 5908156 * 2
def baseEnd_5908156 : Nat := 3033723809745091546178891

theorem tailTrace_5908156 : CollatzResearch.WordTrace tailWord_5908156 prefixEnd_5908156 3033723809745091546178891 := by
  unfold tailWord_5908156
  simp only [CollatzResearch.WordTrace]
  refine ⟨107744076191883659778356161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143658768255844879704474881 107744076191883659778356161)
  ·
    refine ⟨80808057143912744833767121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107744076191883659778356161 80808057143912744833767121)
    ·
      refine ⟨60606042857934558625325341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80808057143912744833767121 60606042857934558625325341)
      ·
        refine ⟨22727266071725459484497003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60606042857934558625325341 22727266071725459484497003)
        ·
          refine ⟨34090899107588189226745505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22727266071725459484497003 34090899107588189226745505)
          ·
            refine ⟨25568174330691141920059129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34090899107588189226745505 25568174330691141920059129)
            ·
              refine ⟨19176130748018356440044347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25568174330691141920059129 19176130748018356440044347)
              ·
                refine ⟨28764196122027534660066521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19176130748018356440044347 28764196122027534660066521)
                ·
                  refine ⟨21573147091520650995049891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28764196122027534660066521 21573147091520650995049891)
                  ·
                    refine ⟨32359720637280976492574837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21573147091520650995049891 32359720637280976492574837)
                    ·
                      refine ⟨3033723809745091546178891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32359720637280976492574837 3033723809745091546178891)
                      ·
                        rfl

theorem cell23_5908156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_5908156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908156 prefixEnd_5908156 := by exact prefixLift 5908156
  have htrace : WordTrace (prefixWord ++ tailWord_5908156) baseStart_5908156 baseEnd_5908156 := by
    simpa [prefixWord, tailWord_5908156, baseEnd_5908156] using wordTrace_append hprefix tailTrace_5908156
  have hstable : (prefixWord ++ tailWord_5908156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908156).length < 2 ^ (prefixWord ++ tailWord_5908156).sum := by decide
  have hdescent : baseEnd_5908156 < baseStart_5908156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908186 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3]
def baseStart_5908186 : Nat := 118140960795 + 5908186 * 2 ^ 59
def prefixEnd_5908186 : Nat := 4983230072969 + 3 ^ 40 * 5908186 * 2
def baseEnd_5908186 : Nat := 3033739214164726428803753

theorem tailTrace_5908186 : CollatzResearch.WordTrace tailWord_5908186 prefixEnd_5908186 3033739214164726428803753 := by
  unfold tailWord_5908186
  simp only [CollatzResearch.WordTrace]
  refine ⟨53872311643414658670076103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143659497715772423120202941 53872311643414658670076103)
  ·
    refine ⟨80808467465121988005114155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53872311643414658670076103 80808467465121988005114155)
    ·
      refine ⟨121212701197682982007671233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80808467465121988005114155 121212701197682982007671233)
      ·
        refine ⟨90909525898262236505753425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121212701197682982007671233 90909525898262236505753425)
        ·
          refine ⟨68182144423696677379315069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90909525898262236505753425 68182144423696677379315069)
          ·
            refine ⟨25568304158886254017243151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68182144423696677379315069 25568304158886254017243151)
            ·
              refine ⟨38352456238329381025864727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25568304158886254017243151 38352456238329381025864727)
              ·
                refine ⟨57528684357494071538797091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38352456238329381025864727 57528684357494071538797091)
                ·
                  refine ⟨86293026536241107308195637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57528684357494071538797091 86293026536241107308195637)
                  ·
                    refine ⟨8089971237772603810143341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86293026536241107308195637 8089971237772603810143341)
                    ·
                      refine ⟨3033739214164726428803753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8089971237772603810143341 3033739214164726428803753)
                      ·
                        rfl

theorem cell23_5908186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_5908186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908186 prefixEnd_5908186 := by exact prefixLift 5908186
  have htrace : WordTrace (prefixWord ++ tailWord_5908186) baseStart_5908186 baseEnd_5908186 := by
    simpa [prefixWord, tailWord_5908186, baseEnd_5908186] using wordTrace_append hprefix tailTrace_5908186
  have hstable : (prefixWord ++ tailWord_5908186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908186).length < 2 ^ (prefixWord ++ tailWord_5908186).sum := by decide
  have hdescent : baseEnd_5908186 < baseStart_5908186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908206 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_5908206 : Nat := 118140960795 + 5908206 * 2 ^ 59
def prefixEnd_5908206 : Nat := 4983230072969 + 3 ^ 40 * 5908206 * 2
def baseEnd_5908206 : Nat := 1011249827925938783517887

theorem tailTrace_5908206 : CollatzResearch.WordTrace tailWord_5908206 prefixEnd_5908206 1011249827925938783517887 := by
  unfold tailWord_5908206
  simp only [CollatzResearch.WordTrace]
  refine ⟨26936247004198272262004059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143659984022390785397354981 26936247004198272262004059)
  ·
    refine ⟨40404370506297408393006089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26936247004198272262004059 40404370506297408393006089)
    ·
      refine ⟨30303277879723056294754567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40404370506297408393006089 30303277879723056294754567)
      ·
        refine ⟨45454916819584584442131851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30303277879723056294754567 45454916819584584442131851)
        ·
          refine ⟨68182375229376876663197777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45454916819584584442131851 68182375229376876663197777)
          ·
            refine ⟨51136781422032657497398333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68182375229376876663197777 51136781422032657497398333)
            ·
              refine ⟨19176293033262246561524375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51136781422032657497398333 19176293033262246561524375)
              ·
                refine ⟨28764439549893369842286563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19176293033262246561524375 28764439549893369842286563)
                ·
                  refine ⟨43146659324840054763429845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28764439549893369842286563 43146659324840054763429845)
                  ·
                    refine ⟨1011249827925938783517887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43146659324840054763429845 1011249827925938783517887)
                    ·
                      rfl

theorem cell23_5908206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_5908206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908206 prefixEnd_5908206 := by exact prefixLift 5908206
  have htrace : WordTrace (prefixWord ++ tailWord_5908206) baseStart_5908206 baseEnd_5908206 := by
    simpa [prefixWord, tailWord_5908206, baseEnd_5908206] using wordTrace_append hprefix tailTrace_5908206
  have hstable : (prefixWord ++ tailWord_5908206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908206).length < 2 ^ (prefixWord ++ tailWord_5908206).sum := by decide
  have hdescent : baseEnd_5908206 < baseStart_5908206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908256 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 4]
def baseStart_5908256 : Nat := 118140960795 + 5908256 * 2 ^ 59
def prefixEnd_5908256 : Nat := 4983230072969 + 3 ^ 40 * 5908256 * 2
def baseEnd_5908256 : Nat := 3033775157810541154928431

theorem tailTrace_5908256 : CollatzResearch.WordTrace tailWord_5908256 prefixEnd_5908256 3033775157810541154928431 := by
  unfold tailWord_5908256
  simp only [CollatzResearch.WordTrace]
  refine ⟨107745899841702518317676311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143661199788936691090235081 107745899841702518317676311)
  ·
    refine ⟨161618849762553777476514467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107745899841702518317676311 161618849762553777476514467)
    ·
      refine ⟨242428274643830666214771701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161618849762553777476514467 242428274643830666214771701)
      ·
        refine ⟨22727650747859124957634847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242428274643830666214771701 22727650747859124957634847)
        ·
          refine ⟨34091476121788687436452271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22727650747859124957634847 34091476121788687436452271)
          ·
            refine ⟨51137214182683031154678407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34091476121788687436452271 51137214182683031154678407)
            ·
              refine ⟨76705821274024546732017611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51137214182683031154678407 76705821274024546732017611)
              ·
                refine ⟨115058731911036820098026417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76705821274024546732017611 115058731911036820098026417)
                ·
                  refine ⟨86294048933277615073519813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115058731911036820098026417 86294048933277615073519813)
                  ·
                    refine ⟨16180134174989552826284965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86294048933277615073519813 16180134174989552826284965)
                    ·
                      refine ⟨3033775157810541154928431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16180134174989552826284965 3033775157810541154928431)
                      ·
                        rfl

theorem cell23_5908256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_5908256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908256 prefixEnd_5908256 := by exact prefixLift 5908256
  have htrace : WordTrace (prefixWord ++ tailWord_5908256) baseStart_5908256 baseEnd_5908256 := by
    simpa [prefixWord, tailWord_5908256, baseEnd_5908256] using wordTrace_append hprefix tailTrace_5908256
  have hstable : (prefixWord ++ tailWord_5908256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908256).length < 2 ^ (prefixWord ++ tailWord_5908256).sum := by decide
  have hdescent : baseEnd_5908256 < baseStart_5908256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908287 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 3, 4]
def baseStart_5908287 : Nat := 118140960795 + 5908287 * 2 ^ 59
def prefixEnd_5908287 : Nat := 4983230072969 + 3 ^ 40 * 5908287 * 2
def baseEnd_5908287 : Nat := 1011263691903610177880263

theorem tailTrace_5908287 : CollatzResearch.WordTrace tailWord_5908287 prefixEnd_5908287 1011263691903610177880263 := by
  unfold tailWord_5908287
  simp only [CollatzResearch.WordTrace]
  refine ⟨215492930346292728929731115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143661953564195152619820743 215492930346292728929731115)
  ·
    refine ⟨323239395519439093394596673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215492930346292728929731115 323239395519439093394596673)
    ·
      refine ⟨242429546639579320045947505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323239395519439093394596673 242429546639579320045947505)
      ·
        refine ⟨181822159979684490034460629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242429546639579320045947505 181822159979684490034460629)
        ·
          refine ⟨4261456874523855235182671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 181822159979684490034460629 4261456874523855235182671)
          ·
            refine ⟨6392185311785782852774007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4261456874523855235182671 6392185311785782852774007)
            ·
              refine ⟨9588277967678674279161011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6392185311785782852774007 9588277967678674279161011)
              ·
                refine ⟨14382416951518011418741517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9588277967678674279161011 14382416951518011418741517)
                ·
                  refine ⟨5393406356819254282028069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14382416951518011418741517 5393406356819254282028069)
                  ·
                    refine ⟨1011263691903610177880263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5393406356819254282028069 1011263691903610177880263)
                    ·
                      rfl

theorem cell23_5908287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 3, 4].length) (baseStart_5908287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908287 prefixEnd_5908287 := by exact prefixLift 5908287
  have htrace : WordTrace (prefixWord ++ tailWord_5908287) baseStart_5908287 baseEnd_5908287 := by
    simpa [prefixWord, tailWord_5908287, baseEnd_5908287] using wordTrace_append hprefix tailTrace_5908287
  have hstable : (prefixWord ++ tailWord_5908287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908287).length < 2 ^ (prefixWord ++ tailWord_5908287).sum := by decide
  have hdescent : baseEnd_5908287 < baseStart_5908287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908320 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 2, 3, 2]
def baseStart_5908320 : Nat := 118140960795 + 5908320 * 2 ^ 59
def prefixEnd_5908320 : Nat := 4983230072969 + 3 ^ 40 * 5908320 * 2
def baseEnd_5908320 : Nat := 3033808020572428904528137

theorem tailTrace_5908320 : CollatzResearch.WordTrace tailWord_5908320 prefixEnd_5908320 3033808020572428904528137 := by
  unfold tailWord_5908320
  simp only [CollatzResearch.WordTrace]
  refine ⟨107747066977586587782841207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143662755970115450377121609 107747066977586587782841207)
  ·
    refine ⟨161620600466379881674261811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107747066977586587782841207 161620600466379881674261811)
    ·
      refine ⟨242430900699569822511392717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161620600466379881674261811 242430900699569822511392717)
      ·
        refine ⟨90911587762338683441772269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242430900699569822511392717 90911587762338683441772269)
        ·
          refine ⟨34091845410877006290664601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90911587762338683441772269 34091845410877006290664601)
          ·
            refine ⟨25568884058157754717998451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34091845410877006290664601 25568884058157754717998451)
            ·
              refine ⟨38353326087236632076997677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25568884058157754717998451 38353326087236632076997677)
              ·
                refine ⟨14382497282713737028874129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38353326087236632076997677 14382497282713737028874129)
                ·
                  refine ⟨10786872962035302771655597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14382497282713737028874129 10786872962035302771655597)
                  ·
                    refine ⟨4045077360763238539370849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10786872962035302771655597 4045077360763238539370849)
                    ·
                      refine ⟨3033808020572428904528137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4045077360763238539370849 3033808020572428904528137)
                      ·
                        rfl

theorem cell23_5908320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_5908320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908320 prefixEnd_5908320 := by exact prefixLift 5908320
  have htrace : WordTrace (prefixWord ++ tailWord_5908320) baseStart_5908320 baseEnd_5908320 := by
    simpa [prefixWord, tailWord_5908320, baseEnd_5908320] using wordTrace_append hprefix tailTrace_5908320
  have hstable : (prefixWord ++ tailWord_5908320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908320).length < 2 ^ (prefixWord ++ tailWord_5908320).sum := by decide
  have hdescent : baseEnd_5908320 < baseStart_5908320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908327 : List Nat := [1, 1, 5, 1, 2, 1, 2, 5, 1, 1, 3]
def baseStart_5908327 : Nat := 118140960795 + 5908327 * 2 ^ 59
def prefixEnd_5908327 : Nat := 4983230072969 + 3 ^ 40 * 5908327 * 2
def baseEnd_5908327 : Nat := 3033811614937010377140605

theorem tailTrace_5908327 : CollatzResearch.WordTrace tailWord_5908327 prefixEnd_5908327 3033811614937010377140605 := by
  unfold tailWord_5908327
  simp only [CollatzResearch.WordTrace]
  refine ⟨215494389266147815761187235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143662926177431877174124823 215494389266147815761187235)
  ·
    refine ⟨323241583899221723641780853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215494389266147815761187235 323241583899221723641780853)
    ·
      refine ⟨30303898490552036591416955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 323241583899221723641780853 30303898490552036591416955)
      ·
        refine ⟨45455847735828054887125433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30303898490552036591416955 45455847735828054887125433)
        ·
          refine ⟨34091885801871041165344075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45455847735828054887125433 34091885801871041165344075)
          ·
            refine ⟨51137828702806561748016113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34091885801871041165344075 51137828702806561748016113)
            ·
              refine ⟨38353371527104921311012085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51137828702806561748016113 38353371527104921311012085)
              ·
                refine ⟨3595628580666086372907383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38353371527104921311012085 3595628580666086372907383)
                ·
                  refine ⟨5393442870999129559361075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595628580666086372907383 5393442870999129559361075)
                  ·
                    refine ⟨8090164306498694339041613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5393442870999129559361075 8090164306498694339041613)
                    ·
                      refine ⟨3033811614937010377140605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8090164306498694339041613 3033811614937010377140605)
                      ·
                        rfl

theorem cell23_5908327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_5908327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908327 prefixEnd_5908327 := by exact prefixLift 5908327
  have htrace : WordTrace (prefixWord ++ tailWord_5908327) baseStart_5908327 baseEnd_5908327 := by
    simpa [prefixWord, tailWord_5908327, baseEnd_5908327] using wordTrace_append hprefix tailTrace_5908327
  have hstable : (prefixWord ++ tailWord_5908327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908327).length < 2 ^ (prefixWord ++ tailWord_5908327).sum := by decide
  have hdescent : baseEnd_5908327 < baseStart_5908327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908346 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_5908346 : Nat := 118140960795 + 5908346 * 2 ^ 59
def prefixEnd_5908346 : Nat := 4983230072969 + 3 ^ 40 * 5908346 * 2
def baseEnd_5908346 : Nat := 3033821371069445802803017

theorem tailTrace_5908346 : CollatzResearch.WordTrace tailWord_5908346 prefixEnd_5908346 3033821371069445802803017 := by
  unfold tailWord_5908346
  simp only [CollatzResearch.WordTrace]
  refine ⟨53873770563269745501532223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143663388168719321337419261 53873770563269745501532223)
  ·
    refine ⟨80810655844904618252298335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53873770563269745501532223 80810655844904618252298335)
    ·
      refine ⟨121215983767356927378447503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80810655844904618252298335 121215983767356927378447503)
      ·
        refine ⟨181823975651035391067671255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121215983767356927378447503 181823975651035391067671255)
        ·
          refine ⟨272735963476553086601506883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181823975651035391067671255 272735963476553086601506883)
          ·
            refine ⟨409103945214829629902260325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272735963476553086601506883 409103945214829629902260325)
            ·
              refine ⟨76706989727780555606673811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 409103945214829629902260325 76706989727780555606673811)
              ·
                refine ⟨115060484591670833410010717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76706989727780555606673811 115060484591670833410010717)
                ·
                  refine ⟨43147681721876562528754019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115060484591670833410010717 43147681721876562528754019)
                  ·
                    refine ⟨64721522582814843793131029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43147681721876562528754019 64721522582814843793131029)
                    ·
                      refine ⟨3033821371069445802803017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64721522582814843793131029 3033821371069445802803017)
                      ·
                        rfl

theorem cell23_5908346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_5908346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908346 prefixEnd_5908346 := by exact prefixLift 5908346
  have htrace : WordTrace (prefixWord ++ tailWord_5908346) baseStart_5908346 baseEnd_5908346 := by
    simpa [prefixWord, tailWord_5908346, baseEnd_5908346] using wordTrace_append hprefix tailTrace_5908346
  have hstable : (prefixWord ++ tailWord_5908346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908346).length < 2 ^ (prefixWord ++ tailWord_5908346).sum := by decide
  have hdescent : baseEnd_5908346 < baseStart_5908346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908360 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 1, 6]
def baseStart_5908360 : Nat := 118140960795 + 5908360 * 2 ^ 59
def prefixEnd_5908360 : Nat := 4983230072969 + 3 ^ 40 * 5908360 * 2
def baseEnd_5908360 : Nat := 1011276186599536249342651

theorem tailTrace_5908360 : CollatzResearch.WordTrace tailWord_5908360 prefixEnd_5908360 1011276186599536249342651 := by
  unfold tailWord_5908360
  simp only [CollatzResearch.WordTrace]
  refine ⟨107747796437514131198569267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143663728583352174931425689 107747796437514131198569267)
  ·
    refine ⟨161621694656271196797853901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107747796437514131198569267 161621694656271196797853901)
    ·
      refine ⟨60608135496101698799195213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161621694656271196797853901 60608135496101698799195213)
      ·
        refine ⟨22728050811038137049698205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60608135496101698799195213 22728050811038137049698205)
        ·
          refine ⟨8523019054139301393636827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22728050811038137049698205 8523019054139301393636827)
          ·
            refine ⟨12784528581208952090455241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8523019054139301393636827 12784528581208952090455241)
            ·
              refine ⟨9588396435906714067841431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12784528581208952090455241 9588396435906714067841431)
              ·
                refine ⟨14382594653860071101762147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9588396435906714067841431 14382594653860071101762147)
                ·
                  refine ⟨21573891980790106652643221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14382594653860071101762147 21573891980790106652643221)
                  ·
                    refine ⟨1011276186599536249342651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21573891980790106652643221 1011276186599536249342651)
                    ·
                      rfl

theorem cell23_5908360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_5908360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908360 prefixEnd_5908360 := by exact prefixLift 5908360
  have htrace : WordTrace (prefixWord ++ tailWord_5908360) baseStart_5908360 baseEnd_5908360 := by
    simpa [prefixWord, tailWord_5908360, baseEnd_5908360] using wordTrace_append hprefix tailTrace_5908360
  have hstable : (prefixWord ++ tailWord_5908360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908360).length < 2 ^ (prefixWord ++ tailWord_5908360).sum := by decide
  have hdescent : baseEnd_5908360 < baseStart_5908360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908373 : List Nat := [1, 3, 2, 1, 1, 3, 5, 7]
def baseStart_5908373 : Nat := 118140960795 + 5908373 * 2 ^ 59
def prefixEnd_5908373 : Nat := 4983230072969 + 3 ^ 40 * 5908373 * 2
def baseEnd_5908373 : Nat := 112364267964708044339459

theorem tailTrace_5908373 : CollatzResearch.WordTrace tailWord_5908373 prefixEnd_5908373 112364267964708044339459 := by
  unfold tailWord_5908373
  simp only [CollatzResearch.WordTrace]
  refine ⟨215496067023981165617361773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143664044682654110411574515 215496067023981165617361773)
  ·
    refine ⟨80811025133992937106510665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215496067023981165617361773 80811025133992937106510665)
    ·
      refine ⟨60608268850494702829882999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80811025133992937106510665 60608268850494702829882999)
      ·
        refine ⟨90912403275742054244824499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60608268850494702829882999 90912403275742054244824499)
        ·
          refine ⟨136368604913613081367236749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90912403275742054244824499 136368604913613081367236749)
          ·
            refine ⟨51138226842604905512713781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136368604913613081367236749 51138226842604905512713781)
            ·
              refine ⟨4794208766494209891816917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51138226842604905512713781 4794208766494209891816917)
              ·
                refine ⟨112364267964708044339459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4794208766494209891816917 112364267964708044339459)
                ·
                  rfl

theorem cell23_5908373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 7].length) (baseStart_5908373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908373 prefixEnd_5908373 := by exact prefixLift 5908373
  have htrace : WordTrace (prefixWord ++ tailWord_5908373) baseStart_5908373 baseEnd_5908373 := by
    simpa [prefixWord, tailWord_5908373, baseEnd_5908373] using wordTrace_append hprefix tailTrace_5908373
  have hstable : (prefixWord ++ tailWord_5908373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908373).length < 2 ^ (prefixWord ++ tailWord_5908373).sum := by decide
  have hdescent : baseEnd_5908373 < baseStart_5908373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908380 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_5908380 : Nat := 118140960795 + 5908380 * 2 ^ 59
def prefixEnd_5908380 : Nat := 4983230072969 + 3 ^ 40 * 5908380 * 2
def baseEnd_5908380 : Nat := 3033838829411698669777861

theorem tailTrace_5908380 : CollatzResearch.WordTrace tailWord_5908380 prefixEnd_5908380 3033838829411698669777861 := by
  unfold tailWord_5908380
  simp only [CollatzResearch.WordTrace]
  refine ⟨107748161167477902906433297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143664214889970537208577729 107748161167477902906433297)
  ·
    refine ⟨80811120875608427179824973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107748161167477902906433297 80811120875608427179824973)
    ·
      refine ⟨30304170328353160192434365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80811120875608427179824973 30304170328353160192434365)
      ·
        refine ⟨11364063873132435072162887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30304170328353160192434365 11364063873132435072162887)
        ·
          refine ⟨17046095809698652608244331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11364063873132435072162887 17046095809698652608244331)
          ·
            refine ⟨25569143714547978912366497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17046095809698652608244331 25569143714547978912366497)
            ·
              refine ⟨19176857785910984184274873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25569143714547978912366497 19176857785910984184274873)
              ·
                refine ⟨14382643339433238138206155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19176857785910984184274873 14382643339433238138206155)
                ·
                  refine ⟨21573965009149857207309233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14382643339433238138206155 21573965009149857207309233)
                  ·
                    refine ⟨16180473756862392905481925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21573965009149857207309233 16180473756862392905481925)
                    ·
                      refine ⟨3033838829411698669777861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16180473756862392905481925 3033838829411698669777861)
                      ·
                        rfl

theorem cell23_5908380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_5908380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908380 prefixEnd_5908380 := by exact prefixLift 5908380
  have htrace : WordTrace (prefixWord ++ tailWord_5908380) baseStart_5908380 baseEnd_5908380 := by
    simpa [prefixWord, tailWord_5908380, baseEnd_5908380] using wordTrace_append hprefix tailTrace_5908380
  have hstable : (prefixWord ++ tailWord_5908380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908380).length < 2 ^ (prefixWord ++ tailWord_5908380).sum := by decide
  have hdescent : baseEnd_5908380 < baseStart_5908380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908396 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_5908396 : Nat := 118140960795 + 5908396 * 2 ^ 59
def prefixEnd_5908396 : Nat := 4983230072969 + 3 ^ 40 * 5908396 * 2
def baseEnd_5908396 : Nat := 3033847045102170607177787

theorem tailTrace_5908396 : CollatzResearch.WordTrace tailWord_5908396 prefixEnd_5908396 3033847045102170607177787 := by
  unfold tailWord_5908396
  simp only [CollatzResearch.WordTrace]
  refine ⟨107748452951448920272724521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143664603935265227030299361 107748452951448920272724521)
  ·
    refine ⟨80811339713586690204543391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107748452951448920272724521 80811339713586690204543391)
    ·
      refine ⟨121217009570380035306815087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80811339713586690204543391 121217009570380035306815087)
      ·
        refine ⟨181825514355570052960222631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121217009570380035306815087 181825514355570052960222631)
        ·
          refine ⟨272738271533355079440333947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181825514355570052960222631 272738271533355079440333947)
          ·
            refine ⟨409107407300032619160500921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272738271533355079440333947 409107407300032619160500921)
            ·
              refine ⟨306830555475024464370375691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409107407300032619160500921 306830555475024464370375691)
              ·
                refine ⟨460245833212536696555563537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306830555475024464370375691 460245833212536696555563537)
                ·
                  refine ⟨345184374909402522416672653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460245833212536696555563537 345184374909402522416672653)
                  ·
                    refine ⟨129444140591025945906252245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 345184374909402522416672653 129444140591025945906252245)
                    ·
                      refine ⟨3033847045102170607177787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129444140591025945906252245 3033847045102170607177787)
                      ·
                        rfl

theorem cell23_5908396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_5908396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908396 prefixEnd_5908396 := by exact prefixLift 5908396
  have htrace : WordTrace (prefixWord ++ tailWord_5908396) baseStart_5908396 baseEnd_5908396 := by
    simpa [prefixWord, tailWord_5908396, baseEnd_5908396] using wordTrace_append hprefix tailTrace_5908396
  have hstable : (prefixWord ++ tailWord_5908396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908396).length < 2 ^ (prefixWord ++ tailWord_5908396).sum := by decide
  have hdescent : baseEnd_5908396 < baseStart_5908396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908410 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2]
def baseStart_5908410 : Nat := 118140960795 + 5908410 * 2 ^ 59
def prefixEnd_5908410 : Nat := 4983230072969 + 3 ^ 40 * 5908410 * 2
def baseEnd_5908410 : Nat := 3033854233831333552402723

theorem tailTrace_5908410 : CollatzResearch.WordTrace tailWord_5908410 prefixEnd_5908410 3033854233831333552402723 := by
  unfold tailWord_5908410
  simp only [CollatzResearch.WordTrace]
  refine ⟨53874354131211780234114671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143664944349898080624305789 53874354131211780234114671)
  ·
    refine ⟨80811531196817670351172007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53874354131211780234114671 80811531196817670351172007)
    ·
      refine ⟨121217296795226505526758011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80811531196817670351172007 121217296795226505526758011)
      ·
        refine ⟨181825945192839758290137017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121217296795226505526758011 181825945192839758290137017)
        ·
          refine ⟨136369458894629818717602763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181825945192839758290137017 136369458894629818717602763)
          ·
            refine ⟨204554188341944728076404145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136369458894629818717602763 204554188341944728076404145)
            ·
              refine ⟨153415641256458546057303109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204554188341944728076404145 153415641256458546057303109)
              ·
                refine ⟨28765432735585977385744333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153415641256458546057303109 28765432735585977385744333)
                ·
                  refine ⟨10787037275844741519654125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28765432735585977385744333 10787037275844741519654125)
                  ·
                    refine ⟨4045138978441778069870297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10787037275844741519654125 4045138978441778069870297)
                    ·
                      refine ⟨3033854233831333552402723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4045138978441778069870297 3033854233831333552402723)
                      ·
                        rfl

theorem cell23_5908410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2].length) (baseStart_5908410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908410 prefixEnd_5908410 := by exact prefixLift 5908410
  have htrace : WordTrace (prefixWord ++ tailWord_5908410) baseStart_5908410 baseEnd_5908410 := by
    simpa [prefixWord, tailWord_5908410, baseEnd_5908410] using wordTrace_append hprefix tailTrace_5908410
  have hstable : (prefixWord ++ tailWord_5908410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908410).length < 2 ^ (prefixWord ++ tailWord_5908410).sum := by decide
  have hdescent : baseEnd_5908410 < baseStart_5908410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908427 : List Nat := [1, 1, 1, 1, 3, 4, 4, 2, 1, 3, 2]
def baseStart_5908427 : Nat := 118140960795 + 5908427 * 2 ^ 59
def prefixEnd_5908427 : Nat := 4983230072969 + 3 ^ 40 * 5908427 * 2
def baseEnd_5908427 : Nat := 3033862963002459985890145

theorem tailTrace_5908427 : CollatzResearch.WordTrace tailWord_5908427 prefixEnd_5908427 3033862963002459985890145 := by
  unfold tailWord_5908427
  simp only [CollatzResearch.WordTrace]
  refine ⟨215498036565785532839827535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143665357710523688559885023 215498036565785532839827535)
  ·
    refine ⟨323247054848678299259741303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215498036565785532839827535 323247054848678299259741303)
    ·
      refine ⟨484870582273017448889611955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323247054848678299259741303 484870582273017448889611955)
      ·
        refine ⟨727305873409526173334417933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484870582273017448889611955 727305873409526173334417933)
        ·
          refine ⟨272739702528572315000406725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 727305873409526173334417933 272739702528572315000406725)
          ·
            refine ⟨51138694224107309062576261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 272739702528572315000406725 51138694224107309062576261)
            ·
              refine ⟨9588505167020120449233049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51138694224107309062576261 9588505167020120449233049)
              ·
                refine ⟨7191378875265090336924787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9588505167020120449233049 7191378875265090336924787)
                ·
                  refine ⟨10787068312897635505387181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7191378875265090336924787 10787068312897635505387181)
                  ·
                    refine ⟨4045150617336613314520193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10787068312897635505387181 4045150617336613314520193)
                    ·
                      refine ⟨3033862963002459985890145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4045150617336613314520193 3033862963002459985890145)
                      ·
                        rfl

theorem cell23_5908427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 3, 2].length) (baseStart_5908427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908427 prefixEnd_5908427 := by exact prefixLift 5908427
  have htrace : WordTrace (prefixWord ++ tailWord_5908427) baseStart_5908427 baseEnd_5908427 := by
    simpa [prefixWord, tailWord_5908427, baseEnd_5908427] using wordTrace_append hprefix tailTrace_5908427
  have hstable : (prefixWord ++ tailWord_5908427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908427).length < 2 ^ (prefixWord ++ tailWord_5908427).sum := by decide
  have hdescent : baseEnd_5908427 < baseStart_5908427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908440 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 3, 4, 2]
def baseStart_5908440 : Nat := 118140960795 + 5908440 * 2 ^ 59
def prefixEnd_5908440 : Nat := 4983230072969 + 3 ^ 40 * 5908440 * 2
def baseEnd_5908440 : Nat := 3033869638250968435027585

theorem tailTrace_5908440 : CollatzResearch.WordTrace tailWord_5908440 prefixEnd_5908440 3033869638250968435027585 := by
  unfold tailWord_5908440
  simp only [CollatzResearch.WordTrace]
  refine ⟨107749255357369218030025387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143665673809825624040033849 107749255357369218030025387)
  ·
    refine ⟨161623883036053827045038081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107749255357369218030025387 161623883036053827045038081)
    ·
      refine ⟨121217912277040370283778561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161623883036053827045038081 121217912277040370283778561)
      ·
        refine ⟨90913434207780277712833921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121217912277040370283778561 90913434207780277712833921)
        ·
          refine ⟨68185075655835208284625441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90913434207780277712833921 68185075655835208284625441)
          ·
            refine ⟨51138806741876406213469081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68185075655835208284625441 51138806741876406213469081)
            ·
              refine ⟨38354105056407304660101811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51138806741876406213469081 38354105056407304660101811)
              ·
                refine ⟨57531157584610956990152717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38354105056407304660101811 57531157584610956990152717)
                ·
                  refine ⟨21574184094229108871307269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57531157584610956990152717 21574184094229108871307269)
                  ·
                    refine ⟨4045159517667957913370113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21574184094229108871307269 4045159517667957913370113)
                    ·
                      refine ⟨3033869638250968435027585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4045159517667957913370113 3033869638250968435027585)
                      ·
                        rfl

theorem cell23_5908440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_5908440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908440 prefixEnd_5908440 := by exact prefixLift 5908440
  have htrace : WordTrace (prefixWord ++ tailWord_5908440) baseStart_5908440 baseEnd_5908440 := by
    simpa [prefixWord, tailWord_5908440, baseEnd_5908440] using wordTrace_append hprefix tailTrace_5908440
  have hstable : (prefixWord ++ tailWord_5908440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908440).length < 2 ^ (prefixWord ++ tailWord_5908440).sum := by decide
  have hdescent : baseEnd_5908440 < baseStart_5908440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908553 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 8]
def baseStart_5908553 : Nat := 118140960795 + 5908553 * 2 ^ 59
def prefixEnd_5908553 : Nat := 4983230072969 + 3 ^ 40 * 5908553 * 2
def baseEnd_5908553 : Nat := 337103073507214054768285

theorem tailTrace_5908553 : CollatzResearch.WordTrace tailWord_5908553 prefixEnd_5908553 337103073507214054768285 := by
  unfold tailWord_5908553
  simp only [CollatzResearch.WordTrace]
  refine ⟨215502632163329056358914313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143668421442219370905942875 215502632163329056358914313)
  ·
    refine ⟨161626974122496792269185735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215502632163329056358914313 161626974122496792269185735)
    ·
      refine ⟨242440461183745188403778603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161626974122496792269185735 242440461183745188403778603)
      ·
        refine ⟨363660691775617782605667905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242440461183745188403778603 363660691775617782605667905)
        ·
          refine ⟨272745518831713336954250929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363660691775617782605667905 272745518831713336954250929)
          ·
            refine ⟨204559139123785002715688197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272745518831713336954250929 204559139123785002715688197)
            ·
              refine ⟨38354838585709688009191537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204559139123785002715688197 38354838585709688009191537)
              ·
                refine ⟨28766128939282266006893653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38354838585709688009191537 28766128939282266006893653)
                ·
                  refine ⟨337103073507214054768285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28766128939282266006893653 337103073507214054768285)
                  ·
                    rfl

theorem cell23_5908553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 8].length) (baseStart_5908553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908553 prefixEnd_5908553 := by exact prefixLift 5908553
  have htrace : WordTrace (prefixWord ++ tailWord_5908553) baseStart_5908553 baseEnd_5908553 := by
    simpa [prefixWord, tailWord_5908553, baseEnd_5908553] using wordTrace_append hprefix tailTrace_5908553
  have hstable : (prefixWord ++ tailWord_5908553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908553).length < 2 ^ (prefixWord ++ tailWord_5908553).sum := by decide
  have hdescent : baseEnd_5908553 < baseStart_5908553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908557 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_5908557 : Nat := 118140960795 + 5908557 * 2 ^ 59
def prefixEnd_5908557 : Nat := 4983230072969 + 3 ^ 40 * 5908557 * 2
def baseEnd_5908557 : Nat := 1011309905162514825754849

theorem tailTrace_5908557 : CollatzResearch.WordTrace tailWord_5908557 prefixEnd_5908557 1011309905162514825754849 := by
  unfold tailWord_5908557
  simp only [CollatzResearch.WordTrace]
  refine ⟨215502778055314565042059925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143668518703543043361373283 215502778055314565042059925)
  ·
    refine ⟨10101692721342870236346559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 215502778055314565042059925 10101692721342870236346559)
    ·
      refine ⟨15152539082014305354519839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10101692721342870236346559 15152539082014305354519839)
      ·
        refine ⟨22728808623021458031779759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15152539082014305354519839 22728808623021458031779759)
        ·
          refine ⟨34093212934532187047669639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22728808623021458031779759 34093212934532187047669639)
          ·
            refine ⟨51139819401798280571504459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34093212934532187047669639 51139819401798280571504459)
            ·
              refine ⟨76709729102697420857256689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51139819401798280571504459 76709729102697420857256689)
              ·
                refine ⟨57532296827023065642942517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76709729102697420857256689 57532296827023065642942517)
                ·
                  refine ⟨5393652827533412404025861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57532296827023065642942517 5393652827533412404025861)
                  ·
                    refine ⟨1011309905162514825754849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5393652827533412404025861 1011309905162514825754849)
                    ·
                      rfl

theorem cell23_5908557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_5908557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908557 prefixEnd_5908557 := by exact prefixLift 5908557
  have htrace : WordTrace (prefixWord ++ tailWord_5908557) baseStart_5908557 baseEnd_5908557 := by
    simpa [prefixWord, tailWord_5908557, baseEnd_5908557] using wordTrace_append hprefix tailTrace_5908557
  have hstable : (prefixWord ++ tailWord_5908557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908557).length < 2 ^ (prefixWord ++ tailWord_5908557).sum := by decide
  have hdescent : baseEnd_5908557 < baseStart_5908557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908590 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_5908590 : Nat := 118140960795 + 5908590 * 2 ^ 59
def prefixEnd_5908590 : Nat := 4983230072969 + 3 ^ 40 * 5908590 * 2
def baseEnd_5908590 : Nat := 3033946660349142848151895

theorem tailTrace_5908590 : CollatzResearch.WordTrace tailWord_5908590 prefixEnd_5908590 3033946660349142848151895 := by
  unfold tailWord_5908590
  simp only [CollatzResearch.WordTrace]
  refine ⟨26937997708024376459751403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143669321109463341118674149 26937997708024376459751403)
  ·
    refine ⟨40406996562036564689627105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26937997708024376459751403 40406996562036564689627105)
    ·
      refine ⟨30305247421527423517220329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40406996562036564689627105 30305247421527423517220329)
      ·
        refine ⟨22728935566145567637915247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30305247421527423517220329 22728935566145567637915247)
        ·
          refine ⟨34093403349218351456872871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22728935566145567637915247 34093403349218351456872871)
          ·
            refine ⟨51140105023827527185309307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34093403349218351456872871 51140105023827527185309307)
            ·
              refine ⟨76710157535741290777963961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51140105023827527185309307 76710157535741290777963961)
              ·
                refine ⟨57532618151805968083472971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76710157535741290777963961 57532618151805968083472971)
                ·
                  refine ⟨86298927227708952125209457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57532618151805968083472971 86298927227708952125209457)
                  ·
                    refine ⟨64724195420781714093907093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86298927227708952125209457 64724195420781714093907093)
                    ·
                      refine ⟨3033946660349142848151895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64724195420781714093907093 3033946660349142848151895)
                      ·
                        rfl

theorem cell23_5908590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_5908590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908590 prefixEnd_5908590 := by exact prefixLift 5908590
  have htrace : WordTrace (prefixWord ++ tailWord_5908590) baseStart_5908590 baseEnd_5908590 := by
    simpa [prefixWord, tailWord_5908590, baseEnd_5908590] using wordTrace_append hprefix tailTrace_5908590
  have hstable : (prefixWord ++ tailWord_5908590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908590).length < 2 ^ (prefixWord ++ tailWord_5908590).sum := by decide
  have hdescent : baseEnd_5908590 < baseStart_5908590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908620 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 7, 1, 4]
def baseStart_5908620 : Nat := 118140960795 + 5908620 * 2 ^ 59
def prefixEnd_5908620 : Nat := 4983230072969 + 3 ^ 40 * 5908620 * 2
def baseEnd_5908620 : Nat := 3033962064768777730776757

theorem tailTrace_5908620 : CollatzResearch.WordTrace tailWord_5908620 prefixEnd_5908620 3033962064768777730776757 := by
  unfold tailWord_5908620
  simp only [CollatzResearch.WordTrace]
  refine ⟨107752537927043163400801657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143670050569390884534402209 107752537927043163400801657)
  ·
    refine ⟨80814403445282372550601243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107752537927043163400801657 80814403445282372550601243)
    ·
      refine ⟨121221605167923558825901865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80814403445282372550601243 121221605167923558825901865)
      ·
        refine ⟨90916203875942669119426399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121221605167923558825901865 90916203875942669119426399)
        ·
          refine ⟨136374305813914003679139599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90916203875942669119426399 136374305813914003679139599)
          ·
            refine ⟨204561458720871005518709399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136374305813914003679139599 204561458720871005518709399)
            ·
              refine ⟨306842188081306508278064099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204561458720871005518709399 306842188081306508278064099)
              ·
                refine ⟨460263282121959762417096149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306842188081306508278064099 460263282121959762417096149)
                ·
                  refine ⟨10787420674733431931650691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 460263282121959762417096149 10787420674733431931650691)
                  ·
                    refine ⟨16181131012100147897476037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10787420674733431931650691 16181131012100147897476037)
                    ·
                      refine ⟨3033962064768777730776757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16181131012100147897476037 3033962064768777730776757)
                      ·
                        rfl

theorem cell23_5908620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_5908620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908620 prefixEnd_5908620 := by exact prefixLift 5908620
  have htrace : WordTrace (prefixWord ++ tailWord_5908620) baseStart_5908620 baseEnd_5908620 := by
    simpa [prefixWord, tailWord_5908620, baseEnd_5908620] using wordTrace_append hprefix tailTrace_5908620
  have hstable : (prefixWord ++ tailWord_5908620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908620).length < 2 ^ (prefixWord ++ tailWord_5908620).sum := by decide
  have hdescent : baseEnd_5908620 < baseStart_5908620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908631 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 3, 1, 3]
def baseStart_5908631 : Nat := 118140960795 + 5908631 * 2 ^ 59
def prefixEnd_5908631 : Nat := 4983230072969 + 3 ^ 40 * 5908631 * 2
def baseEnd_5908631 : Nat := 3033967713055977187739207

theorem tailTrace_5908631 : CollatzResearch.WordTrace tailWord_5908631 prefixEnd_5908631 3033967713055977187739207 := by
  unfold tailWord_5908631
  simp only [CollatzResearch.WordTrace]
  refine ⟨215505477057046475680253747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143670318038030983786835831 215505477057046475680253747)
  ·
    refine ⟨323258215585569713520380621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215505477057046475680253747 323258215585569713520380621)
    ·
      refine ⟨121221830844588642570142733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323258215585569713520380621 121221830844588642570142733)
      ·
        refine ⟨45458186566720740963803525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121221830844588642570142733 45458186566720740963803525)
        ·
          refine ⟨8523409981260138930713161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45458186566720740963803525 8523409981260138930713161)
          ·
            refine ⟨6392557485945104198034871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8523409981260138930713161 6392557485945104198034871)
            ·
              refine ⟨9588836228917656297052307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6392557485945104198034871 9588836228917656297052307)
              ·
                refine ⟨14383254343376484445578461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9588836228917656297052307 14383254343376484445578461)
                ·
                  refine ⟨5393720378766181667091923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14383254343376484445578461 5393720378766181667091923)
                  ·
                    refine ⟨8090580568149272500637885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5393720378766181667091923 8090580568149272500637885)
                    ·
                      refine ⟨3033967713055977187739207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8090580568149272500637885 3033967713055977187739207)
                      ·
                        rfl

theorem cell23_5908631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_5908631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908631 prefixEnd_5908631 := by exact prefixLift 5908631
  have htrace : WordTrace (prefixWord ++ tailWord_5908631) baseStart_5908631 baseEnd_5908631 := by
    simpa [prefixWord, tailWord_5908631, baseEnd_5908631] using wordTrace_append hprefix tailTrace_5908631
  have hstable : (prefixWord ++ tailWord_5908631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908631).length < 2 ^ (prefixWord ++ tailWord_5908631).sum := by decide
  have hdescent : baseEnd_5908631 < baseStart_5908631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908638 : List Nat := [4, 3, 1, 1, 4, 1, 2, 1, 6]
def baseStart_5908638 : Nat := 118140960795 + 5908638 * 2 ^ 59
def prefixEnd_5908638 : Nat := 4983230072969 + 3 ^ 40 * 5908638 * 2
def baseEnd_5908638 : Nat := 337107923046728740039075

theorem tailTrace_5908638 : CollatzResearch.WordTrace tailWord_5908638 prefixEnd_5908638 337107923046728740039075 := by
  unfold tailWord_5908638
  simp only [CollatzResearch.WordTrace]
  refine ⟨26938216546002639484469821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143670488245347410583839045 26938216546002639484469821)
  ·
    refine ⟨10101831204750989806676183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26938216546002639484469821 10101831204750989806676183)
    ·
      refine ⟨15152746807126484710014275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10101831204750989806676183 15152746807126484710014275)
      ·
        refine ⟨22729120210689727065021413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15152746807126484710014275 22729120210689727065021413)
        ·
          refine ⟨4261710039504323824691515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22729120210689727065021413 4261710039504323824691515)
          ·
            refine ⟨6392565059256485737037273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4261710039504323824691515 6392565059256485737037273)
            ·
              refine ⟨4794423794442364302777955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6392565059256485737037273 4794423794442364302777955)
              ·
                refine ⟨7191635691663546454166933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4794423794442364302777955 7191635691663546454166933)
                ·
                  refine ⟨337107923046728740039075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7191635691663546454166933 337107923046728740039075)
                  ·
                    rfl

theorem cell23_5908638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_5908638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908638 prefixEnd_5908638 := by exact prefixLift 5908638
  have htrace : WordTrace (prefixWord ++ tailWord_5908638) baseStart_5908638 baseEnd_5908638 := by
    simpa [prefixWord, tailWord_5908638, baseEnd_5908638] using wordTrace_append hprefix tailTrace_5908638
  have hstable : (prefixWord ++ tailWord_5908638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908638).length < 2 ^ (prefixWord ++ tailWord_5908638).sum := by decide
  have hdescent : baseEnd_5908638 < baseStart_5908638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908671 : List Nat := [1, 1, 2, 2, 2, 2, 1, 7, 1, 2, 2]
def baseStart_5908671 : Nat := 118140960795 + 5908671 * 2 ^ 59
def prefixEnd_5908671 : Nat := 4983230072969 + 3 ^ 40 * 5908671 * 2
def baseEnd_5908671 : Nat := 3033988252282157031239023

theorem tailTrace_5908671 : CollatzResearch.WordTrace tailWord_5908671 prefixEnd_5908671 3033988252282157031239023 := by
  unfold tailWord_5908671
  simp only [CollatzResearch.WordTrace]
  refine ⟨215506935976901562511709867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143671290651267708341139911 215506935976901562511709867)
  ·
    refine ⟨323260403965352343767564801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215506935976901562511709867 323260403965352343767564801)
    ·
      refine ⟨242445302974014257825673601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323260403965352343767564801 242445302974014257825673601)
      ·
        refine ⟨181833977230510693369255201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242445302974014257825673601 181833977230510693369255201)
        ·
          refine ⟨136375482922883020026941401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181833977230510693369255201 136375482922883020026941401)
          ·
            refine ⟨102281612192162265020206051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136375482922883020026941401 102281612192162265020206051)
            ·
              refine ⟨153422418288243397530309077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102281612192162265020206051 153422418288243397530309077)
              ·
                refine ⟨3595837928630704629616619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 153422418288243397530309077 3595837928630704629616619)
                ·
                  refine ⟨5393756892946056944424929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595837928630704629616619 5393756892946056944424929)
                  ·
                    refine ⟨4045317669709542708318697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5393756892946056944424929 4045317669709542708318697)
                    ·
                      refine ⟨3033988252282157031239023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4045317669709542708318697 3033988252282157031239023)
                      ·
                        rfl

theorem cell23_5908671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 1, 2, 2].length) (baseStart_5908671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908671 prefixEnd_5908671 := by exact prefixLift 5908671
  have htrace : WordTrace (prefixWord ++ tailWord_5908671) baseStart_5908671 baseEnd_5908671 := by
    simpa [prefixWord, tailWord_5908671, baseEnd_5908671] using wordTrace_append hprefix tailTrace_5908671
  have hstable : (prefixWord ++ tailWord_5908671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908671).length < 2 ^ (prefixWord ++ tailWord_5908671).sum := by decide
  have hdescent : baseEnd_5908671 < baseStart_5908671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908694 : List Nat := [5, 2, 1, 2, 1, 1, 3, 8]
def baseStart_5908694 : Nat := 118140960795 + 5908694 * 2 ^ 59
def prefixEnd_5908694 : Nat := 4983230072969 + 3 ^ 40 * 5908694 * 2
def baseEnd_5908694 : Nat := 112370372679155942268571

theorem tailTrace_5908694 : CollatzResearch.WordTrace tailWord_5908694 prefixEnd_5908694 112370372679155942268571 := by
  unfold tailWord_5908694
  simp only [CollatzResearch.WordTrace]
  refine ⟨13469235928488639839987321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143671849903878824959864757 13469235928488639839987321)
  ·
    refine ⟨10101926946366479879990491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13469235928488639839987321 10101926946366479879990491)
    ·
      refine ⟨15152890419549719819985737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10101926946366479879990491 15152890419549719819985737)
      ·
        refine ⟨11364667814662289864989303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15152890419549719819985737 11364667814662289864989303)
        ·
          refine ⟨17047001721993434797483955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11364667814662289864989303 17047001721993434797483955)
          ·
            refine ⟨25570502582990152196225933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17047001721993434797483955 25570502582990152196225933)
            ·
              refine ⟨9588938468621307073584725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25570502582990152196225933 9588938468621307073584725)
              ·
                refine ⟨112370372679155942268571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9588938468621307073584725 112370372679155942268571)
                ·
                  rfl

theorem cell23_5908694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_5908694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908694 prefixEnd_5908694 := by exact prefixLift 5908694
  have htrace : WordTrace (prefixWord ++ tailWord_5908694) baseStart_5908694 baseEnd_5908694 := by
    simpa [prefixWord, tailWord_5908694, baseEnd_5908694] using wordTrace_append hprefix tailTrace_5908694
  have hstable : (prefixWord ++ tailWord_5908694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908694).length < 2 ^ (prefixWord ++ tailWord_5908694).sum := by decide
  have hdescent : baseEnd_5908694 < baseStart_5908694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908704 : List Nat := [2, 1, 1, 3, 1, 3, 1, 5, 2, 1, 3]
def baseStart_5908704 : Nat := 118140960795 + 5908704 * 2 ^ 59
def prefixEnd_5908704 : Nat := 4983230072969 + 3 ^ 40 * 5908704 * 2
def baseEnd_5908704 : Nat := 3034005197143755402126371

theorem tailTrace_5908704 : CollatzResearch.WordTrace tailWord_5908704 prefixEnd_5908704 3034005197143755402126371 := by
  unfold tailWord_5908704
  simp only [CollatzResearch.WordTrace]
  refine ⟨107754069792891004573830583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143672093057188006098440777 107754069792891004573830583)
  ·
    refine ⟨161631104689336506860745875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107754069792891004573830583 161631104689336506860745875)
    ·
      refine ⟨242446657034004760291118813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161631104689336506860745875 242446657034004760291118813)
      ·
        refine ⟨90917496387751785109169555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242446657034004760291118813 90917496387751785109169555)
        ·
          refine ⟨136376244581627677663754333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90917496387751785109169555 136376244581627677663754333)
          ·
            refine ⟨51141091718110379123907875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136376244581627677663754333 51141091718110379123907875)
            ·
              refine ⟨76711637577165568685861813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51141091718110379123907875 76711637577165568685861813)
              ·
                refine ⟨7191716022859272064299545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76711637577165568685861813 7191716022859272064299545)
                ·
                  refine ⟨5393787017144454048224659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7191716022859272064299545 5393787017144454048224659)
                  ·
                    refine ⟨8090680525716681072336989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5393787017144454048224659 8090680525716681072336989)
                    ·
                      refine ⟨3034005197143755402126371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8090680525716681072336989 3034005197143755402126371)
                      ·
                        rfl

theorem cell23_5908704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_5908704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908704 prefixEnd_5908704 := by exact prefixLift 5908704
  have htrace : WordTrace (prefixWord ++ tailWord_5908704) baseStart_5908704 baseEnd_5908704 := by
    simpa [prefixWord, tailWord_5908704, baseEnd_5908704] using wordTrace_append hprefix tailTrace_5908704
  have hstable : (prefixWord ++ tailWord_5908704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908704).length < 2 ^ (prefixWord ++ tailWord_5908704).sum := by decide
  have hdescent : baseEnd_5908704 < baseStart_5908704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908714 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 3, 3, 2]
def baseStart_5908714 : Nat := 118140960795 + 5908714 * 2 ^ 59
def prefixEnd_5908714 : Nat := 4983230072969 + 3 ^ 40 * 5908714 * 2
def baseEnd_5908714 : Nat := 3034010331950300363001325

theorem tailTrace_5908714 : CollatzResearch.WordTrace tailWord_5908714 prefixEnd_5908714 3034010331950300363001325 := by
  unfold tailWord_5908714
  simp only [CollatzResearch.WordTrace]
  refine ⟨53877126078936445213881299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143672336210497187237016797 53877126078936445213881299)
  ·
    refine ⟨80815689118404667820821949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53877126078936445213881299 80815689118404667820821949)
    ·
      refine ⟨30305883419401750432808231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80815689118404667820821949 30305883419401750432808231)
      ·
        refine ⟨45458825129102625649212347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30305883419401750432808231 45458825129102625649212347)
        ·
          refine ⟨68188237693653938473818521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45458825129102625649212347 68188237693653938473818521)
          ·
            refine ⟨51141178270240453855363891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68188237693653938473818521 51141178270240453855363891)
            ·
              refine ⟨76711767405360680783045837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51141178270240453855363891 76711767405360680783045837)
              ·
                refine ⟨28766912777010255293642189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76711767405360680783045837 28766912777010255293642189)
                ·
                  refine ⟨10787592291378845735115821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28766912777010255293642189 10787592291378845735115821)
                  ·
                    refine ⟨4045347109267067150668433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10787592291378845735115821 4045347109267067150668433)
                    ·
                      refine ⟨3034010331950300363001325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4045347109267067150668433 3034010331950300363001325)
                      ·
                        rfl

theorem cell23_5908714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_5908714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908714 prefixEnd_5908714 := by exact prefixLift 5908714
  have htrace : WordTrace (prefixWord ++ tailWord_5908714) baseStart_5908714 baseEnd_5908714 := by
    simpa [prefixWord, tailWord_5908714, baseEnd_5908714] using wordTrace_append hprefix tailTrace_5908714
  have hstable : (prefixWord ++ tailWord_5908714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908714).length < 2 ^ (prefixWord ++ tailWord_5908714).sum := by decide
  have hdescent : baseEnd_5908714 < baseStart_5908714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908738 : List Nat := [3, 4, 1, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_5908738 : Nat := 118140960795 + 5908738 * 2 ^ 59
def prefixEnd_5908738 : Nat := 4983230072969 + 3 ^ 40 * 5908738 * 2
def baseEnd_5908738 : Nat := 3034022655486008269101215

theorem tailTrace_5908738 : CollatzResearch.WordTrace tailWord_5908738 prefixEnd_5908738 3034022655486008269101215 := by
  unfold tailWord_5908738
  simp only [CollatzResearch.WordTrace]
  refine ⟨53877344916914708238599717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143672919778439221969599245 53877344916914708238599717)
  ·
    refine ⟨10102002171921507794737447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53877344916914708238599717 10102002171921507794737447)
    ·
      refine ⟨15153003257882261692106171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10102002171921507794737447 15153003257882261692106171)
      ·
        refine ⟨22729504886823392538159257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15153003257882261692106171 22729504886823392538159257)
        ·
          refine ⟨17047128665117544403619443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22729504886823392538159257 17047128665117544403619443)
          ·
            refine ⟨25570692997676316605429165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17047128665117544403619443 25570692997676316605429165)
            ·
              refine ⟨9589009874128618727035937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25570692997676316605429165 9589009874128618727035937)
              ·
                refine ⟨7191757405596464045276953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9589009874128618727035937 7191757405596464045276953)
                ·
                  refine ⟨5393818054197348033957715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7191757405596464045276953 5393818054197348033957715)
                  ·
                    refine ⟨8090727081296022050936573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5393818054197348033957715 8090727081296022050936573)
                    ·
                      refine ⟨3034022655486008269101215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8090727081296022050936573 3034022655486008269101215)
                      ·
                        rfl

theorem cell23_5908738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_5908738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908738 prefixEnd_5908738 := by exact prefixLift 5908738
  have htrace : WordTrace (prefixWord ++ tailWord_5908738) baseStart_5908738 baseEnd_5908738 := by
    simpa [prefixWord, tailWord_5908738, baseEnd_5908738] using wordTrace_append hprefix tailTrace_5908738
  have hstable : (prefixWord ++ tailWord_5908738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908738).length < 2 ^ (prefixWord ++ tailWord_5908738).sum := by decide
  have hdescent : baseEnd_5908738 < baseStart_5908738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908757 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_5908757 : Nat := 118140960795 + 5908757 * 2 ^ 59
def prefixEnd_5908757 : Nat := 4983230072969 + 3 ^ 40 * 5908757 * 2
def baseEnd_5908757 : Nat := 3034032411618443694763627

theorem tailTrace_5908757 : CollatzResearch.WordTrace tailWord_5908757 prefixEnd_5908757 3034032411618443694763627 := by
  unfold tailWord_5908757
  simp only [CollatzResearch.WordTrace]
  refine ⟨215510072654589999199340525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143673381769726666132893683 215510072654589999199340525)
  ·
    refine ⟨80816277245471249699752697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215510072654589999199340525 80816277245471249699752697)
    ·
      refine ⟨60612207934103437274814523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80816277245471249699752697 60612207934103437274814523)
      ·
        refine ⟨90918311901155155912221785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60612207934103437274814523 90918311901155155912221785)
        ·
          refine ⟨68188733925866366934166339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90918311901155155912221785 68188733925866366934166339)
          ·
            refine ⟨102283100888799550401249509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68188733925866366934166339 102283100888799550401249509)
            ·
              refine ⟨19178081416649915700234283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102283100888799550401249509 19178081416649915700234283)
              ·
                refine ⟨28767122124974873550351425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19178081416649915700234283 28767122124974873550351425)
                ·
                  refine ⟨21575341593731155162763569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28767122124974873550351425 21575341593731155162763569)
                  ·
                    refine ⟨16181506195298366372072677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21575341593731155162763569 16181506195298366372072677)
                    ·
                      refine ⟨3034032411618443694763627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16181506195298366372072677 3034032411618443694763627)
                      ·
                        rfl

theorem cell23_5908757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_5908757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908757 prefixEnd_5908757 := by exact prefixLift 5908757
  have htrace : WordTrace (prefixWord ++ tailWord_5908757) baseStart_5908757 baseEnd_5908757 := by
    simpa [prefixWord, tailWord_5908757, baseEnd_5908757] using wordTrace_append hprefix tailTrace_5908757
  have hstable : (prefixWord ++ tailWord_5908757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908757).length < 2 ^ (prefixWord ++ tailWord_5908757).sum := by decide
  have hdescent : baseEnd_5908757 < baseStart_5908757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908767 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 7]
def baseStart_5908767 : Nat := 118140960795 + 5908767 * 2 ^ 59
def prefixEnd_5908767 : Nat := 4983230072969 + 3 ^ 40 * 5908767 * 2
def baseEnd_5908767 : Nat := 337115282936109850626509

theorem tailTrace_5908767 : CollatzResearch.WordTrace tailWord_5908767 prefixEnd_5908767 337115282936109850626509 := by
  unfold tailWord_5908767
  simp only [CollatzResearch.WordTrace]
  refine ⟨215510437384553770907204555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143673624923035847271469703 215510437384553770907204555)
  ·
    refine ⟨323265656076830656360806833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215510437384553770907204555 323265656076830656360806833)
    ·
      refine ⟨242449242057622992270605125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323265656076830656360806833 242449242057622992270605125)
      ·
        refine ⟨45459232885804311050738461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242449242057622992270605125 45459232885804311050738461)
        ·
          refine ⟨17047212332176616644026923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45459232885804311050738461 17047212332176616644026923)
          ·
            refine ⟨25570818498264924966040385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17047212332176616644026923 25570818498264924966040385)
            ·
              refine ⟨19178113873698693724530289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25570818498264924966040385 19178113873698693724530289)
              ·
                refine ⟨14383585405274020293397717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19178113873698693724530289 14383585405274020293397717)
                ·
                  refine ⟨337115282936109850626509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14383585405274020293397717 337115282936109850626509)
                  ·
                    rfl

theorem cell23_5908767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 7].length) (baseStart_5908767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908767 prefixEnd_5908767 := by exact prefixLift 5908767
  have htrace : WordTrace (prefixWord ++ tailWord_5908767) baseStart_5908767 baseEnd_5908767 := by
    simpa [prefixWord, tailWord_5908767, baseEnd_5908767] using wordTrace_append hprefix tailTrace_5908767
  have hstable : (prefixWord ++ tailWord_5908767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908767).length < 2 ^ (prefixWord ++ tailWord_5908767).sum := by decide
  have hdescent : baseEnd_5908767 < baseStart_5908767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908781 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_5908781 : Nat := 118140960795 + 5908781 * 2 ^ 59
def prefixEnd_5908781 : Nat := 4983230072969 + 3 ^ 40 * 5908781 * 2
def baseEnd_5908781 : Nat := 3034044735154151600863517

theorem tailTrace_5908781 : CollatzResearch.WordTrace tailWord_5908781 prefixEnd_5908781 3034044735154151600863517 := by
  unfold tailWord_5908781
  simp only [CollatzResearch.WordTrace]
  refine ⟨215510948006503051298214197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143673965337668700865476131 215510948006503051298214197)
  ·
    refine ⟨20204151375609661059207581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215510948006503051298214197 20204151375609661059207581)
    ·
      refine ⟨7576556765853622897202843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20204151375609661059207581 7576556765853622897202843)
      ·
        refine ⟨11364835148780434345804265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7576556765853622897202843 11364835148780434345804265)
        ·
          refine ⟨8523626361585325759353199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11364835148780434345804265 8523626361585325759353199)
          ·
            refine ⟨12785439542377988639029799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8523626361585325759353199 12785439542377988639029799)
            ·
              refine ⟨19178159313566982958544699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12785439542377988639029799 19178159313566982958544699)
              ·
                refine ⟨28767238970350474437817049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19178159313566982958544699 28767238970350474437817049)
                ·
                  refine ⟨21575429227762855828362787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28767238970350474437817049 21575429227762855828362787)
                  ·
                    refine ⟨32363143841644283742544181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21575429227762855828362787 32363143841644283742544181)
                    ·
                      refine ⟨3034044735154151600863517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32363143841644283742544181 3034044735154151600863517)
                      ·
                        rfl

theorem cell23_5908781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_5908781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908781 prefixEnd_5908781 := by exact prefixLift 5908781
  have htrace : WordTrace (prefixWord ++ tailWord_5908781) baseStart_5908781 baseEnd_5908781 := by
    simpa [prefixWord, tailWord_5908781, baseEnd_5908781] using wordTrace_append hprefix tailTrace_5908781
  have hstable : (prefixWord ++ tailWord_5908781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908781).length < 2 ^ (prefixWord ++ tailWord_5908781).sum := by decide
  have hdescent : baseEnd_5908781 < baseStart_5908781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908801 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 7]
def baseStart_5908801 : Nat := 118140960795 + 5908801 * 2 ^ 59
def prefixEnd_5908801 : Nat := 4983230072969 + 3 ^ 40 * 5908801 * 2
def baseEnd_5908801 : Nat := 337117222751915724734825

theorem tailTrace_5908801 : CollatzResearch.WordTrace tailWord_5908801 prefixEnd_5908801 337117222751915724734825 := by
  unfold tailWord_5908801
  simp only [CollatzResearch.WordTrace]
  refine ⟨215511677466430594713942257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143674451644287063142628171 215511677466430594713942257)
  ·
    refine ⟨161633758099822946035456693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215511677466430594713942257 161633758099822946035456693)
    ·
      refine ⟨15153164821858401190824065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161633758099822946035456693 15153164821858401190824065)
      ·
        refine ⟨11364873616393800893118049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15153164821858401190824065 11364873616393800893118049)
        ·
          refine ⟨8523655212295350669838537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11364873616393800893118049 8523655212295350669838537)
          ·
            refine ⟨6392741409221513002378903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8523655212295350669838537 6392741409221513002378903)
            ·
              refine ⟨9589112113832269503568355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6392741409221513002378903 9589112113832269503568355)
              ·
                refine ⟨14383668170748404255352533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9589112113832269503568355 14383668170748404255352533)
                ·
                  refine ⟨337117222751915724734825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14383668170748404255352533 337117222751915724734825)
                  ·
                    rfl

theorem cell23_5908801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 7].length) (baseStart_5908801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908801 prefixEnd_5908801 := by exact prefixLift 5908801
  have htrace : WordTrace (prefixWord ++ tailWord_5908801) baseStart_5908801 baseEnd_5908801 := by
    simpa [prefixWord, tailWord_5908801, baseEnd_5908801] using wordTrace_append hprefix tailTrace_5908801
  have hstable : (prefixWord ++ tailWord_5908801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908801).length < 2 ^ (prefixWord ++ tailWord_5908801).sum := by decide
  have hdescent : baseEnd_5908801 < baseStart_5908801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908807 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_5908807 : Nat := 118140960795 + 5908807 * 2 ^ 59
def prefixEnd_5908807 : Nat := 4983230072969 + 3 ^ 40 * 5908807 * 2
def baseEnd_5908807 : Nat := 3034058085651168499138397

theorem tailTrace_5908807 : CollatzResearch.WordTrace tailWord_5908807 prefixEnd_5908807 3034058085651168499138397 := by
  unfold tailWord_5908807
  simp only [CollatzResearch.WordTrace]
  refine ⟨215511896304408857738660675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143674597536272571825773783 215511896304408857738660675)
  ·
    refine ⟨323267844456613286607991013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215511896304408857738660675 323267844456613286607991013)
    ·
      refine ⟨60612720835614991238998315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323267844456613286607991013 60612720835614991238998315)
      ·
        refine ⟨90919081253422486858497473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60612720835614991238998315 90919081253422486858497473)
        ·
          refine ⟨68189310940066865143873105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90919081253422486858497473 68189310940066865143873105)
          ·
            refine ⟨51141983205050148857904829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68189310940066865143873105 51141983205050148857904829)
            ·
              refine ⟨19178243701893805821714311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51141983205050148857904829 19178243701893805821714311)
              ·
                refine ⟨28767365552840708732571467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19178243701893805821714311 28767365552840708732571467)
                ·
                  refine ⟨43151048329261063098857201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28767365552840708732571467 43151048329261063098857201)
                  ·
                    refine ⟨32363286246945797324142901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43151048329261063098857201 32363286246945797324142901)
                    ·
                      refine ⟨3034058085651168499138397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32363286246945797324142901 3034058085651168499138397)
                      ·
                        rfl

theorem cell23_5908807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_5908807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908807 prefixEnd_5908807 := by exact prefixLift 5908807
  have htrace : WordTrace (prefixWord ++ tailWord_5908807) baseStart_5908807 baseEnd_5908807 := by
    simpa [prefixWord, tailWord_5908807, baseEnd_5908807] using wordTrace_append hprefix tailTrace_5908807
  have hstable : (prefixWord ++ tailWord_5908807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908807).length < 2 ^ (prefixWord ++ tailWord_5908807).sum := by decide
  have hdescent : baseEnd_5908807 < baseStart_5908807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908888 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 2, 2, 3]
def baseStart_5908888 : Nat := 118140960795 + 5908888 * 2 ^ 59
def prefixEnd_5908888 : Nat := 4983230072969 + 3 ^ 40 * 5908888 * 2
def baseEnd_5908888 : Nat := 3034099677584182682225525

theorem tailTrace_5908888 : CollatzResearch.WordTrace tailWord_5908888 prefixEnd_5908888 3034099677584182682225525 := by
  unfold tailWord_5908888
  simp only [CollatzResearch.WordTrace]
  refine ⟨107757425308557704286179659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143676567078076939048239545 107757425308557704286179659)
  ·
    refine ⟨161636137962836556429269489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107757425308557704286179659 161636137962836556429269489)
    ·
      refine ⟨121227103472127417321952117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161636137962836556429269489 121227103472127417321952117)
      ·
        refine ⟨11365040950511945373933011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121227103472127417321952117 11365040950511945373933011)
        ·
          refine ⟨17047561425767918060899517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11365040950511945373933011 17047561425767918060899517)
          ·
            refine ⟨6392835534662969272837319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17047561425767918060899517 6392835534662969272837319)
            ·
              refine ⟨9589253301994453909255979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6392835534662969272837319 9589253301994453909255979)
              ·
                refine ⟨14383879952991680863883969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9589253301994453909255979 14383879952991680863883969)
                ·
                  refine ⟨10787909964743760647912977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14383879952991680863883969 10787909964743760647912977)
                  ·
                    refine ⟨8090932473557820485934733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10787909964743760647912977 8090932473557820485934733)
                    ·
                      refine ⟨3034099677584182682225525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8090932473557820485934733 3034099677584182682225525)
                      ·
                        rfl

theorem cell23_5908888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_5908888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908888 prefixEnd_5908888 := by exact prefixLift 5908888
  have htrace : WordTrace (prefixWord ++ tailWord_5908888) baseStart_5908888 baseEnd_5908888 := by
    simpa [prefixWord, tailWord_5908888, baseEnd_5908888] using wordTrace_append hprefix tailTrace_5908888
  have hstable : (prefixWord ++ tailWord_5908888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908888).length < 2 ^ (prefixWord ++ tailWord_5908888).sum := by decide
  have hdescent : baseEnd_5908888 < baseStart_5908888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908954 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4]
def baseStart_5908954 : Nat := 118140960795 + 5908954 * 2 ^ 59
def prefixEnd_5908954 : Nat := 4983230072969 + 3 ^ 40 * 5908954 * 2
def baseEnd_5908954 : Nat := 3034133567307379424000221

theorem tailTrace_5908954 : CollatzResearch.WordTrace tailWord_5908954 prefixEnd_5908954 3034133567307379424000221 := by
  unfold tailWord_5908954
  simp only [CollatzResearch.WordTrace]
  refine ⟨53879314458719075461065479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143678171889917534562841277 53879314458719075461065479)
  ·
    refine ⟨80818971688078613191598219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53879314458719075461065479 80818971688078613191598219)
    ·
      refine ⟨121228457532117919787397329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80818971688078613191598219 121228457532117919787397329)
      ·
        refine ⟨90921343149088439840547997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121228457532117919787397329 90921343149088439840547997)
        ·
          refine ⟨34095503680908164940205499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90921343149088439840547997 34095503680908164940205499)
          ·
            refine ⟨51143255521362247410308249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34095503680908164940205499 51143255521362247410308249)
            ·
              refine ⟨38357441641021685557731187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51143255521362247410308249 38357441641021685557731187)
              ·
                refine ⟨57536162461532528336596781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38357441641021685557731187 57536162461532528336596781)
                ·
                  refine ⟨21576060923074698126223793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57536162461532528336596781 21576060923074698126223793)
                  ·
                    refine ⟨16182045692306023594667845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21576060923074698126223793 16182045692306023594667845)
                    ·
                      refine ⟨3034133567307379424000221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16182045692306023594667845 3034133567307379424000221)
                      ·
                        rfl

theorem cell23_5908954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_5908954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908954 prefixEnd_5908954 := by exact prefixLift 5908954
  have htrace : WordTrace (prefixWord ++ tailWord_5908954) baseStart_5908954 baseEnd_5908954 := by
    simpa [prefixWord, tailWord_5908954, baseEnd_5908954] using wordTrace_append hprefix tailTrace_5908954
  have hstable : (prefixWord ++ tailWord_5908954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908954).length < 2 ^ (prefixWord ++ tailWord_5908954).sum := by decide
  have hdescent : baseEnd_5908954 < baseStart_5908954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908961 : List Nat := [1, 2, 3, 1, 2, 2, 1, 5, 1, 2, 3]
def baseStart_5908961 : Nat := 118140960795 + 5908961 * 2 ^ 59
def prefixEnd_5908961 : Nat := 4983230072969 + 3 ^ 40 * 5908961 * 2
def baseEnd_5908961 : Nat := 3034137161671960896612689

theorem tailTrace_5908961 : CollatzResearch.WordTrace tailWord_5908961 prefixEnd_5908961 3034137161671960896612689 := by
  unfold tailWord_5908961
  simp only [CollatzResearch.WordTrace]
  refine ⟨215517513145850942039766737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143678342097233961359844491 215517513145850942039766737)
  ·
    refine ⟨161638134859388206529825053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215517513145850942039766737 161638134859388206529825053)
    ·
      refine ⟨60614300572270577448684395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161638134859388206529825053 60614300572270577448684395)
      ·
        refine ⟨90921450858405866173026593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60614300572270577448684395 90921450858405866173026593)
        ·
          refine ⟨68191088143804399629769945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90921450858405866173026593 68191088143804399629769945)
          ·
            refine ⟨51143316107853299722327459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68191088143804399629769945 51143316107853299722327459)
            ·
              refine ⟨76714974161779949583491189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51143316107853299722327459 76714974161779949583491189)
              ·
                refine ⟨7192028827666870273452299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76714974161779949583491189 7192028827666870273452299)
                ·
                  refine ⟨10788043241500305410178449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7192028827666870273452299 10788043241500305410178449)
                  ·
                    refine ⟨8091032431125229057633837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10788043241500305410178449 8091032431125229057633837)
                    ·
                      refine ⟨3034137161671960896612689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8091032431125229057633837 3034137161671960896612689)
                      ·
                        rfl

theorem cell23_5908961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_5908961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908961 prefixEnd_5908961 := by exact prefixLift 5908961
  have htrace : WordTrace (prefixWord ++ tailWord_5908961) baseStart_5908961 baseEnd_5908961 := by
    simpa [prefixWord, tailWord_5908961, baseEnd_5908961] using wordTrace_append hprefix tailTrace_5908961
  have hstable : (prefixWord ++ tailWord_5908961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908961).length < 2 ^ (prefixWord ++ tailWord_5908961).sum := by decide
  have hdescent : baseEnd_5908961 < baseStart_5908961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5908962 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_5908962 : Nat := 118140960795 + 5908962 * 2 ^ 59
def prefixEnd_5908962 : Nat := 4983230072969 + 3 ^ 40 * 5908962 * 2
def baseEnd_5908962 : Nat := 3034137675152615392700185

theorem tailTrace_5908962 : CollatzResearch.WordTrace tailWord_5908962 prefixEnd_5908962 3034137675152615392700185 := by
  unfold tailWord_5908962
  simp only [CollatzResearch.WordTrace]
  refine ⟨53879387404711829802638285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143678366412564879473702093 53879387404711829802638285)
  ·
    refine ⟨20204770276766936175989357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53879387404711829802638285 20204770276766936175989357)
    ·
      refine ⟨7576788853787601065996009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20204770276766936175989357 7576788853787601065996009)
      ·
        refine ⟨5682591640340700799497007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7576788853787601065996009 5682591640340700799497007)
        ·
          refine ⟨8523887460511051199245511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5682591640340700799497007 8523887460511051199245511)
          ·
            refine ⟨12785831190766576798868267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8523887460511051199245511 12785831190766576798868267)
            ·
              refine ⟨19178746786149865198302401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12785831190766576798868267 19178746786149865198302401)
              ·
                refine ⟨14384060089612398898726801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19178746786149865198302401 14384060089612398898726801)
                ·
                  refine ⟨10788045067209299174045101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14384060089612398898726801 10788045067209299174045101)
                  ·
                    refine ⟨4045516900203487190266913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10788045067209299174045101 4045516900203487190266913)
                    ·
                      refine ⟨3034137675152615392700185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4045516900203487190266913 3034137675152615392700185)
                      ·
                        rfl

theorem cell23_5908962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_5908962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5908962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5908962 prefixEnd_5908962 := by exact prefixLift 5908962
  have htrace : WordTrace (prefixWord ++ tailWord_5908962) baseStart_5908962 baseEnd_5908962 := by
    simpa [prefixWord, tailWord_5908962, baseEnd_5908962] using wordTrace_append hprefix tailTrace_5908962
  have hstable : (prefixWord ++ tailWord_5908962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5908962).length < 2 ^ (prefixWord ++ tailWord_5908962).sum := by decide
  have hdescent : baseEnd_5908962 < baseStart_5908962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5908962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909005 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_5909005 : Nat := 118140960795 + 5909005 * 2 ^ 59
def prefixEnd_5909005 : Nat := 4983230072969 + 3 ^ 40 * 5909005 * 2
def baseEnd_5909005 : Nat := 3034159754820758724462487

theorem tailTrace_5909005 : CollatzResearch.WordTrace tailWord_5909005 prefixEnd_5909005 3034159754820758724462487 := by
  unfold tailWord_5909005
  simp only [CollatzResearch.WordTrace]
  refine ⟨215519117957691537554368469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143679411971794358369578979 215519117957691537554368469)
  ·
    refine ⟨5051229327133395411430511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 215519117957691537554368469 5051229327133395411430511)
    ·
      refine ⟨7576843990700093117145767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5051229327133395411430511 7576843990700093117145767)
      ·
        refine ⟨11365265986050139675718651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7576843990700093117145767 11365265986050139675718651)
        ·
          refine ⟨17047898979075209513577977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11365265986050139675718651 17047898979075209513577977)
          ·
            refine ⟨12785924234306407135183483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17047898979075209513577977 12785924234306407135183483)
            ·
              refine ⟨19178886351459610702775225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12785924234306407135183483 19178886351459610702775225)
              ·
                refine ⟨14384164763594708027081419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19178886351459610702775225 14384164763594708027081419)
                ·
                  refine ⟨21576247145392062040622129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14384164763594708027081419 21576247145392062040622129)
                  ·
                    refine ⟨16182185359044046530466597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21576247145392062040622129 16182185359044046530466597)
                    ·
                      refine ⟨3034159754820758724462487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16182185359044046530466597 3034159754820758724462487)
                      ·
                        rfl

theorem cell23_5909005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_5909005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909005 prefixEnd_5909005 := by exact prefixLift 5909005
  have htrace : WordTrace (prefixWord ++ tailWord_5909005) baseStart_5909005 baseEnd_5909005 := by
    simpa [prefixWord, tailWord_5909005, baseEnd_5909005] using wordTrace_append hprefix tailTrace_5909005
  have hstable : (prefixWord ++ tailWord_5909005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909005).length < 2 ^ (prefixWord ++ tailWord_5909005).sum := by decide
  have hdescent : baseEnd_5909005 < baseStart_5909005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909012 : List Nat := [2, 4, 3, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_5909012 : Nat := 118140960795 + 5909012 * 2 ^ 59
def prefixEnd_5909012 : Nat := 4983230072969 + 3 ^ 40 * 5909012 * 2
def baseEnd_5909012 : Nat := 3034163349185340197074955

theorem tailTrace_5909012 : CollatzResearch.WordTrace tailWord_5909012 prefixEnd_5909012 3034163349185340197074955 := by
  unfold tailWord_5909012
  simp only [CollatzResearch.WordTrace]
  refine ⟨107759686634333088874936645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143679582179110785166582193 107759686634333088874936645)
  ·
    refine ⟨20204941243937454164050621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107759686634333088874936645 20204941243937454164050621)
    ·
      refine ⟨7576852966476545311518983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20204941243937454164050621 7576852966476545311518983)
      ·
        refine ⟨11365279449714817967278475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7576852966476545311518983 11365279449714817967278475)
        ·
          refine ⟨17047919174572226950917713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11365279449714817967278475 17047919174572226950917713)
          ·
            refine ⟨12785939380929170213188285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17047919174572226950917713 12785939380929170213188285)
            ·
              refine ⟨4794727267848438829945607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12785939380929170213188285 4794727267848438829945607)
              ·
                refine ⟨7192090901772658244918411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4794727267848438829945607 7192090901772658244918411)
                ·
                  refine ⟨10788136352658987367377617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7192090901772658244918411 10788136352658987367377617)
                  ·
                    refine ⟨8091102264494240525533213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10788136352658987367377617 8091102264494240525533213)
                    ·
                      refine ⟨3034163349185340197074955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8091102264494240525533213 3034163349185340197074955)
                      ·
                        rfl

theorem cell23_5909012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_5909012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909012 prefixEnd_5909012 := by exact prefixLift 5909012
  have htrace : WordTrace (prefixWord ++ tailWord_5909012) baseStart_5909012 baseEnd_5909012 := by
    simpa [prefixWord, tailWord_5909012, baseEnd_5909012] using wordTrace_append hprefix tailTrace_5909012
  have hstable : (prefixWord ++ tailWord_5909012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909012).length < 2 ^ (prefixWord ++ tailWord_5909012).sum := by decide
  have hdescent : baseEnd_5909012 < baseStart_5909012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909018 : List Nat := [3, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2]
def baseStart_5909018 : Nat := 118140960795 + 5909018 * 2 ^ 59
def prefixEnd_5909018 : Nat := 4983230072969 + 3 ^ 40 * 5909018 * 2
def baseEnd_5909018 : Nat := 3034166430069267173599927

theorem tailTrace_5909018 : CollatzResearch.WordTrace tailWord_5909018 prefixEnd_5909018 3034166430069267173599927 := by
  unfold tailWord_5909018
  simp only [CollatzResearch.WordTrace]
  refine ⟨53879898026661110193647927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143679728071096293849727805 53879898026661110193647927)
  ·
    refine ⟨80819847039991665290471891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53879898026661110193647927 80819847039991665290471891)
    ·
      refine ⟨121229770559987497935707837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80819847039991665290471891 121229770559987497935707837)
      ·
        refine ⟨45461163959995311725890439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121229770559987497935707837 45461163959995311725890439)
        ·
          refine ⟨68191745939992967588835659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45461163959995311725890439 68191745939992967588835659)
          ·
            refine ⟨102287618909989451383253489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68191745939992967588835659 102287618909989451383253489)
            ·
              refine ⟨76715714182492088537440117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102287618909989451383253489 76715714182492088537440117)
              ·
                refine ⟨7192098204608633300385011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76715714182492088537440117 7192098204608633300385011)
                ·
                  refine ⟨10788147306912949950577517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7192098204608633300385011 10788147306912949950577517)
                  ·
                    refine ⟨4045555240092356231466569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10788147306912949950577517 4045555240092356231466569)
                    ·
                      refine ⟨3034166430069267173599927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4045555240092356231466569 3034166430069267173599927)
                      ·
                        rfl

theorem cell23_5909018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_5909018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909018 prefixEnd_5909018 := by exact prefixLift 5909018
  have htrace : WordTrace (prefixWord ++ tailWord_5909018) baseStart_5909018 baseEnd_5909018 := by
    simpa [prefixWord, tailWord_5909018, baseEnd_5909018] using wordTrace_append hprefix tailTrace_5909018
  have hstable : (prefixWord ++ tailWord_5909018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909018).length < 2 ^ (prefixWord ++ tailWord_5909018).sum := by decide
  have hdescent : baseEnd_5909018 < baseStart_5909018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909048 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 1, 4, 2]
def baseStart_5909048 : Nat := 118140960795 + 5909048 * 2 ^ 59
def prefixEnd_5909048 : Nat := 4983230072969 + 3 ^ 40 * 5909048 * 2
def baseEnd_5909048 : Nat := 3034181834488902056224789

theorem tailTrace_5909048 : CollatzResearch.WordTrace tailWord_5909048 prefixEnd_5909048 3034181834488902056224789 := by
  unfold tailWord_5909048
  simp only [CollatzResearch.WordTrace]
  refine ⟨107760343148267877949091899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143680457531023837265455865 107760343148267877949091899)
  ·
    refine ⟨161640514722401816923637849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107760343148267877949091899 161640514722401816923637849)
    ·
      refine ⟨121230386041801362692728387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161640514722401816923637849 121230386041801362692728387)
      ·
        refine ⟨181845579062702044039092581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121230386041801362692728387 181845579062702044039092581)
        ·
          refine ⟨34096046074256633257329859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181845579062702044039092581 34096046074256633257329859)
          ·
            refine ⟨51144069111384949885994789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34096046074256633257329859 51144069111384949885994789)
            ·
              refine ⟨9589512958384678103624023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51144069111384949885994789 9589512958384678103624023)
              ·
                refine ⟨14384269437577017155436035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9589512958384678103624023 14384269437577017155436035)
                ·
                  refine ⟨21576404156365525733154053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14384269437577017155436035 21576404156365525733154053)
                  ·
                    refine ⟨4045575779318536074966385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21576404156365525733154053 4045575779318536074966385)
                    ·
                      refine ⟨3034181834488902056224789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4045575779318536074966385 3034181834488902056224789)
                      ·
                        rfl

theorem cell23_5909048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 1, 4, 2].length) (baseStart_5909048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909048 prefixEnd_5909048 := by exact prefixLift 5909048
  have htrace : WordTrace (prefixWord ++ tailWord_5909048) baseStart_5909048 baseEnd_5909048 := by
    simpa [prefixWord, tailWord_5909048, baseEnd_5909048] using wordTrace_append hprefix tailTrace_5909048
  have hstable : (prefixWord ++ tailWord_5909048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909048).length < 2 ^ (prefixWord ++ tailWord_5909048).sum := by decide
  have hdescent : baseEnd_5909048 < baseStart_5909048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909069 : List Nat := [1, 6, 1, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_5909069 : Nat := 118140960795 + 5909069 * 2 ^ 59
def prefixEnd_5909069 : Nat := 4983230072969 + 3 ^ 40 * 5909069 * 2
def baseEnd_5909069 : Nat := 3034192617582646474062193

theorem tailTrace_5909069 : CollatzResearch.WordTrace tailWord_5909069 prefixEnd_5909069 3034192617582646474062193 := by
  unfold tailWord_5909069
  simp only [CollatzResearch.WordTrace]
  refine ⟨215521452229459676484698261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143680968152973117656465507 215521452229459676484698261)
  ·
    refine ⟨10102568073255922335220231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 215521452229459676484698261 10102568073255922335220231)
    ·
      refine ⟨15153852109883883502830347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10102568073255922335220231 15153852109883883502830347)
      ·
        refine ⟨22730778164825825254245521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15153852109883883502830347 22730778164825825254245521)
        ·
          refine ⟨17048083623619368940684141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22730778164825825254245521 17048083623619368940684141)
          ·
            refine ⟨6393031358857263352756553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17048083623619368940684141 6393031358857263352756553)
            ·
              refine ⟨4794773519142947514567415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6393031358857263352756553 4794773519142947514567415)
              ·
                refine ⟨7192160278714421271851123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4794773519142947514567415 7192160278714421271851123)
                ·
                  refine ⟨10788240418071631907776685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7192160278714421271851123 10788240418071631907776685)
                  ·
                    refine ⟨4045590156776861965416257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10788240418071631907776685 4045590156776861965416257)
                    ·
                      refine ⟨3034192617582646474062193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4045590156776861965416257 3034192617582646474062193)
                      ·
                        rfl

theorem cell23_5909069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_5909069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909069 prefixEnd_5909069 := by exact prefixLift 5909069
  have htrace : WordTrace (prefixWord ++ tailWord_5909069) baseStart_5909069 baseEnd_5909069 := by
    simpa [prefixWord, tailWord_5909069, baseEnd_5909069] using wordTrace_append hprefix tailTrace_5909069
  have hstable : (prefixWord ++ tailWord_5909069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909069).length < 2 ^ (prefixWord ++ tailWord_5909069).sum := by decide
  have hdescent : baseEnd_5909069 < baseStart_5909069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909071 : List Nat := [1, 1, 2, 1, 1, 2, 5, 5, 5]
def baseStart_5909071 : Nat := 118140960795 + 5909071 * 2 ^ 59
def prefixEnd_5909071 : Nat := 4983230072969 + 3 ^ 40 * 5909071 * 2
def baseEnd_5909071 : Nat := 337132627171550607359687

theorem tailTrace_5909071 : CollatzResearch.WordTrace tailWord_5909071 prefixEnd_5909071 337132627171550607359687 := by
  unfold tailWord_5909071
  simp only [CollatzResearch.WordTrace]
  refine ⟨215521525175452430826271067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143681016783634953884180711 215521525175452430826271067)
  ·
    refine ⟨323282287763178646239406601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215521525175452430826271067 323282287763178646239406601)
    ·
      refine ⟨242461715822383984679554951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323282287763178646239406601 242461715822383984679554951)
      ·
        refine ⟨363692573733575977019332427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242461715822383984679554951 363692573733575977019332427)
        ·
          refine ⟨545538860600363965528998641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363692573733575977019332427 545538860600363965528998641)
          ·
            refine ⟨409154145450272974146748981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 545538860600363965528998641 409154145450272974146748981)
            ·
              refine ⟨38358201135963091326257717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 409154145450272974146748981 38358201135963091326257717)
              ·
                refine ⟨3596081356496539811836661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38358201135963091326257717 3596081356496539811836661)
                ·
                  refine ⟨337132627171550607359687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3596081356496539811836661 337132627171550607359687)
                  ·
                    rfl

theorem cell23_5909071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 5].length) (baseStart_5909071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909071 prefixEnd_5909071 := by exact prefixLift 5909071
  have htrace : WordTrace (prefixWord ++ tailWord_5909071) baseStart_5909071 baseEnd_5909071 := by
    simpa [prefixWord, tailWord_5909071, baseEnd_5909071] using wordTrace_append hprefix tailTrace_5909071
  have hstable : (prefixWord ++ tailWord_5909071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909071).length < 2 ^ (prefixWord ++ tailWord_5909071).sum := by decide
  have hdescent : baseEnd_5909071 < baseStart_5909071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909101 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_5909101 : Nat := 118140960795 + 5909101 * 2 ^ 59
def prefixEnd_5909101 : Nat := 4983230072969 + 3 ^ 40 * 5909101 * 2
def baseEnd_5909101 : Nat := 1011403016321196782954015

theorem tailTrace_5909101 : CollatzResearch.WordTrace tailWord_5909101 prefixEnd_5909101 1011403016321196782954015 := by
  unfold tailWord_5909101
  simp only [CollatzResearch.WordTrace]
  refine ⟨215522619365343745949863157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143681746243562497299908771 215522619365343745949863157)
  ·
    refine ⟨20205245565500976182799671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215522619365343745949863157 20205245565500976182799671)
    ·
      refine ⟨30307868348251464274199507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20205245565500976182799671 30307868348251464274199507)
      ·
        refine ⟨45461802522377196411299261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30307868348251464274199507 45461802522377196411299261)
        ·
          refine ⟨17048175945891448654237223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45461802522377196411299261 17048175945891448654237223)
          ·
            refine ⟨25572263918837172981355835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17048175945891448654237223 25572263918837172981355835)
            ·
              refine ⟨38358395878255759472033753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25572263918837172981355835 38358395878255759472033753)
              ·
                refine ⟨28768796908691819604025315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38358395878255759472033753 28768796908691819604025315)
                ·
                  refine ⟨43153195363037729406037973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28768796908691819604025315 43153195363037729406037973)
                  ·
                    refine ⟨1011403016321196782954015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43153195363037729406037973 1011403016321196782954015)
                    ·
                      rfl

theorem cell23_5909101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_5909101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909101 prefixEnd_5909101 := by exact prefixLift 5909101
  have htrace : WordTrace (prefixWord ++ tailWord_5909101) baseStart_5909101 baseEnd_5909101 := by
    simpa [prefixWord, tailWord_5909101, baseEnd_5909101] using wordTrace_append hprefix tailTrace_5909101
  have hstable : (prefixWord ++ tailWord_5909101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909101).length < 2 ^ (prefixWord ++ tailWord_5909101).sum := by decide
  have hdescent : baseEnd_5909101 < baseStart_5909101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909121 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_5909121 : Nat := 118140960795 + 5909121 * 2 ^ 59
def prefixEnd_5909121 : Nat := 4983230072969 + 3 ^ 40 * 5909121 * 2
def baseEnd_5909121 : Nat := 3034219318576680270611953

theorem tailTrace_5909121 : CollatzResearch.WordTrace tailWord_5909121 prefixEnd_5909121 3034219318576680270611953 := by
  unfold tailWord_5909121
  simp only [CollatzResearch.WordTrace]
  refine ⟨215523348825271289365591217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143682232550180859577060811 215523348825271289365591217)
  ·
    refine ⟨161642511618953467024193413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215523348825271289365591217 161642511618953467024193413)
    ·
      refine ⟨30307970928553775067036265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161642511618953467024193413 30307970928553775067036265)
      ·
        refine ⟨22730978196415331300277199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30307970928553775067036265 22730978196415331300277199)
        ·
          refine ⟨34096467294622996950415799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22730978196415331300277199 34096467294622996950415799)
          ·
            refine ⟨51144700941934495425623699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34096467294622996950415799 51144700941934495425623699)
            ·
              refine ⟨76717051412901743138435549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51144700941934495425623699 76717051412901743138435549)
              ·
                refine ⟨28768894279838153676913331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76717051412901743138435549 28768894279838153676913331)
                ·
                  refine ⟨43153341419757230515369997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28768894279838153676913331 43153341419757230515369997)
                  ·
                    refine ⟨16182503032408961443263749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43153341419757230515369997 16182503032408961443263749)
                    ·
                      refine ⟨3034219318576680270611953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16182503032408961443263749 3034219318576680270611953)
                      ·
                        rfl

theorem cell23_5909121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_5909121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909121 prefixEnd_5909121 := by exact prefixLift 5909121
  have htrace : WordTrace (prefixWord ++ tailWord_5909121) baseStart_5909121 baseEnd_5909121 := by
    simpa [prefixWord, tailWord_5909121, baseEnd_5909121] using wordTrace_append hprefix tailTrace_5909121
  have hstable : (prefixWord ++ tailWord_5909121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909121).length < 2 ^ (prefixWord ++ tailWord_5909121).sum := by decide
  have hdescent : baseEnd_5909121 < baseStart_5909121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909138 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_5909138 : Nat := 118140960795 + 5909138 * 2 ^ 59
def prefixEnd_5909138 : Nat := 4983230072969 + 3 ^ 40 * 5909138 * 2
def baseEnd_5909138 : Nat := 3034228047747806704099375

theorem tailTrace_5909138 : CollatzResearch.WordTrace tailWord_5909138 prefixEnd_5909138 3034228047747806704099375 := by
  unfold tailWord_5909138
  simp only [CollatzResearch.WordTrace]
  refine ⟨53880992216552425317240017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143682645910806467512640045 53880992216552425317240017)
  ·
    refine ⟨40410744162414318987930013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53880992216552425317240017 40410744162414318987930013)
    ·
      refine ⟨15154029060905369620473755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40410744162414318987930013 15154029060905369620473755)
      ·
        refine ⟨22731043591358054430710633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15154029060905369620473755 22731043591358054430710633)
        ·
          refine ⟨17048282693518540823032975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22731043591358054430710633 17048282693518540823032975)
          ·
            refine ⟨25572424040277811234549463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17048282693518540823032975 25572424040277811234549463)
            ·
              refine ⟨38358636060416716851824195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25572424040277811234549463 38358636060416716851824195)
              ·
                refine ⟨57537954090625075277736293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38358636060416716851824195 57537954090625075277736293)
                ·
                  refine ⟨10788366391992201614575555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57537954090625075277736293 10788366391992201614575555)
                  ·
                    refine ⟨16182549587988302421863333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10788366391992201614575555 16182549587988302421863333)
                    ·
                      refine ⟨3034228047747806704099375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16182549587988302421863333 3034228047747806704099375)
                      ·
                        rfl

theorem cell23_5909138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_5909138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909138 prefixEnd_5909138 := by exact prefixLift 5909138
  have htrace : WordTrace (prefixWord ++ tailWord_5909138) baseStart_5909138 baseEnd_5909138 := by
    simpa [prefixWord, tailWord_5909138, baseEnd_5909138] using wordTrace_append hprefix tailTrace_5909138
  have hstable : (prefixWord ++ tailWord_5909138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909138).length < 2 ^ (prefixWord ++ tailWord_5909138).sum := by decide
  have hdescent : baseEnd_5909138 < baseStart_5909138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909175 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 3]
def baseStart_5909175 : Nat := 118140960795 + 5909175 * 2 ^ 59
def prefixEnd_5909175 : Nat := 4983230072969 + 3 ^ 40 * 5909175 * 2
def baseEnd_5909175 : Nat := 3034247046532023059336705

theorem tailTrace_5909175 : CollatzResearch.WordTrace tailWord_5909175 prefixEnd_5909175 3034247046532023059336705 := by
  unfold tailWord_5909175
  simp only [CollatzResearch.WordTrace]
  refine ⟨215525318367075656588056979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143683545578050437725371319 215525318367075656588056979)
  ·
    refine ⟨323287977550613484882085469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215525318367075656588056979 323287977550613484882085469)
    ·
      refine ⟨121232991581480056830782051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323287977550613484882085469 121232991581480056830782051)
      ·
        refine ⟨181849487372220085246173077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121232991581480056830782051 181849487372220085246173077)
        ·
          refine ⟨8524194720572816495914363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 181849487372220085246173077 8524194720572816495914363)
          ·
            refine ⟨12786292080859224743871545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8524194720572816495914363 12786292080859224743871545)
            ·
              refine ⟨9589719060644418557903659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12786292080859224743871545 9589719060644418557903659)
              ·
                refine ⟨14384578590966627836855489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9589719060644418557903659 14384578590966627836855489)
                ·
                  refine ⟨10788433943224970877641617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14384578590966627836855489 10788433943224970877641617)
                  ·
                    refine ⟨8091325457418728158231213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10788433943224970877641617 8091325457418728158231213)
                    ·
                      refine ⟨3034247046532023059336705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8091325457418728158231213 3034247046532023059336705)
                      ·
                        rfl

theorem cell23_5909175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_5909175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909175 prefixEnd_5909175 := by exact prefixLift 5909175
  have htrace : WordTrace (prefixWord ++ tailWord_5909175) baseStart_5909175 baseEnd_5909175 := by
    simpa [prefixWord, tailWord_5909175, baseEnd_5909175] using wordTrace_append hprefix tailTrace_5909175
  have hstable : (prefixWord ++ tailWord_5909175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909175).length < 2 ^ (prefixWord ++ tailWord_5909175).sum := by decide
  have hdescent : baseEnd_5909175 < baseStart_5909175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909228 : List Nat := [2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 4]
def baseStart_5909228 : Nat := 118140960795 + 5909228 * 2 ^ 59
def prefixEnd_5909228 : Nat := 4983230072969 + 3 ^ 40 * 5909228 * 2
def baseEnd_5909228 : Nat := 3034274261006711351973961

theorem tailTrace_5909228 : CollatzResearch.WordTrace tailWord_5909228 prefixEnd_5909228 3034274261006711351973961 := by
  unfold tailWord_5909228
  simp only [CollatzResearch.WordTrace]
  refine ⟨107763625717941823319868169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143684834290589097759824225 107763625717941823319868169)
  ·
    refine ⟨80822719288456367489901127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107763625717941823319868169 80822719288456367489901127)
    ·
      refine ⟨121234078932684551234851691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80822719288456367489901127 121234078932684551234851691)
      ·
        refine ⟨181851118399026826852277537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121234078932684551234851691 181851118399026826852277537)
        ·
          refine ⟨136388338799270120139208153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181851118399026826852277537 136388338799270120139208153)
          ·
            refine ⟨102291254099452590104406115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136388338799270120139208153 102291254099452590104406115)
            ·
              refine ⟨153436881149178885156609173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102291254099452590104406115 153436881149178885156609173)
              ·
                refine ⟨7192353803867760241716055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153436881149178885156609173 7192353803867760241716055)
                ·
                  refine ⟨10788530705801640362574083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7192353803867760241716055 10788530705801640362574083)
                  ·
                    refine ⟨16182796058702460543861125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10788530705801640362574083 16182796058702460543861125)
                    ·
                      refine ⟨3034274261006711351973961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16182796058702460543861125 3034274261006711351973961)
                      ·
                        rfl

theorem cell23_5909228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_5909228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909228 prefixEnd_5909228 := by exact prefixLift 5909228
  have htrace : WordTrace (prefixWord ++ tailWord_5909228) baseStart_5909228 baseEnd_5909228 := by
    simpa [prefixWord, tailWord_5909228, baseEnd_5909228] using wordTrace_append hprefix tailTrace_5909228
  have hstable : (prefixWord ++ tailWord_5909228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909228).length < 2 ^ (prefixWord ++ tailWord_5909228).sum := by decide
  have hdescent : baseEnd_5909228 < baseStart_5909228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909238 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_5909238 : Nat := 118140960795 + 5909238 * 2 ^ 59
def prefixEnd_5909238 : Nat := 4983230072969 + 3 ^ 40 * 5909238 * 2
def baseEnd_5909238 : Nat := 1011426465271085437616305

theorem tailTrace_5909238 : CollatzResearch.WordTrace tailWord_5909238 prefixEnd_5909238 1011426465271085437616305 := by
  unfold tailWord_5909238
  simp only [CollatzResearch.WordTrace]
  refine ⟨13470476010365463646725023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143685077443898278898400245 13470476010365463646725023)
  ·
    refine ⟨20205714015548195470087535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13470476010365463646725023 20205714015548195470087535)
    ·
      refine ⟨30308571023322293205131303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20205714015548195470087535 30308571023322293205131303)
      ·
        refine ⟨45462856534983439807696955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30308571023322293205131303 45462856534983439807696955)
        ·
          refine ⟨68194284802475159711545433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45462856534983439807696955 68194284802475159711545433)
          ·
            refine ⟨51145713601856369783659075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68194284802475159711545433 51145713601856369783659075)
            ·
              refine ⟨76718570402784554675488613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51145713601856369783659075 76718570402784554675488613)
              ·
                refine ⟨14384731950522104001654115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76718570402784554675488613 14384731950522104001654115)
                ·
                  refine ⟨21577097925783156002481173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14384731950522104001654115 21577097925783156002481173)
                  ·
                    refine ⟨1011426465271085437616305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21577097925783156002481173 1011426465271085437616305)
                    ·
                      rfl

theorem cell23_5909238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_5909238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909238 prefixEnd_5909238 := by exact prefixLift 5909238
  have htrace : WordTrace (prefixWord ++ tailWord_5909238) baseStart_5909238 baseEnd_5909238 := by
    simpa [prefixWord, tailWord_5909238, baseEnd_5909238] using wordTrace_append hprefix tailTrace_5909238
  have hstable : (prefixWord ++ tailWord_5909238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909238).length < 2 ^ (prefixWord ++ tailWord_5909238).sum := by decide
  have hdescent : baseEnd_5909238 < baseStart_5909238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909245 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 5, 2, 2]
def baseStart_5909245 : Nat := 118140960795 + 5909245 * 2 ^ 59
def prefixEnd_5909245 : Nat := 4983230072969 + 3 ^ 40 * 5909245 * 2
def baseEnd_5909245 : Nat := 3034282990177837785461383

theorem tailTrace_5909245 : CollatzResearch.WordTrace tailWord_5909245 prefixEnd_5909245 3034282990177837785461383 := by
  unfold tailWord_5909245
  simp only [CollatzResearch.WordTrace]
  refine ⟨215527871476822058543105189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143685247651214705695403459 215527871476822058543105189)
  ·
    refine ⟨40411475901904135976832223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215527871476822058543105189 40411475901904135976832223)
    ·
      refine ⟨60617213852856203965248335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40411475901904135976832223 60617213852856203965248335)
      ·
        refine ⟨90925820779284305947872503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60617213852856203965248335 90925820779284305947872503)
        ·
          refine ⟨136388731168926458921808755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90925820779284305947872503 136388731168926458921808755)
          ·
            refine ⟨204583096753389688382713133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136388731168926458921808755 204583096753389688382713133)
            ·
              refine ⟨76718661282521133143517425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204583096753389688382713133 76718661282521133143517425)
              ·
                refine ⟨57538995961890849857638069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76718661282521133143517425 57538995961890849857638069)
                ·
                  refine ⟨5394280871427267174153569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57538995961890849857638069 5394280871427267174153569)
                  ·
                    refine ⟨4045710653570450380615177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5394280871427267174153569 4045710653570450380615177)
                    ·
                      refine ⟨3034282990177837785461383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4045710653570450380615177 3034282990177837785461383)
                      ·
                        rfl

theorem cell23_5909245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_5909245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909245 prefixEnd_5909245 := by exact prefixLift 5909245
  have htrace : WordTrace (prefixWord ++ tailWord_5909245) baseStart_5909245 baseEnd_5909245 := by
    simpa [prefixWord, tailWord_5909245, baseEnd_5909245] using wordTrace_append hprefix tailTrace_5909245
  have hstable : (prefixWord ++ tailWord_5909245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909245).length < 2 ^ (prefixWord ++ tailWord_5909245).sum := by decide
  have hdescent : baseEnd_5909245 < baseStart_5909245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909255 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 4, 4]
def baseStart_5909255 : Nat := 118140960795 + 5909255 * 2 ^ 59
def prefixEnd_5909255 : Nat := 4983230072969 + 3 ^ 40 * 5909255 * 2
def baseEnd_5909255 : Nat := 1011429374994794248778779

theorem tailTrace_5909255 : CollatzResearch.WordTrace tailWord_5909255 prefixEnd_5909255 1011429374994794248778779 := by
  unfold tailWord_5909255
  simp only [CollatzResearch.WordTrace]
  refine ⟨215528236206785830250969219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143685490804523886833979479 215528236206785830250969219)
  ·
    refine ⟨323292354310178745376453829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215528236206785830250969219 323292354310178745376453829)
    ·
      refine ⟨60617316433158514758085093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323292354310178745376453829 60617316433158514758085093)
      ·
        refine ⟨11365746831217221517140955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60617316433158514758085093 11365746831217221517140955)
        ·
          refine ⟨17048620246825832275711433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11365746831217221517140955 17048620246825832275711433)
          ·
            refine ⟨12786465185119374206783575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17048620246825832275711433 12786465185119374206783575)
            ·
              refine ⟨19179697777679061310175363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12786465185119374206783575 19179697777679061310175363)
              ·
                refine ⟨28769546666518591965263045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19179697777679061310175363 28769546666518591965263045)
                ·
                  refine ⟨5394289999972235993486821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28769546666518591965263045 5394289999972235993486821)
                  ·
                    refine ⟨1011429374994794248778779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5394289999972235993486821 1011429374994794248778779)
                    ·
                      rfl

theorem cell23_5909255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_5909255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909255 prefixEnd_5909255 := by exact prefixLift 5909255
  have htrace : WordTrace (prefixWord ++ tailWord_5909255) baseStart_5909255 baseEnd_5909255 := by
    simpa [prefixWord, tailWord_5909255, baseEnd_5909255] using wordTrace_append hprefix tailTrace_5909255
  have hstable : (prefixWord ++ tailWord_5909255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909255).length < 2 ^ (prefixWord ++ tailWord_5909255).sum := by decide
  have hdescent : baseEnd_5909255 < baseStart_5909255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909282 : List Nat := [3, 3, 1, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_5909282 : Nat := 118140960795 + 5909282 * 2 ^ 59
def prefixEnd_5909282 : Nat := 4983230072969 + 3 ^ 40 * 5909282 * 2
def baseEnd_5909282 : Nat := 3034301988962054140698713

theorem tailTrace_5909282 : CollatzResearch.WordTrace tailWord_5909282 prefixEnd_5909282 3034301988962054140698713 := by
  unfold tailWord_5909282
  simp only [CollatzResearch.WordTrace]
  refine ⟨53882305244422003465550525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143686147318458675908134733 53882305244422003465550525)
  ·
    refine ⟨20205864466658251299581447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53882305244422003465550525 20205864466658251299581447)
    ·
      refine ⟨30308796699987376949372171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20205864466658251299581447 30308796699987376949372171)
      ·
        refine ⟨45463195049981065424058257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30308796699987376949372171 45463195049981065424058257)
        ·
          refine ⟨34097396287485799068043693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45463195049981065424058257 34097396287485799068043693)
          ·
            refine ⟨12786523607807174650516385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34097396287485799068043693 12786523607807174650516385)
            ·
              refine ⟨9589892705855380987887289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12786523607807174650516385 9589892705855380987887289)
              ·
                refine ⟨7192419529391535740915467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9589892705855380987887289 7192419529391535740915467)
                ·
                  refine ⟨10788629294087303611373201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7192419529391535740915467 10788629294087303611373201)
                  ·
                    refine ⟨8091471970565477708529901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10788629294087303611373201 8091471970565477708529901)
                    ·
                      refine ⟨3034301988962054140698713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8091471970565477708529901 3034301988962054140698713)
                      ·
                        rfl

theorem cell23_5909282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_5909282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909282 prefixEnd_5909282 := by exact prefixLift 5909282
  have htrace : WordTrace (prefixWord ++ tailWord_5909282) baseStart_5909282 baseEnd_5909282 := by
    simpa [prefixWord, tailWord_5909282, baseEnd_5909282] using wordTrace_append hprefix tailTrace_5909282
  have hstable : (prefixWord ++ tailWord_5909282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909282).length < 2 ^ (prefixWord ++ tailWord_5909282).sum := by decide
  have hdescent : baseEnd_5909282 < baseStart_5909282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909291 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 5]
def baseStart_5909291 : Nat := 118140960795 + 5909291 * 2 ^ 59
def prefixEnd_5909291 : Nat := 4983230072969 + 3 ^ 40 * 5909291 * 2
def baseEnd_5909291 : Nat := 3034306610287944605486171

theorem tailTrace_5909291 : CollatzResearch.WordTrace tailWord_5909291 prefixEnd_5909291 3034306610287944605486171 := by
  unfold tailWord_5909291
  simp only [CollatzResearch.WordTrace]
  refine ⟨215529549234655408399279727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143686366156436938932853151 215529549234655408399279727)
  ·
    refine ⟨323294323851983112598919591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215529549234655408399279727 323294323851983112598919591)
    ·
      refine ⟨484941485777974668898379387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323294323851983112598919591 484941485777974668898379387)
      ·
        refine ⟨727412228666962003347569081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484941485777974668898379387 727412228666962003347569081)
        ·
          refine ⟨545559171500221502510676811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 727412228666962003347569081 545559171500221502510676811)
          ·
            refine ⟨818338757250332253766015217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545559171500221502510676811 818338757250332253766015217)
            ·
              refine ⟨613754067937749190324511413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 818338757250332253766015217 613754067937749190324511413)
              ·
                refine ⟨57539443869163986592922945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 613754067937749190324511413 57539443869163986592922945)
                ·
                  refine ⟨43154582901872989944692209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57539443869163986592922945 43154582901872989944692209)
                  ·
                    refine ⟨32365937176404742458519157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43154582901872989944692209 32365937176404742458519157)
                    ·
                      refine ⟨3034306610287944605486171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32365937176404742458519157 3034306610287944605486171)
                      ·
                        rfl

theorem cell23_5909291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 5].length) (baseStart_5909291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909291 prefixEnd_5909291 := by exact prefixLift 5909291
  have htrace : WordTrace (prefixWord ++ tailWord_5909291) baseStart_5909291 baseEnd_5909291 := by
    simpa [prefixWord, tailWord_5909291, baseEnd_5909291] using wordTrace_append hprefix tailTrace_5909291
  have hstable : (prefixWord ++ tailWord_5909291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909291).length < 2 ^ (prefixWord ++ tailWord_5909291).sum := by decide
  have hdescent : baseEnd_5909291 < baseStart_5909291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909302 : List Nat := [5, 1, 2, 2, 3, 1, 9]
def baseStart_5909302 : Nat := 118140960795 + 5909302 * 2 ^ 59
def prefixEnd_5909302 : Nat := 4983230072969 + 3 ^ 40 * 5909302 * 2
def baseEnd_5909302 : Nat := 37460645167594371141341

theorem tailTrace_5909302 : CollatzResearch.WordTrace tailWord_5909302 prefixEnd_5909302 37460645167594371141341 := by
  unfold tailWord_5909302
  simp only [CollatzResearch.WordTrace]
  refine ⟨13470621902350972329870635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143686633625077038185286773 13470621902350972329870635)
  ·
    refine ⟨20205932853526458494805953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13470621902350972329870635 20205932853526458494805953)
    ·
      refine ⟨15154449640144843871104465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20205932853526458494805953 15154449640144843871104465)
      ·
        refine ⟨11365837230108632903328349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15154449640144843871104465 11365837230108632903328349)
        ·
          refine ⟨4262188961290737338748131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11365837230108632903328349 4262188961290737338748131)
          ·
            refine ⟨6393283441936106008122197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4262188961290737338748131 6393283441936106008122197)
            ·
              refine ⟨37460645167594371141341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6393283441936106008122197 37460645167594371141341)
              ·
                rfl

theorem cell23_5909302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 9].length) (baseStart_5909302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909302 prefixEnd_5909302 := by exact prefixLift 5909302
  have htrace : WordTrace (prefixWord ++ tailWord_5909302) baseStart_5909302 baseEnd_5909302 := by
    simpa [prefixWord, tailWord_5909302, baseEnd_5909302] using wordTrace_append hprefix tailTrace_5909302
  have hstable : (prefixWord ++ tailWord_5909302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909302).length < 2 ^ (prefixWord ++ tailWord_5909302).sum := by decide
  have hdescent : baseEnd_5909302 < baseStart_5909302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909313 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_5909313 : Nat := 118140960795 + 5909313 * 2 ^ 59
def prefixEnd_5909313 : Nat := 4983230072969 + 3 ^ 40 * 5909313 * 2
def baseEnd_5909313 : Nat := 3034317906862343519411071

theorem tailTrace_5909313 : CollatzResearch.WordTrace tailWord_5909313 prefixEnd_5909313 3034317906862343519411071 := by
  unfold tailWord_5909313
  simp only [CollatzResearch.WordTrace]
  refine ⟨215530351640575706156580593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143686901093717137437720395 215530351640575706156580593)
  ·
    refine ⟨161647763730431779617435445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215530351640575706156580593 161647763730431779617435445)
    ·
      refine ⟨15154477849727979339134573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161647763730431779617435445 15154477849727979339134573)
      ·
        refine ⟨5682929193647992252175465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15154477849727979339134573 5682929193647992252175465)
        ·
          refine ⟨4262196895235994189131599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5682929193647992252175465 4262196895235994189131599)
          ·
            refine ⟨6393295342853991283697399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4262196895235994189131599 6393295342853991283697399)
            ·
              refine ⟨9589943014280986925546099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6393295342853991283697399 9589943014280986925546099)
              ·
                refine ⟨14384914521421480388319149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9589943014280986925546099 14384914521421480388319149)
                ·
                  refine ⟨5394342945533055145619681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14384914521421480388319149 5394342945533055145619681)
                  ·
                    refine ⟨4045757209149791359214761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5394342945533055145619681 4045757209149791359214761)
                    ·
                      refine ⟨3034317906862343519411071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4045757209149791359214761 3034317906862343519411071)
                      ·
                        rfl

theorem cell23_5909313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_5909313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909313 prefixEnd_5909313 := by exact prefixLift 5909313
  have htrace : WordTrace (prefixWord ++ tailWord_5909313) baseStart_5909313 baseEnd_5909313 := by
    simpa [prefixWord, tailWord_5909313, baseEnd_5909313] using wordTrace_append hprefix tailTrace_5909313
  have hstable : (prefixWord ++ tailWord_5909313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909313).length < 2 ^ (prefixWord ++ tailWord_5909313).sum := by decide
  have hdescent : baseEnd_5909313 < baseStart_5909313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909331 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 6]
def baseStart_5909331 : Nat := 118140960795 + 5909331 * 2 ^ 59
def prefixEnd_5909331 : Nat := 4983230072969 + 3 ^ 40 * 5909331 * 2
def baseEnd_5909331 : Nat := 3034327149514124448985987

theorem tailTrace_5909331 : CollatzResearch.WordTrace tailWord_5909331 prefixEnd_5909331 3034327149514124448985987 := by
  unfold tailWord_5909331
  simp only [CollatzResearch.WordTrace]
  refine ⟨215531008154510495230735847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143687338769673663487157231 215531008154510495230735847)
  ·
    refine ⟨323296512231765742846103771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215531008154510495230735847 323296512231765742846103771)
    ·
      refine ⟨484944768347648614269155657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323296512231765742846103771 484944768347648614269155657)
      ·
        refine ⟨363708576260736460701866743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484944768347648614269155657 363708576260736460701866743)
        ·
          refine ⟨545562864391104691052800115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363708576260736460701866743 545562864391104691052800115)
          ·
            refine ⟨818344296586657036579200173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545562864391104691052800115 818344296586657036579200173)
            ·
              refine ⟨306879111219996388717200065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 818344296586657036579200173 306879111219996388717200065)
              ·
                refine ⟨230159333414997291537900049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306879111219996388717200065 230159333414997291537900049)
                ·
                  refine ⟨172619500061247968653425037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230159333414997291537900049 172619500061247968653425037)
                  ·
                    refine ⟨64732312522967988245034389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172619500061247968653425037 64732312522967988245034389)
                    ·
                      refine ⟨3034327149514124448985987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64732312522967988245034389 3034327149514124448985987)
                      ·
                        rfl

theorem cell23_5909331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_5909331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909331 prefixEnd_5909331 := by exact prefixLift 5909331
  have htrace : WordTrace (prefixWord ++ tailWord_5909331) baseStart_5909331 baseEnd_5909331 := by
    simpa [prefixWord, tailWord_5909331, baseEnd_5909331] using wordTrace_append hprefix tailTrace_5909331
  have hstable : (prefixWord ++ tailWord_5909331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909331).length < 2 ^ (prefixWord ++ tailWord_5909331).sum := by decide
  have hdescent : baseEnd_5909331 < baseStart_5909331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909338 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5]
def baseStart_5909338 : Nat := 118140960795 + 5909338 * 2 ^ 59
def prefixEnd_5909338 : Nat := 4983230072969 + 3 ^ 40 * 5909338 * 2
def baseEnd_5909338 : Nat := 3034330743878705921598455

theorem tailTrace_5909338 : CollatzResearch.WordTrace tailWord_5909338 prefixEnd_5909338 3034330743878705921598455 := by
  unfold tailWord_5909338
  simp only [CollatzResearch.WordTrace]
  refine ⟨53882815866371283856560167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143687508976990090284160445 53882815866371283856560167)
  ·
    refine ⟨80824223799556925784840251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53882815866371283856560167 80824223799556925784840251)
    ·
      refine ⟨121236335699335388677260377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80824223799556925784840251 121236335699335388677260377)
      ·
        refine ⟨90927251774501541507945283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121236335699335388677260377 90927251774501541507945283)
        ·
          refine ⟨136390877661752312261917925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90927251774501541507945283 136390877661752312261917925)
          ·
            refine ⟨25573289561578558549109611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136390877661752312261917925 25573289561578558549109611)
            ·
              refine ⟨38359934342367837823664417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25573289561578558549109611 38359934342367837823664417)
              ·
                refine ⟨28769950756775878367748313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38359934342367837823664417 28769950756775878367748313)
                ·
                  refine ⟨21577463067581908775811235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28769950756775878367748313 21577463067581908775811235)
                  ·
                    refine ⟨32366194601372863163716853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21577463067581908775811235 32366194601372863163716853)
                    ·
                      refine ⟨3034330743878705921598455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32366194601372863163716853 3034330743878705921598455)
                      ·
                        rfl

theorem cell23_5909338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_5909338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909338 prefixEnd_5909338 := by exact prefixLift 5909338
  have htrace : WordTrace (prefixWord ++ tailWord_5909338) baseStart_5909338 baseEnd_5909338 := by
    simpa [prefixWord, tailWord_5909338, baseEnd_5909338] using wordTrace_append hprefix tailTrace_5909338
  have hstable : (prefixWord ++ tailWord_5909338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909338).length < 2 ^ (prefixWord ++ tailWord_5909338).sum := by decide
  have hdescent : baseEnd_5909338 < baseStart_5909338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909352 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 1, 4, 2]
def baseStart_5909352 : Nat := 118140960795 + 5909352 * 2 ^ 59
def prefixEnd_5909352 : Nat := 4983230072969 + 3 ^ 40 * 5909352 * 2
def baseEnd_5909352 : Nat := 3034337932607868866823391

theorem tailTrace_5909352 : CollatzResearch.WordTrace tailWord_5909352 prefixEnd_5909352 3034337932607868866823391 := by
  unfold tailWord_5909352
  simp only [CollatzResearch.WordTrace]
  refine ⟨107765887043717207908625155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143687849391622943878166873 107765887043717207908625155)
  ·
    refine ⟨161648830565575811862937733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107765887043717207908625155 161648830565575811862937733)
    ·
      refine ⟨30309155731045464724300825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161648830565575811862937733 30309155731045464724300825)
      ·
        refine ⟨22731866798284098543225619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30309155731045464724300825 22731866798284098543225619)
        ·
          refine ⟨34097800197426147814838429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22731866798284098543225619 34097800197426147814838429)
          ·
            refine ⟨12786675074034805430564411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34097800197426147814838429 12786675074034805430564411)
            ·
              refine ⟨19180012611052208145846617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12786675074034805430564411 19180012611052208145846617)
              ·
                refine ⟨14385009458289156109384963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19180012611052208145846617 14385009458289156109384963)
                ·
                  refine ⟨21577514187433734164077445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14385009458289156109384963 21577514187433734164077445)
                  ·
                    refine ⟨4045783910143825155764521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21577514187433734164077445 4045783910143825155764521)
                    ·
                      refine ⟨3034337932607868866823391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4045783910143825155764521 3034337932607868866823391)
                      ·
                        rfl

theorem cell23_5909352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_5909352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909352 prefixEnd_5909352 := by exact prefixLift 5909352
  have htrace : WordTrace (prefixWord ++ tailWord_5909352) baseStart_5909352 baseEnd_5909352 := by
    simpa [prefixWord, tailWord_5909352, baseEnd_5909352] using wordTrace_append hprefix tailTrace_5909352
  have hstable : (prefixWord ++ tailWord_5909352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909352).length < 2 ^ (prefixWord ++ tailWord_5909352).sum := by decide
  have hdescent : baseEnd_5909352 < baseStart_5909352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909369 : List Nat := [1, 2, 1, 3, 2, 4, 2, 2, 2, 2, 2]
def baseStart_5909369 : Nat := 118140960795 + 5909369 * 2 ^ 59
def prefixEnd_5909369 : Nat := 4983230072969 + 3 ^ 40 * 5909369 * 2
def baseEnd_5909369 : Nat := 3034346661778995300310813

theorem tailTrace_5909369 : CollatzResearch.WordTrace tailWord_5909369 prefixEnd_5909369 3034346661778995300310813 := by
  unfold tailWord_5909369
  simp only [CollatzResearch.WordTrace]
  refine ⟨215532394128372827720619161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143688262752248551813746107 215532394128372827720619161)
  ·
    refine ⟨161649295596279620790464371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215532394128372827720619161 161649295596279620790464371)
    ·
      refine ⟨242473943394419431185696557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161649295596279620790464371 242473943394419431185696557)
      ·
        refine ⟨90927728772907286694636209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242473943394419431185696557 90927728772907286694636209)
        ·
          refine ⟨68195796579680465020977157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90927728772907286694636209 68195796579680465020977157)
          ·
            refine ⟨12786711858690087191433217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68195796579680465020977157 12786711858690087191433217)
            ·
              refine ⟨9590033894017565393574913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12786711858690087191433217 9590033894017565393574913)
              ·
                refine ⟨7192525420513174045181185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9590033894017565393574913 7192525420513174045181185)
                ·
                  refine ⟨5394394065384880533885889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7192525420513174045181185 5394394065384880533885889)
                  ·
                    refine ⟨4045795549038660400414417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5394394065384880533885889 4045795549038660400414417)
                    ·
                      refine ⟨3034346661778995300310813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4045795549038660400414417 3034346661778995300310813)
                      ·
                        rfl

theorem cell23_5909369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_5909369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909369 prefixEnd_5909369 := by exact prefixLift 5909369
  have htrace : WordTrace (prefixWord ++ tailWord_5909369) baseStart_5909369 baseEnd_5909369 := by
    simpa [prefixWord, tailWord_5909369, baseEnd_5909369] using wordTrace_append hprefix tailTrace_5909369
  have hstable : (prefixWord ++ tailWord_5909369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909369).length < 2 ^ (prefixWord ++ tailWord_5909369).sum := by decide
  have hdescent : baseEnd_5909369 < baseStart_5909369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909385 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 2, 3, 3]
def baseStart_5909385 : Nat := 118140960795 + 5909385 * 2 ^ 59
def prefixEnd_5909385 : Nat := 4983230072969 + 3 ^ 40 * 5909385 * 2
def baseEnd_5909385 : Nat := 3034354877469467237710739

theorem tailTrace_5909385 : CollatzResearch.WordTrace tailWord_5909385 prefixEnd_5909385 3034354877469467237710739 := by
  unfold tailWord_5909385
  simp only [CollatzResearch.WordTrace]
  refine ⟨215532977696314862453201609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143688651797543241635467739 215532977696314862453201609)
  ·
    refine ⟨161649733272236146839901207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215532977696314862453201609 161649733272236146839901207)
    ·
      refine ⟨242474599908354220259851811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161649733272236146839901207 242474599908354220259851811)
      ·
        refine ⟨363711899862531330389777717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242474599908354220259851811 363711899862531330389777717)
        ·
          refine ⟨34097990612112312224041661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 363711899862531330389777717 34097990612112312224041661)
          ·
            refine ⟨12786746479542117084015623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34097990612112312224041661 12786746479542117084015623)
            ·
              refine ⟨19180119719313175626023435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12786746479542117084015623 19180119719313175626023435)
              ·
                refine ⟨28770179578969763439035153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19180119719313175626023435 28770179578969763439035153)
                ·
                  refine ⟨21577634684227322579276365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28770179578969763439035153 21577634684227322579276365)
                  ·
                    refine ⟨8091613006585245967228637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21577634684227322579276365 8091613006585245967228637)
                    ·
                      refine ⟨3034354877469467237710739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8091613006585245967228637 3034354877469467237710739)
                      ·
                        rfl

theorem cell23_5909385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 3, 3].length) (baseStart_5909385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909385 prefixEnd_5909385 := by exact prefixLift 5909385
  have htrace : WordTrace (prefixWord ++ tailWord_5909385) baseStart_5909385 baseEnd_5909385 := by
    simpa [prefixWord, tailWord_5909385, baseEnd_5909385] using wordTrace_append hprefix tailTrace_5909385
  have hstable : (prefixWord ++ tailWord_5909385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909385).length < 2 ^ (prefixWord ++ tailWord_5909385).sum := by decide
  have hdescent : baseEnd_5909385 < baseStart_5909385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909388 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 4, 5]
def baseStart_5909388 : Nat := 118140960795 + 5909388 * 2 ^ 59
def prefixEnd_5909388 : Nat := 4983230072969 + 3 ^ 40 * 5909388 * 2
def baseEnd_5909388 : Nat := 1011452139303810241991075

theorem tailTrace_5909388 : CollatzResearch.WordTrace tailWord_5909388 prefixEnd_5909388 1011452139303810241991075 := by
  unfold tailWord_5909388
  simp only [CollatzResearch.WordTrace]
  refine ⟨107766543557651996982780409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143688724743535995977040545 107766543557651996982780409)
  ·
    refine ⟨80824907668238997737085307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107766543557651996982780409 80824907668238997737085307)
    ·
      refine ⟨121237361502358496605627961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80824907668238997737085307 121237361502358496605627961)
      ·
        refine ⟨90928021126768872454220971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121237361502358496605627961 90928021126768872454220971)
        ·
          refine ⟨136392031690153308681331457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90928021126768872454220971 136392031690153308681331457)
          ·
            refine ⟨102294023767614981510998593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136392031690153308681331457 102294023767614981510998593)
            ·
              refine ⟨76720517825711236133248945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102294023767614981510998593 76720517825711236133248945)
              ·
                refine ⟨57540388369283427099936709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76720517825711236133248945 57540388369283427099936709)
                ·
                  refine ⟨10788822819240642581238133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57540388369283427099936709 10788822819240642581238133)
                  ·
                    refine ⟨1011452139303810241991075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10788822819240642581238133 1011452139303810241991075)
                    ·
                      rfl

theorem cell23_5909388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_5909388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909388 prefixEnd_5909388 := by exact prefixLift 5909388
  have htrace : WordTrace (prefixWord ++ tailWord_5909388) baseStart_5909388 baseEnd_5909388 := by
    simpa [prefixWord, tailWord_5909388, baseEnd_5909388] using wordTrace_append hprefix tailTrace_5909388
  have hstable : (prefixWord ++ tailWord_5909388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909388).length < 2 ^ (prefixWord ++ tailWord_5909388).sum := by decide
  have hdescent : baseEnd_5909388 < baseStart_5909388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909486 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 3, 4]
def baseStart_5909486 : Nat := 118140960795 + 5909486 * 2 ^ 59
def prefixEnd_5909486 : Nat := 4983230072969 + 3 ^ 40 * 5909486 * 2
def baseEnd_5909486 : Nat := 1011468913005190447515925

theorem tailTrace_5909486 : CollatzResearch.WordTrace tailWord_5909486 prefixEnd_5909486 1011468913005190447515925 := by
  unfold tailWord_5909486
  simp only [CollatzResearch.WordTrace]
  refine ⟨26942082683618619587828539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143691107645965971135085541 26942082683618619587828539)
  ·
    refine ⟨40413124025427929381742809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26942082683618619587828539 40413124025427929381742809)
    ·
      refine ⟨30309843019070947036307107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40413124025427929381742809 30309843019070947036307107)
      ·
        refine ⟨45464764528606420554460661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30309843019070947036307107 45464764528606420554460661)
        ·
          refine ⟨4262321674556851926980687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45464764528606420554460661 4262321674556851926980687)
          ·
            refine ⟨6393482511835277890471031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4262321674556851926980687 6393482511835277890471031)
            ·
              refine ⟨9590223767752916835706547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6393482511835277890471031 9590223767752916835706547)
              ·
                refine ⟨14385335651629375253559821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9590223767752916835706547 14385335651629375253559821)
                ·
                  refine ⟨5394500869361015720084933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14385335651629375253559821 5394500869361015720084933)
                  ·
                    refine ⟨1011468913005190447515925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5394500869361015720084933 1011468913005190447515925)
                    ·
                      rfl

theorem cell23_5909486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_5909486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909486 prefixEnd_5909486 := by exact prefixLift 5909486
  have htrace : WordTrace (prefixWord ++ tailWord_5909486) baseStart_5909486 baseEnd_5909486 := by
    simpa [prefixWord, tailWord_5909486, baseEnd_5909486] using wordTrace_append hprefix tailTrace_5909486
  have hstable : (prefixWord ++ tailWord_5909486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909486).length < 2 ^ (prefixWord ++ tailWord_5909486).sum := by decide
  have hdescent : baseEnd_5909486 < baseStart_5909486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909488 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 7]
def baseStart_5909488 : Nat := 118140960795 + 5909488 * 2 ^ 59
def prefixEnd_5909488 : Nat := 4983230072969 + 3 ^ 40 * 5909488 * 2
def baseEnd_5909488 : Nat := 3034407765976880334722765

theorem tailTrace_5909488 : CollatzResearch.WordTrace tailWord_5909488 prefixEnd_5909488 3034407765976880334722765 := by
  unfold tailWord_5909488
  simp only [CollatzResearch.WordTrace]
  refine ⟨107768367207470855522100559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143691156276627807362800745 107768367207470855522100559)
  ·
    refine ⟨161652550811206283283150839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107768367207470855522100559 161652550811206283283150839)
    ·
      refine ⟨242478826216809424924726259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161652550811206283283150839 242478826216809424924726259)
      ·
        refine ⟨363718239325214137387089389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242478826216809424924726259 363718239325214137387089389)
        ·
          refine ⟨136394339746955301520158521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363718239325214137387089389 136394339746955301520158521)
          ·
            refine ⟨102295754810216476140118891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136394339746955301520158521 102295754810216476140118891)
            ·
              refine ⟨153443632215324714210178337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102295754810216476140118891 153443632215324714210178337)
              ·
                refine ⟨115082724161493535657633753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153443632215324714210178337 115082724161493535657633753)
                ·
                  refine ⟨86312043121120151743225315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115082724161493535657633753 86312043121120151743225315)
                  ·
                    refine ⟨129468064681680227614837973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86312043121120151743225315 129468064681680227614837973)
                    ·
                      refine ⟨3034407765976880334722765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129468064681680227614837973 3034407765976880334722765)
                      ·
                        rfl

theorem cell23_5909488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_5909488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909488 prefixEnd_5909488 := by exact prefixLift 5909488
  have htrace : WordTrace (prefixWord ++ tailWord_5909488) baseStart_5909488 baseEnd_5909488 := by
    simpa [prefixWord, tailWord_5909488, baseEnd_5909488] using wordTrace_append hprefix tailTrace_5909488
  have hstable : (prefixWord ++ tailWord_5909488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909488).length < 2 ^ (prefixWord ++ tailWord_5909488).sum := by decide
  have hdescent : baseEnd_5909488 < baseStart_5909488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909512 : List Nat := [2, 1, 3, 2, 1, 3, 3, 2, 1, 5]
def baseStart_5909512 : Nat := 118140960795 + 5909512 * 2 ^ 59
def prefixEnd_5909512 : Nat := 4983230072969 + 3 ^ 40 * 5909512 * 2
def baseEnd_5909512 : Nat := 1011473363170862746940885

theorem tailTrace_5909512 : CollatzResearch.WordTrace tailWord_5909512 prefixEnd_5909512 1011473363170862746940885 := by
  unfold tailWord_5909512
  simp only [CollatzResearch.WordTrace]
  refine ⟨107768804883427381571537395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143691739844569842095383193 107768804883427381571537395)
  ·
    refine ⟨161653207325141072357306093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107768804883427381571537395 161653207325141072357306093)
    ·
      refine ⟨60619952746927902133989785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161653207325141072357306093 60619952746927902133989785)
      ·
        refine ⟨45464964560195926600492339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60619952746927902133989785 45464964560195926600492339)
        ·
          refine ⟨68197446840293889900738509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45464964560195926600492339 68197446840293889900738509)
          ·
            refine ⟨25574042565110208712776941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68197446840293889900738509 25574042565110208712776941)
            ·
              refine ⟨9590265961916328267291353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25574042565110208712776941 9590265961916328267291353)
              ·
                refine ⟨7192699471437246200468515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9590265961916328267291353 7192699471437246200468515)
                ·
                  refine ⟨10789049207155869300702773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7192699471437246200468515 10789049207155869300702773)
                  ·
                    refine ⟨1011473363170862746940885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10789049207155869300702773 1011473363170862746940885)
                    ·
                      rfl

theorem cell23_5909512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_5909512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909512 prefixEnd_5909512 := by exact prefixLift 5909512
  have htrace : WordTrace (prefixWord ++ tailWord_5909512) baseStart_5909512 baseEnd_5909512 := by
    simpa [prefixWord, tailWord_5909512, baseEnd_5909512] using wordTrace_append hprefix tailTrace_5909512
  have hstable : (prefixWord ++ tailWord_5909512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909512).length < 2 ^ (prefixWord ++ tailWord_5909512).sum := by decide
  have hdescent : baseEnd_5909512 < baseStart_5909512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909525 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 3, 6]
def baseStart_5909525 : Nat := 118140960795 + 5909525 * 2 ^ 59
def prefixEnd_5909525 : Nat := 4983230072969 + 3 ^ 40 * 5909525 * 2
def baseEnd_5909525 : Nat := 1011475588253698896653365

theorem tailTrace_5909525 : CollatzResearch.WordTrace tailWord_5909525 prefixEnd_5909525 1011475588253698896653365 := by
  unfold tailWord_5909525
  simp only [CollatzResearch.WordTrace]
  refine ⟨215538083915807666363298029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143692055943871777575532019 215538083915807666363298029)
  ·
    refine ⟨80826781468427874886236761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215538083915807666363298029 80826781468427874886236761)
    ·
      refine ⟨60620086101320906164677571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80826781468427874886236761 60620086101320906164677571)
      ·
        refine ⟨90930129151981359247016357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60620086101320906164677571 90930129151981359247016357)
        ·
          refine ⟨17049399215996504858815567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90930129151981359247016357 17049399215996504858815567)
          ·
            refine ⟨25574098823994757288223351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17049399215996504858815567 25574098823994757288223351)
            ·
              refine ⟨38361148235992135932335027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25574098823994757288223351 38361148235992135932335027)
              ·
                refine ⟨57541722353988203898502541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38361148235992135932335027 57541722353988203898502541)
                ·
                  refine ⟨21578145882745576461938453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57541722353988203898502541 21578145882745576461938453)
                  ·
                    refine ⟨1011475588253698896653365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21578145882745576461938453 1011475588253698896653365)
                    ·
                      rfl

theorem cell23_5909525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_5909525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909525 prefixEnd_5909525 := by exact prefixLift 5909525
  have htrace : WordTrace (prefixWord ++ tailWord_5909525) baseStart_5909525 baseEnd_5909525 := by
    simpa [prefixWord, tailWord_5909525, baseEnd_5909525] using wordTrace_append hprefix tailTrace_5909525
  have hstable : (prefixWord ++ tailWord_5909525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909525).length < 2 ^ (prefixWord ++ tailWord_5909525).sum := by decide
  have hdescent : baseEnd_5909525 < baseStart_5909525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909543 : List Nat := [1, 1, 7, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_5909543 : Nat := 118140960795 + 5909543 * 2 ^ 59
def prefixEnd_5909543 : Nat := 4983230072969 + 3 ^ 40 * 5909543 * 2
def baseEnd_5909543 : Nat := 3034436007412877619535013

theorem tailTrace_5909543 : CollatzResearch.WordTrace tailWord_5909543 prefixEnd_5909543 3034436007412877619535013 := by
  unfold tailWord_5909543
  simp only [CollatzResearch.WordTrace]
  refine ⟨215538740429742455437453283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143692493619828303624968855 215538740429742455437453283)
  ·
    refine ⟨323308110644613683156179925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215538740429742455437453283 323308110644613683156179925)
    ·
      refine ⟨7577533843233133198972967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 323308110644613683156179925 7577533843233133198972967)
      ·
        refine ⟨11366300764849699798459451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7577533843233133198972967 11366300764849699798459451)
        ·
          refine ⟨17049451147274549697689177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11366300764849699798459451 17049451147274549697689177)
          ·
            refine ⟨12787088360455912273266883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17049451147274549697689177 12787088360455912273266883)
            ·
              refine ⟨19180632540683868409900325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12787088360455912273266883 19180632540683868409900325)
              ·
                refine ⟨3596368601378225326856311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19180632540683868409900325 3596368601378225326856311)
                ·
                  refine ⟨5394552902067337990284467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3596368601378225326856311 5394552902067337990284467)
                  ·
                    refine ⟨8091829353101006985426701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5394552902067337990284467 8091829353101006985426701)
                    ·
                      refine ⟨3034436007412877619535013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8091829353101006985426701 3034436007412877619535013)
                      ·
                        rfl

theorem cell23_5909543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_5909543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909543 prefixEnd_5909543 := by exact prefixLift 5909543
  have htrace : WordTrace (prefixWord ++ tailWord_5909543) baseStart_5909543 baseEnd_5909543 := by
    simpa [prefixWord, tailWord_5909543, baseEnd_5909543] using wordTrace_append hprefix tailTrace_5909543
  have hstable : (prefixWord ++ tailWord_5909543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909543).length < 2 ^ (prefixWord ++ tailWord_5909543).sum := by decide
  have hdescent : baseEnd_5909543 < baseStart_5909543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909566 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 5, 2, 2]
def baseStart_5909566 : Nat := 118140960795 + 5909566 * 2 ^ 59
def prefixEnd_5909566 : Nat := 4983230072969 + 3 ^ 40 * 5909566 * 2
def baseEnd_5909566 : Nat := 3034447817467931029547407

theorem tailTrace_5909566 : CollatzResearch.WordTrace tailWord_5909566 prefixEnd_5909566 3034447817467931029547407 := by
  unfold tailWord_5909566
  simp only [CollatzResearch.WordTrace]
  refine ⟨26942447413582391295692569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143693052872439420243693701 26942447413582391295692569)
  ·
    refine ⟨20206835560186793471769427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26942447413582391295692569 20206835560186793471769427)
    ·
      refine ⟨30310253340280190207654141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20206835560186793471769427 30310253340280190207654141)
      ·
        refine ⟨11366345002605071327870303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30310253340280190207654141 11366345002605071327870303)
        ·
          refine ⟨17049517503907606991805455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11366345002605071327870303 17049517503907606991805455)
          ·
            refine ⟨25574276255861410487708183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17049517503907606991805455 25574276255861410487708183)
            ·
              refine ⟨38361414383792115731562275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25574276255861410487708183 38361414383792115731562275)
              ·
                refine ⟨57542121575688173597343413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38361414383792115731562275 57542121575688173597343413)
                ·
                  refine ⟨5394573897720766274750945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57542121575688173597343413 5394573897720766274750945)
                  ·
                    refine ⟨4045930423290574706063209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5394573897720766274750945 4045930423290574706063209)
                    ·
                      refine ⟨3034447817467931029547407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4045930423290574706063209 3034447817467931029547407)
                      ·
                        rfl

theorem cell23_5909566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_5909566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909566 prefixEnd_5909566 := by exact prefixLift 5909566
  have htrace : WordTrace (prefixWord ++ tailWord_5909566) baseStart_5909566 baseEnd_5909566 := by
    simpa [prefixWord, tailWord_5909566, baseEnd_5909566] using wordTrace_append hprefix tailTrace_5909566
  have hstable : (prefixWord ++ tailWord_5909566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909566).length < 2 ^ (prefixWord ++ tailWord_5909566).sum := by decide
  have hdescent : baseEnd_5909566 < baseStart_5909566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909582 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3]
def baseStart_5909582 : Nat := 118140960795 + 5909582 * 2 ^ 59
def prefixEnd_5909582 : Nat := 4983230072969 + 3 ^ 40 * 5909582 * 2
def baseEnd_5909582 : Nat := 3034456033158402966947333

theorem tailTrace_5909582 : CollatzResearch.WordTrace tailWord_5909582 prefixEnd_5909582 3034456033158402966947333 := by
  unfold tailWord_5909582
  simp only [CollatzResearch.WordTrace]
  refine ⟨26942520359575145637265375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143693441917734110065415333 26942520359575145637265375)
  ·
    refine ⟨40413780539362718455898063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26942520359575145637265375 40413780539362718455898063)
    ·
      refine ⟨60620670809044077683847095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40413780539362718455898063 60620670809044077683847095)
      ·
        refine ⟨90931006213566116525770643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60620670809044077683847095 90931006213566116525770643)
        ·
          refine ⟨136396509320349174788655965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90931006213566116525770643 136396509320349174788655965)
          ·
            refine ⟨51148690995130940545745987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136396509320349174788655965 51148690995130940545745987)
            ·
              refine ⟨76723036492696410818618981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51148690995130940545745987 76723036492696410818618981)
              ·
                refine ⟨14385569342380577028491059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76723036492696410818618981 14385569342380577028491059)
                ·
                  refine ⟨21578354013570865542736589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14385569342380577028491059 21578354013570865542736589)
                  ·
                    refine ⟨8091882755089074578526221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21578354013570865542736589 8091882755089074578526221)
                    ·
                      refine ⟨3034456033158402966947333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8091882755089074578526221 3034456033158402966947333)
                      ·
                        rfl

theorem cell23_5909582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_5909582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909582 prefixEnd_5909582 := by exact prefixLift 5909582
  have htrace : WordTrace (prefixWord ++ tailWord_5909582) baseStart_5909582 baseEnd_5909582 := by
    simpa [prefixWord, tailWord_5909582, baseEnd_5909582] using wordTrace_append hprefix tailTrace_5909582
  have hstable : (prefixWord ++ tailWord_5909582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909582).length < 2 ^ (prefixWord ++ tailWord_5909582).sum := by decide
  have hdescent : baseEnd_5909582 < baseStart_5909582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909586 : List Nat := [3, 2, 2, 1, 3, 1, 4, 1, 1, 2, 3]
def baseStart_5909586 : Nat := 118140960795 + 5909586 * 2 ^ 59
def prefixEnd_5909586 : Nat := 4983230072969 + 3 ^ 40 * 5909586 * 2
def baseEnd_5909586 : Nat := 3034458087081020951297315

theorem tailTrace_5909586 : CollatzResearch.WordTrace tailWord_5909586 prefixEnd_5909586 3034458087081020951297315 := by
  unfold tailWord_5909586
  simp only [CollatzResearch.WordTrace]
  refine ⟨53885077192146668445317153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143693539179057782520845741 53885077192146668445317153)
  ·
    refine ⟨40413807894110001333987865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53885077192146668445317153 40413807894110001333987865)
    ·
      refine ⟨30310355920582501000490899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40413807894110001333987865 30310355920582501000490899)
      ·
        refine ⟨45465533880873751500736349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30310355920582501000490899 45465533880873751500736349)
        ·
          refine ⟨17049575205327656812776131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45465533880873751500736349 17049575205327656812776131)
          ·
            refine ⟨25574362807991485219164197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17049575205327656812776131 25574362807991485219164197)
            ·
              refine ⟨4795193026498403478593287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25574362807991485219164197 4795193026498403478593287)
              ·
                refine ⟨7192789539747605217889931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4795193026498403478593287 7192789539747605217889931)
                ·
                  refine ⟨10789184309621407826834897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7192789539747605217889931 10789184309621407826834897)
                  ·
                    refine ⟨8091888232216055870126173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10789184309621407826834897 8091888232216055870126173)
                    ·
                      refine ⟨3034458087081020951297315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8091888232216055870126173 3034458087081020951297315)
                      ·
                        rfl

theorem cell23_5909586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_5909586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909586 prefixEnd_5909586 := by exact prefixLift 5909586
  have htrace : WordTrace (prefixWord ++ tailWord_5909586) baseStart_5909586 baseEnd_5909586 := by
    simpa [prefixWord, tailWord_5909586, baseEnd_5909586] using wordTrace_append hprefix tailTrace_5909586
  have hstable : (prefixWord ++ tailWord_5909586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909586).length < 2 ^ (prefixWord ++ tailWord_5909586).sum := by decide
  have hdescent : baseEnd_5909586 < baseStart_5909586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909615 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 2, 6]
def baseStart_5909615 : Nat := 118140960795 + 5909615 * 2 ^ 59
def prefixEnd_5909615 : Nat := 4983230072969 + 3 ^ 40 * 5909615 * 2
def baseEnd_5909615 : Nat := 1011490992673333779278227

theorem tailTrace_5909615 : CollatzResearch.WordTrace tailWord_5909615 prefixEnd_5909615 1011490992673333779278227 := by
  unfold tailWord_5909615
  simp only [CollatzResearch.WordTrace]
  refine ⟨215541366485481611734074299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143694244323654407822716199 215541366485481611734074299)
  ·
    refine ⟨323312049728222417601111449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215541366485481611734074299 323312049728222417601111449)
    ·
      refine ⟨242484037296166813200833587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323312049728222417601111449 242484037296166813200833587)
      ·
        refine ⟨363726055944250219801250381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242484037296166813200833587 363726055944250219801250381)
        ·
          refine ⟨136397270979093832425468893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363726055944250219801250381 136397270979093832425468893)
          ·
            refine ⟨51148976617160187159550835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136397270979093832425468893 51148976617160187159550835)
            ·
              refine ⟨76723464925740280739326253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51148976617160187159550835 76723464925740280739326253)
              ·
                refine ⟨28771299347152605277247345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76723464925740280739326253 28771299347152605277247345)
                ·
                  refine ⟨21578474510364453957935509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28771299347152605277247345 21578474510364453957935509)
                  ·
                    refine ⟨1011490992673333779278227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21578474510364453957935509 1011490992673333779278227)
                    ·
                      rfl

theorem cell23_5909615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 6].length) (baseStart_5909615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909615 prefixEnd_5909615 := by exact prefixLift 5909615
  have htrace : WordTrace (prefixWord ++ tailWord_5909615) baseStart_5909615 baseEnd_5909615 := by
    simpa [prefixWord, tailWord_5909615, baseEnd_5909615] using wordTrace_append hprefix tailTrace_5909615
  have hstable : (prefixWord ++ tailWord_5909615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909615).length < 2 ^ (prefixWord ++ tailWord_5909615).sum := by decide
  have hdescent : baseEnd_5909615 < baseStart_5909615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909616 : List Nat := [2, 1, 1, 1, 5, 1, 5, 1, 2, 1, 3]
def baseStart_5909616 : Nat := 118140960795 + 5909616 * 2 ^ 59
def prefixEnd_5909616 : Nat := 4983230072969 + 3 ^ 40 * 5909616 * 2
def baseEnd_5909616 : Nat := 3034473491500655833922177

theorem tailTrace_5909616 : CollatzResearch.WordTrace tailWord_5909616 prefixEnd_5909616 3034473491500655833922177 := by
  unfold tailWord_5909616
  simp only [CollatzResearch.WordTrace]
  refine ⟨107770701479238994452430351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143694268638985325936573801 107770701479238994452430351)
  ·
    refine ⟨161656052218858491678645527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107770701479238994452430351 161656052218858491678645527)
    ·
      refine ⟨242484078328287737517968291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161656052218858491678645527 242484078328287737517968291)
      ·
        refine ⟨363726117492431606276952437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242484078328287737517968291 363726117492431606276952437)
        ·
          refine ⟨34099323514915463088464291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 363726117492431606276952437 34099323514915463088464291)
          ·
            refine ⟨51148985272373194632696437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34099323514915463088464291 51148985272373194632696437)
            ·
              refine ⟨4795217369284986996815291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51148985272373194632696437 4795217369284986996815291)
              ·
                refine ⟨7192826053927480495222937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4795217369284986996815291 7192826053927480495222937)
                ·
                  refine ⟨5394619540445610371417203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7192826053927480495222937 5394619540445610371417203)
                  ·
                    refine ⟨8091929310668415557125805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5394619540445610371417203 8091929310668415557125805)
                    ·
                      refine ⟨3034473491500655833922177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8091929310668415557125805 3034473491500655833922177)
                      ·
                        rfl

theorem cell23_5909616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 2, 1, 3].length) (baseStart_5909616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909616 prefixEnd_5909616 := by exact prefixLift 5909616
  have htrace : WordTrace (prefixWord ++ tailWord_5909616) baseStart_5909616 baseEnd_5909616 := by
    simpa [prefixWord, tailWord_5909616, baseEnd_5909616] using wordTrace_append hprefix tailTrace_5909616
  have hstable : (prefixWord ++ tailWord_5909616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909616).length < 2 ^ (prefixWord ++ tailWord_5909616).sum := by decide
  have hdescent : baseEnd_5909616 < baseStart_5909616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909642 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_5909642 : Nat := 118140960795 + 5909642 * 2 ^ 59
def prefixEnd_5909642 : Nat := 4983230072969 + 3 ^ 40 * 5909642 * 2
def baseEnd_5909642 : Nat := 3034486841997672732197057

theorem tailTrace_5909642 : CollatzResearch.WordTrace tailWord_5909642 prefixEnd_5909642 3034486841997672732197057 := by
  unfold tailWord_5909642
  simp only [CollatzResearch.WordTrace]
  refine ⟨53885587814095948836326795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143694900837589196896871453 53885587814095948836326795)
  ·
    refine ⟨80828381721143923254490193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53885587814095948836326795 80828381721143923254490193)
    ·
      refine ⟨60621286290857942440867645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80828381721143923254490193 60621286290857942440867645)
      ·
        refine ⟨22732982359071728415325367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60621286290857942440867645 22732982359071728415325367)
        ·
          refine ⟨34099473538607592622988051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22732982359071728415325367 34099473538607592622988051)
          ·
            refine ⟨51149210307911388934482077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34099473538607592622988051 51149210307911388934482077)
            ·
              refine ⟨19180953865466770850430779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51149210307911388934482077 19180953865466770850430779)
              ·
                refine ⟨28771430798200156275646169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19180953865466770850430779 28771430798200156275646169)
                ·
                  refine ⟨21578573098650117206734627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28771430798200156275646169 21578573098650117206734627)
                  ·
                    refine ⟨32367859647975175810101941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21578573098650117206734627 32367859647975175810101941)
                    ·
                      refine ⟨3034486841997672732197057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32367859647975175810101941 3034486841997672732197057)
                      ·
                        rfl

theorem cell23_5909642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_5909642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909642 prefixEnd_5909642 := by exact prefixLift 5909642
  have htrace : WordTrace (prefixWord ++ tailWord_5909642) baseStart_5909642 baseEnd_5909642 := by
    simpa [prefixWord, tailWord_5909642, baseEnd_5909642] using wordTrace_append hprefix tailTrace_5909642
  have hstable : (prefixWord ++ tailWord_5909642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909642).length < 2 ^ (prefixWord ++ tailWord_5909642).sum := by decide
  have hdescent : baseEnd_5909642 < baseStart_5909642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909656 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 4, 2, 2]
def baseStart_5909656 : Nat := 118140960795 + 5909656 * 2 ^ 59
def prefixEnd_5909656 : Nat := 4983230072969 + 3 ^ 40 * 5909656 * 2
def baseEnd_5909656 : Nat := 3034494030726835677421993

theorem tailTrace_5909656 : CollatzResearch.WordTrace tailWord_5909656 prefixEnd_5909656 3034494030726835677421993 := by
  unfold tailWord_5909656
  simp only [CollatzResearch.WordTrace]
  refine ⟨107771430939166537868158411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143695241252222050490877881 107771430939166537868158411)
  ·
    refine ⟨161657146408749806802237617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107771430939166537868158411 161657146408749806802237617)
    ·
      refine ⟨121242859806562355101678213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161657146408749806802237617 121242859806562355101678213)
      ·
        refine ⟨22733036213730441581564665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121242859806562355101678213 22733036213730441581564665)
        ·
          refine ⟨17049777160297831186173499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22733036213730441581564665 17049777160297831186173499)
          ·
            refine ⟨25574665740446746779260249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17049777160297831186173499 25574665740446746779260249)
            ·
              refine ⟨19180999305335060084445187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25574665740446746779260249 19180999305335060084445187)
              ·
                refine ⟨28771498958002590126667781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19180999305335060084445187 28771498958002590126667781)
                ·
                  refine ⟨5394656054625485648750209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28771498958002590126667781 5394656054625485648750209)
                  ·
                    refine ⟨4045992040969114236562657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5394656054625485648750209 4045992040969114236562657)
                    ·
                      refine ⟨3034494030726835677421993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4045992040969114236562657 3034494030726835677421993)
                      ·
                        rfl

theorem cell23_5909656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_5909656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909656 prefixEnd_5909656 := by exact prefixLift 5909656
  have htrace : WordTrace (prefixWord ++ tailWord_5909656) baseStart_5909656 baseEnd_5909656 := by
    simpa [prefixWord, tailWord_5909656, baseEnd_5909656] using wordTrace_append hprefix tailTrace_5909656
  have hstable : (prefixWord ++ tailWord_5909656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909656).length < 2 ^ (prefixWord ++ tailWord_5909656).sum := by decide
  have hdescent : baseEnd_5909656 < baseStart_5909656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909705 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 4, 8]
def baseStart_5909705 : Nat := 118140960795 + 5909705 * 2 ^ 59
def prefixEnd_5909705 : Nat := 4983230072969 + 3 ^ 40 * 5909705 * 2
def baseEnd_5909705 : Nat := 1011506397092968661903089

theorem tailTrace_5909705 : CollatzResearch.WordTrace tailWord_5909705 prefixEnd_5909705 1011506397092968661903089 := by
  unfold tailWord_5909705
  simp only [CollatzResearch.WordTrace]
  refine ⟨215544649055155557104850569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143696432703437038069900379 215544649055155557104850569)
  ·
    refine ⟨161658486791366667828637927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215544649055155557104850569 161658486791366667828637927)
    ·
      refine ⟨242487730187050001742956891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161658486791366667828637927 242487730187050001742956891)
      ·
        refine ⟨363731595280575002614435337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242487730187050001742956891 363731595280575002614435337)
        ·
          refine ⟨272798696460431251960826503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363731595280575002614435337 272798696460431251960826503)
          ·
            refine ⟨409198044690646877941239755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272798696460431251960826503 409198044690646877941239755)
            ·
              refine ⟨613797067035970316911859633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409198044690646877941239755 613797067035970316911859633)
              ·
                refine ⟨460347800276977737683894725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 613797067035970316911859633 460347800276977737683894725)
                ·
                  refine ⟨86315212551933325815730261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 460347800276977737683894725 86315212551933325815730261)
                  ·
                    refine ⟨1011506397092968661903089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86315212551933325815730261 1011506397092968661903089)
                    ·
                      rfl

theorem cell23_5909705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 8].length) (baseStart_5909705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909705 prefixEnd_5909705 := by exact prefixLift 5909705
  have htrace : WordTrace (prefixWord ++ tailWord_5909705) baseStart_5909705 baseEnd_5909705 := by
    simpa [prefixWord, tailWord_5909705, baseEnd_5909705] using wordTrace_append hprefix tailTrace_5909705
  have hstable : (prefixWord ++ tailWord_5909705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909705).length < 2 ^ (prefixWord ++ tailWord_5909705).sum := by decide
  have hdescent : baseEnd_5909705 < baseStart_5909705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909729 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 1, 6, 2]
def baseStart_5909729 : Nat := 118140960795 + 5909729 * 2 ^ 59
def prefixEnd_5909729 : Nat := 4983230072969 + 3 ^ 40 * 5909729 * 2
def baseEnd_5909729 : Nat := 3034531514814613891809157

theorem tailTrace_5909729 : CollatzResearch.WordTrace tailWord_5909729 prefixEnd_5909729 3034531514814613891809157 := by
  unfold tailWord_5909729
  simp only [CollatzResearch.WordTrace]
  refine ⟨215545524407068609203724241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143697016271379072802482827 215545524407068609203724241)
  ·
    refine ⟨161659143305301456902793181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215545524407068609203724241 161659143305301456902793181)
    ·
      refine ⟨60622178739488046338547443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161659143305301456902793181 60622178739488046338547443)
      ·
        refine ⟨90933268109232069507821165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60622178739488046338547443 90933268109232069507821165)
        ·
          refine ⟨34099975540962026065432937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90933268109232069507821165 34099975540962026065432937)
          ·
            refine ⟨25574981655721519549074703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34099975540962026065432937 25574981655721519549074703)
            ·
              refine ⟨38362472483582279323612055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25574981655721519549074703 38362472483582279323612055)
              ·
                refine ⟨57543708725373418985418083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38362472483582279323612055 57543708725373418985418083)
                ·
                  refine ⟨86315563088060128478127125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57543708725373418985418083 86315563088060128478127125)
                  ·
                    refine ⟨4046042019752818522412209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86315563088060128478127125 4046042019752818522412209)
                    ·
                      refine ⟨3034531514814613891809157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4046042019752818522412209 3034531514814613891809157)
                      ·
                        rfl

theorem cell23_5909729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_5909729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909729 prefixEnd_5909729 := by exact prefixLift 5909729
  have htrace : WordTrace (prefixWord ++ tailWord_5909729) baseStart_5909729 baseEnd_5909729 := by
    simpa [prefixWord, tailWord_5909729, baseEnd_5909729] using wordTrace_append hprefix tailTrace_5909729
  have hstable : (prefixWord ++ tailWord_5909729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909729).length < 2 ^ (prefixWord ++ tailWord_5909729).sum := by decide
  have hdescent : baseEnd_5909729 < baseStart_5909729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909739 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 3, 4]
def baseStart_5909739 : Nat := 118140960795 + 5909739 * 2 ^ 59
def prefixEnd_5909739 : Nat := 4983230072969 + 3 ^ 40 * 5909739 * 2
def baseEnd_5909739 : Nat := 1011512216540386284228037

theorem tailTrace_5909739 : CollatzResearch.WordTrace tailWord_5909739 prefixEnd_5909739 1011512216540386284228037 := by
  unfold tailWord_5909739
  simp only [CollatzResearch.WordTrace]
  refine ⟨215545889137032380911588271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143697259424688253941058847 215545889137032380911588271)
  ·
    refine ⟨323318833705548571367382407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215545889137032380911588271 323318833705548571367382407)
    ·
      refine ⟨484978250558322857051073611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323318833705548571367382407 484978250558322857051073611)
      ·
        refine ⟨727467375837484285576610417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484978250558322857051073611 727467375837484285576610417)
        ·
          refine ⟨545600531878113214182457813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 727467375837484285576610417 545600531878113214182457813)
          ·
            refine ⟨12787512465893278457401355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 545600531878113214182457813 12787512465893278457401355)
            ·
              refine ⟨19181268698839917686102033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12787512465893278457401355 19181268698839917686102033)
              ·
                refine ⟨14385951524129938264576525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19181268698839917686102033 14385951524129938264576525)
                ·
                  refine ⟨5394731821548726849216197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14385951524129938264576525 5394731821548726849216197)
                  ·
                    refine ⟨1011512216540386284228037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5394731821548726849216197 1011512216540386284228037)
                    ·
                      rfl

theorem cell23_5909739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 4].length) (baseStart_5909739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909739 prefixEnd_5909739 := by exact prefixLift 5909739
  have htrace : WordTrace (prefixWord ++ tailWord_5909739) baseStart_5909739 baseEnd_5909739 := by
    simpa [prefixWord, tailWord_5909739, baseEnd_5909739] using wordTrace_append hprefix tailTrace_5909739
  have hstable : (prefixWord ++ tailWord_5909739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909739).length < 2 ^ (prefixWord ++ tailWord_5909739).sum := by decide
  have hdescent : baseEnd_5909739 < baseStart_5909739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909772 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 1, 2, 6]
def baseStart_5909772 : Nat := 118140960795 + 5909772 * 2 ^ 59
def prefixEnd_5909772 : Nat := 4983230072969 + 3 ^ 40 * 5909772 * 2
def baseEnd_5909772 : Nat := 3034553594482757223571459

theorem tailTrace_5909772 : CollatzResearch.WordTrace tailWord_5909772 prefixEnd_5909772 3034553594482757223571459 := by
  unfold tailWord_5909772
  simp only [CollatzResearch.WordTrace]
  refine ⟨107773546372956413773769785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143698061830608551698359713 107773546372956413773769785)
  ·
    refine ⟨80830159779717310330327339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107773546372956413773769785 80830159779717310330327339)
    ·
      refine ⟨121245239669575965495491009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80830159779717310330327339 121245239669575965495491009)
      ·
        refine ⟨90933929752181974121618257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121245239669575965495491009 90933929752181974121618257)
        ·
          refine ⟨68200447314136480591213693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90933929752181974121618257 68200447314136480591213693)
          ·
            refine ⟨25575167742801180221705135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68200447314136480591213693 25575167742801180221705135)
            ·
              refine ⟨38362751614201770332557703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25575167742801180221705135 38362751614201770332557703)
              ·
                refine ⟨57544127421302655498836555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38362751614201770332557703 57544127421302655498836555)
                ·
                  refine ⟨86316191131953983248254833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57544127421302655498836555 86316191131953983248254833)
                  ·
                    refine ⟨64737143348965487436191125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86316191131953983248254833 64737143348965487436191125)
                    ·
                      refine ⟨3034553594482757223571459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64737143348965487436191125 3034553594482757223571459)
                      ·
                        rfl

theorem cell23_5909772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_5909772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909772 prefixEnd_5909772 := by exact prefixLift 5909772
  have htrace : WordTrace (prefixWord ++ tailWord_5909772) baseStart_5909772 baseEnd_5909772 := by
    simpa [prefixWord, tailWord_5909772, baseEnd_5909772] using wordTrace_append hprefix tailTrace_5909772
  have hstable : (prefixWord ++ tailWord_5909772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909772).length < 2 ^ (prefixWord ++ tailWord_5909772).sum := by decide
  have hdescent : baseEnd_5909772 < baseStart_5909772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909786 : List Nat := [3, 1, 1, 3, 3, 2, 3, 1, 6]
def baseStart_5909786 : Nat := 118140960795 + 5909786 * 2 ^ 59
def prefixEnd_5909786 : Nat := 4983230072969 + 3 ^ 40 * 5909786 * 2
def baseEnd_5909786 : Nat := 337173420356880018755155

theorem tailTrace_5909786 : CollatzResearch.WordTrace tailWord_5909786 prefixEnd_5909786 337173420356880018755155 := by
  unfold tailWord_5909786
  simp only [CollatzResearch.WordTrace]
  refine ⟨53886900841965526984637303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143698402245241405292366141 53886900841965526984637303)
  ·
    refine ⟨80830351262948290476955955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53886900841965526984637303 80830351262948290476955955)
    ·
      refine ⟨121245526894422435715433933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80830351262948290476955955 121245526894422435715433933)
      ·
        refine ⟨45467072585408413393287725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121245526894422435715433933 45467072585408413393287725)
        ·
          refine ⟨17050152219528155022482897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45467072585408413393287725 17050152219528155022482897)
          ·
            refine ⟨12787614164646116266862173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17050152219528155022482897 12787614164646116266862173)
            ·
              refine ⟨4795355311742293600073315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12787614164646116266862173 4795355311742293600073315)
              ·
                refine ⟨7193032967613440400109973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4795355311742293600073315 7193032967613440400109973)
                ·
                  refine ⟨337173420356880018755155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7193032967613440400109973 337173420356880018755155)
                  ·
                    rfl

theorem cell23_5909786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 6].length) (baseStart_5909786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909786 prefixEnd_5909786 := by exact prefixLift 5909786
  have htrace : WordTrace (prefixWord ++ tailWord_5909786) baseStart_5909786 baseEnd_5909786 := by
    simpa [prefixWord, tailWord_5909786, baseEnd_5909786] using wordTrace_append hprefix tailTrace_5909786
  have hstable : (prefixWord ++ tailWord_5909786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909786).length < 2 ^ (prefixWord ++ tailWord_5909786).sum := by decide
  have hdescent : baseEnd_5909786 < baseStart_5909786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909796 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 3, 1, 3]
def baseStart_5909796 : Nat := 118140960795 + 5909796 * 2 ^ 59
def prefixEnd_5909796 : Nat := 4983230072969 + 3 ^ 40 * 5909796 * 2
def baseEnd_5909796 : Nat := 3034565918018465129671349

theorem tailTrace_5909796 : CollatzResearch.WordTrace tailWord_5909796 prefixEnd_5909796 3034565918018465129671349 := by
  unfold tailWord_5909796
  simp only [CollatzResearch.WordTrace]
  refine ⟨107773984048912939823206621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143698645398550586430942161 107773984048912939823206621)
  ·
    refine ⟨40415244018342352433702483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107773984048912939823206621 40415244018342352433702483)
    ·
      refine ⟨60622866027513528650553725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40415244018342352433702483 60622866027513528650553725)
      ·
        refine ⟨22733574760317573243957647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60622866027513528650553725 22733574760317573243957647)
        ·
          refine ⟨34100362140476359865936471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22733574760317573243957647 34100362140476359865936471)
          ·
            refine ⟨51150543210714539798904707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34100362140476359865936471 51150543210714539798904707)
            ·
              refine ⟨76725814816071809698357061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51150543210714539798904707 76725814816071809698357061)
              ·
                refine ⟨14386090278013464318441949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76725814816071809698357061 14386090278013464318441949)
                ·
                  refine ⟨5394783854255049119415731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14386090278013464318441949 5394783854255049119415731)
                  ·
                    refine ⟨8092175781382573679123597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5394783854255049119415731 8092175781382573679123597)
                    ·
                      refine ⟨3034565918018465129671349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8092175781382573679123597 3034565918018465129671349)
                      ·
                        rfl

theorem cell23_5909796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_5909796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909796 prefixEnd_5909796 := by exact prefixLift 5909796
  have htrace : WordTrace (prefixWord ++ tailWord_5909796) baseStart_5909796 baseEnd_5909796 := by
    simpa [prefixWord, tailWord_5909796, baseEnd_5909796] using wordTrace_append hprefix tailTrace_5909796
  have hstable : (prefixWord ++ tailWord_5909796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909796).length < 2 ^ (prefixWord ++ tailWord_5909796).sum := by decide
  have hdescent : baseEnd_5909796 < baseStart_5909796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909837 : List Nat := [1, 6, 1, 3, 2, 1, 2, 1, 6]
def baseStart_5909837 : Nat := 118140960795 + 5909837 * 2 ^ 59
def prefixEnd_5909837 : Nat := 4983230072969 + 3 ^ 40 * 5909837 * 2
def baseEnd_5909837 : Nat := 337176330080588829917629

theorem tailTrace_5909837 : CollatzResearch.WordTrace tailWord_5909837 prefixEnd_5909837 337176330080588829917629 := by
  unfold tailWord_5909837
  simp only [CollatzResearch.WordTrace]
  refine ⟨215549463490677343648655765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143699642327118229099103843 215549463490677343648655765)
  ·
    refine ⟨10103881101125500483530739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 215549463490677343648655765 10103881101125500483530739)
    ·
      refine ⟨15155821651688250725296109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10103881101125500483530739 15155821651688250725296109)
      ·
        refine ⟨5683433119383094021986041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15155821651688250725296109 5683433119383094021986041)
        ·
          refine ⟨4262574839537320516489531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5683433119383094021986041 4262574839537320516489531)
          ·
            refine ⟨6393862259305980774734297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4262574839537320516489531 6393862259305980774734297)
            ·
              refine ⟨4795396694479485581050723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6393862259305980774734297 4795396694479485581050723)
              ·
                refine ⟨7193095041719228371576085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4795396694479485581050723 7193095041719228371576085)
                ·
                  refine ⟨337176330080588829917629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7193095041719228371576085 337176330080588829917629)
                  ·
                    rfl

theorem cell23_5909837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_5909837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909837 prefixEnd_5909837 := by exact prefixLift 5909837
  have htrace : WordTrace (prefixWord ++ tailWord_5909837) baseStart_5909837 baseEnd_5909837 := by
    simpa [prefixWord, tailWord_5909837, baseEnd_5909837] using wordTrace_append hprefix tailTrace_5909837
  have hstable : (prefixWord ++ tailWord_5909837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909837).length < 2 ^ (prefixWord ++ tailWord_5909837).sum := by decide
  have hdescent : baseEnd_5909837 < baseStart_5909837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5909856 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 3]
def baseStart_5909856 : Nat := 118140960795 + 5909856 * 2 ^ 59
def prefixEnd_5909856 : Nat := 4983230072969 + 3 ^ 40 * 5909856 * 2
def baseEnd_5909856 : Nat := 3034596726857734894921073

theorem tailTrace_5909856 : CollatzResearch.WordTrace tailWord_5909856 prefixEnd_5909856 3034596726857734894921073 := by
  unfold tailWord_5909856
  simp only [CollatzResearch.WordTrace]
  refine ⟨107775078238804254946798711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143700104318405673262398281 107775078238804254946798711)
  ·
    refine ⟨161662617358206382420198067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107775078238804254946798711 161662617358206382420198067)
    ·
      refine ⟨242493926037309573630297101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161662617358206382420198067 242493926037309573630297101)
      ·
        refine ⟨90935222263991090111361413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242493926037309573630297101 90935222263991090111361413)
        ·
          refine ⟨17050354174498329395880265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90935222263991090111361413 17050354174498329395880265)
          ·
            refine ⟨12787765630873747046910199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17050354174498329395880265 12787765630873747046910199)
            ·
              refine ⟨19181648446310620570365299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12787765630873747046910199 19181648446310620570365299)
              ·
                refine ⟨28772472669465930855547949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19181648446310620570365299 28772472669465930855547949)
                ·
                  refine ⟨10789677251049724070830481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28772472669465930855547949 10789677251049724070830481)
                  ·
                    refine ⟨8092257938287293053122861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10789677251049724070830481 8092257938287293053122861)
                    ·
                      refine ⟨3034596726857734894921073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8092257938287293053122861 3034596726857734894921073)
                      ·
                        rfl

theorem cell23_5909856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_5909856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909856 prefixEnd_5909856 := by exact prefixLift 5909856
  have htrace : WordTrace (prefixWord ++ tailWord_5909856) baseStart_5909856 baseEnd_5909856 := by
    simpa [prefixWord, tailWord_5909856, baseEnd_5909856] using wordTrace_append hprefix tailTrace_5909856
  have hstable : (prefixWord ++ tailWord_5909856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909856).length < 2 ^ (prefixWord ++ tailWord_5909856).sum := by decide
  have hdescent : baseEnd_5909856 < baseStart_5909856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
