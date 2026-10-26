import V185TrunkScan22Chunk294

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2631268 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_2631268 : Nat := 118140960795 + 2631268 * 2 ^ 59
def prefixEnd_2631268 : Nat := 4983230072969 + 3 ^ 40 * 2631268 * 2
def baseEnd_2631268 : Nat := 900736809863144257032683

theorem tailTrace_2631268 : CollatzResearch.WordTrace tailWord_2631268 prefixEnd_2631268 900736809863144257032683 := by
  unfold tailWord_2631268
  simp only [CollatzResearch.WordTrace]
  refine ⟨47985114115686447821079229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63980152154248597094772305 47985114115686447821079229)
  ·
    refine ⟨17994417793382417932904711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47985114115686447821079229 17994417793382417932904711)
    ·
      refine ⟨26991626690073626899357067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17994417793382417932904711 26991626690073626899357067)
      ·
        refine ⟨40487440035110440349035601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26991626690073626899357067 40487440035110440349035601)
        ·
          refine ⟨30365580026332830261776701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40487440035110440349035601 30365580026332830261776701)
          ·
            refine ⟨11387092509874811348166263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30365580026332830261776701 11387092509874811348166263)
            ·
              refine ⟨17080638764812217022249395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11387092509874811348166263 17080638764812217022249395)
              ·
                refine ⟨25620958147218325533374093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17080638764812217022249395 25620958147218325533374093)
                ·
                  refine ⟨9607859305206872075015285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25620958147218325533374093 9607859305206872075015285)
                  ·
                    refine ⟨900736809863144257032683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9607859305206872075015285 900736809863144257032683)
                    ·
                      rfl

theorem cell22_2631268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_2631268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631268 prefixEnd_2631268 := by exact prefixLift 2631268
  have htrace : WordTrace (prefixWord ++ tailWord_2631268) baseStart_2631268 baseEnd_2631268 := by
    simpa [prefixWord, tailWord_2631268, baseEnd_2631268] using wordTrace_append hprefix tailTrace_2631268
  have hstable : (prefixWord ++ tailWord_2631268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631268).length < 2 ^ (prefixWord ++ tailWord_2631268).sum := by decide
  have hdescent : baseEnd_2631268 < baseStart_2631268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631336 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2631336 : Nat := 118140960795 + 2631336 * 2 ^ 59
def prefixEnd_2631336 : Nat := 4983230072969 + 3 ^ 40 * 2631336 * 2
def baseEnd_2631336 : Nat := 900760087652814746332475

theorem tailTrace_2631336 : CollatzResearch.WordTrace tailWord_2631336 prefixEnd_2631336 900760087652814746332475 := by
  unfold tailWord_2631336
  simp only [CollatzResearch.WordTrace]
  refine ⟨47986354197563271627816931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63981805596751028837089241 47986354197563271627816931)
  ·
    refine ⟨71979531296344907441725397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47986354197563271627816931 71979531296344907441725397)
    ·
      refine ⟨1687020264758083768165439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 71979531296344907441725397 1687020264758083768165439)
      ·
        refine ⟨2530530397137125652248159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1687020264758083768165439 2530530397137125652248159)
        ·
          refine ⟨3795795595705688478372239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2530530397137125652248159 3795795595705688478372239)
          ·
            refine ⟨5693693393558532717558359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3795795595705688478372239 5693693393558532717558359)
            ·
              refine ⟨8540540090337799076337539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5693693393558532717558359 8540540090337799076337539)
              ·
                refine ⟨12810810135506698614506309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8540540090337799076337539 12810810135506698614506309)
                ·
                  refine ⟨2402026900407505990219933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12810810135506698614506309 2402026900407505990219933)
                  ·
                    refine ⟨900760087652814746332475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2402026900407505990219933 900760087652814746332475)
                    ·
                      rfl

theorem cell22_2631336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2631336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631336 prefixEnd_2631336 := by exact prefixLift 2631336
  have htrace : WordTrace (prefixWord ++ tailWord_2631336) baseStart_2631336 baseEnd_2631336 := by
    simpa [prefixWord, tailWord_2631336, baseEnd_2631336] using wordTrace_append hprefix tailTrace_2631336
  have hstable : (prefixWord ++ tailWord_2631336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631336).length < 2 ^ (prefixWord ++ tailWord_2631336).sum := by decide
  have hdescent : baseEnd_2631336 < baseStart_2631336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631343 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 7]
def baseStart_2631343 : Nat := 118140960795 + 2631343 * 2 ^ 59
def prefixEnd_2631343 : Nat := 4983230072969 + 3 ^ 40 * 2631343 * 2
def baseEnd_2631343 : Nat := 300254161298623020469151

theorem tailTrace_2631343 : CollatzResearch.WordTrace tailWord_2631343 prefixEnd_2631343 300254161298623020469151 := by
  unfold tailWord_2631343
  simp only [CollatzResearch.WordTrace]
  refine ⟨95972963706101183451138683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63981975804067455634092455 95972963706101183451138683)
  ·
    refine ⟨143959445559151775176708025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95972963706101183451138683 143959445559151775176708025)
    ·
      refine ⟨107969584169363831382531019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143959445559151775176708025 107969584169363831382531019)
      ·
        refine ⟨161954376254045747073796529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107969584169363831382531019 161954376254045747073796529)
        ·
          refine ⟨121465782190534310305347397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161954376254045747073796529 121465782190534310305347397)
          ·
            refine ⟨22774834160725183182252637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121465782190534310305347397 22774834160725183182252637)
            ·
              refine ⟨8540562810271943693344739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22774834160725183182252637 8540562810271943693344739)
              ·
                refine ⟨12810844215407915540017109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8540562810271943693344739 12810844215407915540017109)
                ·
                  refine ⟨300254161298623020469151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12810844215407915540017109 300254161298623020469151)
                  ·
                    rfl

theorem cell22_2631343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 7].length) (baseStart_2631343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631343 prefixEnd_2631343 := by exact prefixLift 2631343
  have htrace : WordTrace (prefixWord ++ tailWord_2631343) baseStart_2631343 baseEnd_2631343 := by
    simpa [prefixWord, tailWord_2631343, baseEnd_2631343] using wordTrace_append hprefix tailTrace_2631343
  have hstable : (prefixWord ++ tailWord_2631343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631343).length < 2 ^ (prefixWord ++ tailWord_2631343).sum := by decide
  have hdescent : baseEnd_2631343 < baseStart_2631343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631347 : List Nat := [1, 1, 1, 2, 3, 3, 1, 6, 1, 3]
def baseStart_2631347 : Nat := 118140960795 + 2631347 * 2 ^ 59
def prefixEnd_2631347 : Nat := 4983230072969 + 3 ^ 40 * 2631347 * 2
def baseEnd_2631347 : Nat := 900763853177614384307441

theorem tailTrace_2631347 : CollatzResearch.WordTrace tailWord_2631347 prefixEnd_2631347 900763853177614384307441 := by
  unfold tailWord_2631347
  simp only [CollatzResearch.WordTrace]
  refine ⟨95973109598086692134284295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63982073065391128089522863 95973109598086692134284295)
  ·
    refine ⟨143959664397130038201426443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95973109598086692134284295 143959664397130038201426443)
    ·
      refine ⟨215939496595695057302139665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143959664397130038201426443 215939496595695057302139665)
      ·
        refine ⟨161954622446771292976604749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215939496595695057302139665 161954622446771292976604749)
        ·
          refine ⟨60732983417539234866226781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161954622446771292976604749 60732983417539234866226781)
          ·
            refine ⟨22774868781577213074835043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60732983417539234866226781 22774868781577213074835043)
            ·
              refine ⟨34162303172365819612252565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22774868781577213074835043 34162303172365819612252565)
              ·
                refine ⟨1601357961204647794324339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34162303172365819612252565 1601357961204647794324339)
                ·
                  refine ⟨2402036941806971691486509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1601357961204647794324339 2402036941806971691486509)
                  ·
                    refine ⟨900763853177614384307441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2402036941806971691486509 900763853177614384307441)
                    ·
                      rfl

theorem cell22_2631347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 1, 3].length) (baseStart_2631347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631347 prefixEnd_2631347 := by exact prefixLift 2631347
  have htrace : WordTrace (prefixWord ++ tailWord_2631347) baseStart_2631347 baseEnd_2631347 := by
    simpa [prefixWord, tailWord_2631347, baseEnd_2631347] using wordTrace_append hprefix tailTrace_2631347
  have hstable : (prefixWord ++ tailWord_2631347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631347).length < 2 ^ (prefixWord ++ tailWord_2631347).sum := by decide
  have hdescent : baseEnd_2631347 < baseStart_2631347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631366 : List Nat := [6, 1, 2, 1, 1, 3, 2, 6]
def baseStart_2631366 : Nat := 118140960795 + 2631366 * 2 ^ 59
def prefixEnd_2631366 : Nat := 4983230072969 + 3 ^ 40 * 2631366 * 2
def baseEnd_2631366 : Nat := 100085595251767185342487

theorem tailTrace_2631366 : CollatzResearch.WordTrace tailWord_2631366 prefixEnd_2631366 100085595251767185342487 := by
  unfold tailWord_2631366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2999181330781808074350811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63982535056678572252817301 2999181330781808074350811)
  ·
    refine ⟨4498771996172712111526217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2999181330781808074350811 4498771996172712111526217)
    ·
      refine ⟨3374078997129534083644663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4498771996172712111526217 3374078997129534083644663)
      ·
        refine ⟨5061118495694301125466995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3374078997129534083644663 5061118495694301125466995)
        ·
          refine ⟨7591677743541451688200493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5061118495694301125466995 7591677743541451688200493)
          ·
            refine ⟨2846879153828044383075185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7591677743541451688200493 2846879153828044383075185)
            ·
              refine ⟨2135159365371033287306389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2846879153828044383075185 2135159365371033287306389)
              ·
                refine ⟨100085595251767185342487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2135159365371033287306389 100085595251767185342487)
                ·
                  rfl

theorem cell22_2631366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_2631366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631366 prefixEnd_2631366 := by exact prefixLift 2631366
  have htrace : WordTrace (prefixWord ++ tailWord_2631366) baseStart_2631366 baseEnd_2631366 := by
    simpa [prefixWord, tailWord_2631366, baseEnd_2631366] using wordTrace_append hprefix tailTrace_2631366
  have hstable : (prefixWord ++ tailWord_2631366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631366).length < 2 ^ (prefixWord ++ tailWord_2631366).sum := by decide
  have hdescent : baseEnd_2631366 < baseStart_2631366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631420 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 1, 5]
def baseStart_2631420 : Nat := 118140960795 + 2631420 * 2 ^ 59
def prefixEnd_2631420 : Nat := 4983230072969 + 3 ^ 40 * 2631420 * 2
def baseEnd_2631420 : Nat := 900788842569466527232217

theorem tailTrace_2631420 : CollatzResearch.WordTrace tailWord_2631420 prefixEnd_2631420 900788842569466527232217 := by
  unfold tailWord_2631420
  simp only [CollatzResearch.WordTrace]
  refine ⟨47987886063411112800845857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63983848084548150401127809 47987886063411112800845857)
  ·
    refine ⟨35990914547558334600634393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47987886063411112800845857 35990914547558334600634393)
    ·
      refine ⟨26993185910668750950475795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35990914547558334600634393 26993185910668750950475795)
      ·
        refine ⟨40489778866003126425713693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26993185910668750950475795 40489778866003126425713693)
        ·
          refine ⟨15183667074751172409642635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40489778866003126425713693 15183667074751172409642635)
          ·
            refine ⟨22775500612126758614463953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15183667074751172409642635 22775500612126758614463953)
            ·
              refine ⟨17081625459095068960847965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22775500612126758614463953 17081625459095068960847965)
              ·
                refine ⟨6405609547160650860317987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17081625459095068960847965 6405609547160650860317987)
                ·
                  refine ⟨9608414320740976290476981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6405609547160650860317987 9608414320740976290476981)
                  ·
                    refine ⟨900788842569466527232217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9608414320740976290476981 900788842569466527232217)
                    ·
                      rfl

theorem cell22_2631420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_2631420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631420 prefixEnd_2631420 := by exact prefixLift 2631420
  have htrace : WordTrace (prefixWord ++ tailWord_2631420) baseStart_2631420 baseEnd_2631420 := by
    simpa [prefixWord, tailWord_2631420, baseEnd_2631420] using wordTrace_append hprefix tailTrace_2631420
  have hstable : (prefixWord ++ tailWord_2631420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631420).length < 2 ^ (prefixWord ++ tailWord_2631420).sum := by decide
  have hdescent : baseEnd_2631420 < baseStart_2631420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631435 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 2, 4]
def baseStart_2631435 : Nat := 118140960795 + 2631435 * 2 ^ 59
def prefixEnd_2631435 : Nat := 4983230072969 + 3 ^ 40 * 2631435 * 2
def baseEnd_2631435 : Nat := 900793977376011488107171

theorem tailTrace_2631435 : CollatzResearch.WordTrace tailWord_2631435 prefixEnd_2631435 900793977376011488107171 := by
  unfold tailWord_2631435
  simp only [CollatzResearch.WordTrace]
  refine ⟨95976319221767883163487759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63984212814511922108991839 95976319221767883163487759)
  ·
    refine ⟨143964478832651824745231639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95976319221767883163487759 143964478832651824745231639)
    ·
      refine ⟨215946718248977737117847459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143964478832651824745231639 215946718248977737117847459)
      ·
        refine ⟨323920077373466605676771189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215946718248977737117847459 323920077373466605676771189)
        ·
          refine ⟨30367507253762494282197299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 323920077373466605676771189 30367507253762494282197299)
          ·
            refine ⟨45551260880643741423295949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30367507253762494282197299 45551260880643741423295949)
            ·
              refine ⟨17081722830241403033735981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45551260880643741423295949 17081722830241403033735981)
              ·
                refine ⟨6405646061340526137650993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17081722830241403033735981 6405646061340526137650993)
                ·
                  refine ⟨4804234546005394603238245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6405646061340526137650993 4804234546005394603238245)
                  ·
                    refine ⟨900793977376011488107171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4804234546005394603238245 900793977376011488107171)
                    ·
                      rfl

theorem cell22_2631435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 4].length) (baseStart_2631435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631435 prefixEnd_2631435 := by exact prefixLift 2631435
  have htrace : WordTrace (prefixWord ++ tailWord_2631435) baseStart_2631435 baseEnd_2631435 := by
    simpa [prefixWord, tailWord_2631435, baseEnd_2631435] using wordTrace_append hprefix tailTrace_2631435
  have hstable : (prefixWord ++ tailWord_2631435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631435).length < 2 ^ (prefixWord ++ tailWord_2631435).sum := by decide
  have hdescent : baseEnd_2631435 < baseStart_2631435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631482 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 5, 3]
def baseStart_2631482 : Nat := 118140960795 + 2631482 * 2 ^ 59
def prefixEnd_2631482 : Nat := 4983230072969 + 3 ^ 40 * 2631482 * 2
def baseEnd_2631482 : Nat := 900810066436519032182027

theorem tailTrace_2631482 : CollatzResearch.WordTrace tailWord_2631482 prefixEnd_2631482 900810066436519032182027 := by
  unfold tailWord_2631482
  simp only [CollatzResearch.WordTrace]
  refine ⟨23994508363149402547612175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63985355635065073460299133 23994508363149402547612175)
  ·
    refine ⟨35991762544724103821418263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23994508363149402547612175 35991762544724103821418263)
    ·
      refine ⟨53987643817086155732127395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35991762544724103821418263 53987643817086155732127395)
      ·
        refine ⟨80981465725629233598191093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53987643817086155732127395 80981465725629233598191093)
        ·
          refine ⟨7592012411777740649830415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80981465725629233598191093 7592012411777740649830415)
          ·
            refine ⟨11388018617666610974745623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7592012411777740649830415 11388018617666610974745623)
            ·
              refine ⟨17082027926499916462118435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11388018617666610974745623 17082027926499916462118435)
              ·
                refine ⟨25623041889749874693177653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17082027926499916462118435 25623041889749874693177653)
                ·
                  refine ⟨2402160177164050752485405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25623041889749874693177653 2402160177164050752485405)
                  ·
                    refine ⟨900810066436519032182027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2402160177164050752485405 900810066436519032182027)
                    ·
                      rfl

theorem cell22_2631482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_2631482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631482 prefixEnd_2631482 := by exact prefixLift 2631482
  have htrace : WordTrace (prefixWord ++ tailWord_2631482) baseStart_2631482 baseEnd_2631482 := by
    simpa [prefixWord, tailWord_2631482, baseEnd_2631482] using wordTrace_append hprefix tailTrace_2631482
  have hstable : (prefixWord ++ tailWord_2631482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631482).length < 2 ^ (prefixWord ++ tailWord_2631482).sum := by decide
  have hdescent : baseEnd_2631482 < baseStart_2631482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631516 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 3, 3]
def baseStart_2631516 : Nat := 118140960795 + 2631516 * 2 ^ 59
def prefixEnd_2631516 : Nat := 4983230072969 + 3 ^ 40 * 2631516 * 2
def baseEnd_2631516 : Nat := 900821705331354276831923

theorem tailTrace_2631516 : CollatzResearch.WordTrace tailWord_2631516 prefixEnd_2631516 900821705331354276831923 := by
  unfold tailWord_2631516
  simp only [CollatzResearch.WordTrace]
  refine ⟨47989636767237216998593201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63986182356316289331457601 47989636767237216998593201)
  ·
    refine ⟨35992227575427912748944901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47989636767237216998593201 35992227575427912748944901)
    ·
      refine ⟨6748542670392733640427169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35992227575427912748944901 6748542670392733640427169)
      ·
        refine ⟨5061407002794550230320377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6748542670392733640427169 5061407002794550230320377)
        ·
          refine ⟨3796055252095912672740283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5061407002794550230320377 3796055252095912672740283)
          ·
            refine ⟨5694082878143869009110425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3796055252095912672740283 5694082878143869009110425)
            ·
              refine ⟨4270562158607901756832819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5694082878143869009110425 4270562158607901756832819)
              ·
                refine ⟨6405843237911852635249229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4270562158607901756832819 6405843237911852635249229)
                ·
                  refine ⟨2402191214216944738218461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6405843237911852635249229 2402191214216944738218461)
                  ·
                    refine ⟨900821705331354276831923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2402191214216944738218461 900821705331354276831923)
                    ·
                      rfl

theorem cell22_2631516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_2631516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631516 prefixEnd_2631516 := by exact prefixLift 2631516
  have htrace : WordTrace (prefixWord ++ tailWord_2631516) baseStart_2631516 baseEnd_2631516 := by
    simpa [prefixWord, tailWord_2631516, baseEnd_2631516] using wordTrace_append hprefix tailTrace_2631516
  have hstable : (prefixWord ++ tailWord_2631516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631516).length < 2 ^ (prefixWord ++ tailWord_2631516).sum := by decide
  have hdescent : baseEnd_2631516 < baseStart_2631516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631550 : List Nat := [4, 2, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_2631550 : Nat := 118140960795 + 2631550 * 2 ^ 59
def prefixEnd_2631550 : Nat := 4983230072969 + 3 ^ 40 * 2631550 * 2
def baseEnd_2631550 : Nat := 900833344226189521481819

theorem tailTrace_2631550 : CollatzResearch.WordTrace tailWord_2631550 prefixEnd_2631550 900833344226189521481819 := by
  unfold tailWord_2631550
  simp only [CollatzResearch.WordTrace]
  refine ⟨11997564202043907225490513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63987009077567505202616069 11997564202043907225490513)
  ·
    refine ⟨8998173151532930419117885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11997564202043907225490513 8998173151532930419117885)
    ·
      refine ⟨3374314931824848907169207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8998173151532930419117885 3374314931824848907169207)
      ·
        refine ⟨5061472397737273360753811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3374314931824848907169207 5061472397737273360753811)
        ·
          refine ⟨7592208596605910041130717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5061472397737273360753811 7592208596605910041130717)
          ·
            refine ⟨2847078223727216265424019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7592208596605910041130717 2847078223727216265424019)
            ·
              refine ⟨4270617335590824398136029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2847078223727216265424019 4270617335590824398136029)
              ·
                refine ⟨1601481500846559149301011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4270617335590824398136029 1601481500846559149301011)
                ·
                  refine ⟨2402222251269838723951517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1601481500846559149301011 2402222251269838723951517)
                  ·
                    refine ⟨900833344226189521481819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2402222251269838723951517 900833344226189521481819)
                    ·
                      rfl

theorem cell22_2631550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_2631550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631550 prefixEnd_2631550 := by exact prefixLift 2631550
  have htrace : WordTrace (prefixWord ++ tailWord_2631550) baseStart_2631550 baseEnd_2631550 := by
    simpa [prefixWord, tailWord_2631550, baseEnd_2631550] using wordTrace_append hprefix tailTrace_2631550
  have hstable : (prefixWord ++ tailWord_2631550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631550).length < 2 ^ (prefixWord ++ tailWord_2631550).sum := by decide
  have hdescent : baseEnd_2631550 < baseStart_2631550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631707 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 1, 5]
def baseStart_2631707 : Nat := 118140960795 + 2631707 * 2 ^ 59
def prefixEnd_2631707 : Nat := 4983230072969 + 3 ^ 40 * 2631707 * 2
def baseEnd_2631707 : Nat := 900887088534693445306337

theorem tailTrace_2631707 : CollatzResearch.WordTrace tailWord_2631707 prefixEnd_2631707 900887088534693445306337 := by
  unfold tailWord_2631707
  simp only [CollatzResearch.WordTrace]
  refine ⟨95986239876782473617389375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63990826584521649078259583 95986239876782473617389375)
  ·
    refine ⟨143979359815173710426084063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95986239876782473617389375 143979359815173710426084063)
    ·
      refine ⟨215969039722760565639126095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143979359815173710426084063 215969039722760565639126095)
      ·
        refine ⟨323953559584140848458689143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215969039722760565639126095 323953559584140848458689143)
        ·
          refine ⟨485930339376211272688033715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323953559584140848458689143 485930339376211272688033715)
          ·
            refine ⟨728895509064316909032050573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485930339376211272688033715 728895509064316909032050573)
            ·
              refine ⟨273335815899118840887018965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 728895509064316909032050573 273335815899118840887018965)
              ·
                refine ⟨6406308185135597833289507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 273335815899118840887018965 6406308185135597833289507)
                ·
                  refine ⟨9609462277703396749934261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6406308185135597833289507 9609462277703396749934261)
                  ·
                    refine ⟨900887088534693445306337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9609462277703396749934261 900887088534693445306337)
                    ·
                      rfl

theorem cell22_2631707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 5].length) (baseStart_2631707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631707 prefixEnd_2631707 := by exact prefixLift 2631707
  have htrace : WordTrace (prefixWord ++ tailWord_2631707) baseStart_2631707 baseEnd_2631707 := by
    simpa [prefixWord, tailWord_2631707, baseEnd_2631707] using wordTrace_append hprefix tailTrace_2631707
  have hstable : (prefixWord ++ tailWord_2631707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631707).length < 2 ^ (prefixWord ++ tailWord_2631707).sum := by decide
  have hdescent : baseEnd_2631707 < baseStart_2631707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631709 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 6]
def baseStart_2631709 : Nat := 118140960795 + 2631709 * 2 ^ 59
def prefixEnd_2631709 : Nat := 4983230072969 + 3 ^ 40 * 2631709 * 2
def baseEnd_2631709 : Nat := 300295924391855368918777

theorem tailTrace_2631709 : CollatzResearch.WordTrace tailWord_2631709 prefixEnd_2631709 300295924391855368918777 := by
  unfold tailWord_2631709
  simp only [CollatzResearch.WordTrace]
  refine ⟨95986312822775227958962181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63990875215183485305974787 95986312822775227958962181)
  ·
    refine ⟨17997433654270355242305409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95986312822775227958962181 17997433654270355242305409)
    ·
      refine ⟨13498075240702766431729057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17997433654270355242305409 13498075240702766431729057)
      ·
        refine ⟨10123556430527074823796793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13498075240702766431729057 10123556430527074823796793)
        ·
          refine ⟨7592667322895306117847595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10123556430527074823796793 7592667322895306117847595)
          ·
            refine ⟨11389000984342959176771393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7592667322895306117847595 11389000984342959176771393)
            ·
              refine ⟨8541750738257219382578545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11389000984342959176771393 8541750738257219382578545)
              ·
                refine ⟨6406313053692914536933909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8541750738257219382578545 6406313053692914536933909)
                ·
                  refine ⟨300295924391855368918777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6406313053692914536933909 300295924391855368918777)
                  ·
                    rfl

theorem cell22_2631709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_2631709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631709 prefixEnd_2631709 := by exact prefixLift 2631709
  have htrace : WordTrace (prefixWord ++ tailWord_2631709) baseStart_2631709 baseEnd_2631709 := by
    simpa [prefixWord, tailWord_2631709, baseEnd_2631709] using wordTrace_append hprefix tailTrace_2631709
  have hstable : (prefixWord ++ tailWord_2631709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631709).length < 2 ^ (prefixWord ++ tailWord_2631709).sum := by decide
  have hdescent : baseEnd_2631709 < baseStart_2631709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631741 : List Nat := [1, 4, 1, 3, 1, 1, 2, 4, 2, 3]
def baseStart_2631741 : Nat := 118140960795 + 2631741 * 2 ^ 59
def prefixEnd_2631741 : Nat := 4983230072969 + 3 ^ 40 * 2631741 * 2
def baseEnd_2631741 : Nat := 900898727429528689956233

theorem tailTrace_2631741 : CollatzResearch.WordTrace tailWord_2631741 prefixEnd_2631741 900898727429528689956233 := by
  unfold tailWord_2631741
  simp only [CollatzResearch.WordTrace]
  refine ⟨95987479958659297424127077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63991653305772864949418051 95987479958659297424127077)
  ·
    refine ⟨17997652492248618267023827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95987479958659297424127077 17997652492248618267023827)
    ·
      refine ⟨26996478738372927400535741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17997652492248618267023827 26996478738372927400535741)
      ·
        refine ⟨10123679526889847775200903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26996478738372927400535741 10123679526889847775200903)
        ·
          refine ⟨15185519290334771662801355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10123679526889847775200903 15185519290334771662801355)
          ·
            refine ⟨22778278935502157494202033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15185519290334771662801355 22778278935502157494202033)
            ·
              refine ⟨17083709201626618120651525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22778278935502157494202033 17083709201626618120651525)
              ·
                refine ⟨3203195475304990897622161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17083709201626618120651525 3203195475304990897622161)
                ·
                  refine ⟨2402396606478743173216621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3203195475304990897622161 2402396606478743173216621)
                  ·
                    refine ⟨900898727429528689956233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2402396606478743173216621 900898727429528689956233)
                    ·
                      rfl

theorem cell22_2631741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_2631741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631741 prefixEnd_2631741 := by exact prefixLift 2631741
  have htrace : WordTrace (prefixWord ++ tailWord_2631741) baseStart_2631741 baseEnd_2631741 := by
    simpa [prefixWord, tailWord_2631741, baseEnd_2631741] using wordTrace_append hprefix tailTrace_2631741
  have hstable : (prefixWord ++ tailWord_2631741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631741).length < 2 ^ (prefixWord ++ tailWord_2631741).sum := by decide
  have hdescent : baseEnd_2631741 < baseStart_2631741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631752 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 2, 7]
def baseStart_2631752 : Nat := 118140960795 + 2631752 * 2 ^ 59
def prefixEnd_2631752 : Nat := 4983230072969 + 3 ^ 40 * 2631752 * 2
def baseEnd_2631752 : Nat := 900902492954328327931199

theorem tailTrace_2631752 : CollatzResearch.WordTrace tailWord_2631752 prefixEnd_2631752 900902492954328327931199 := by
  unfold tailWord_2631752
  simp only [CollatzResearch.WordTrace]
  refine ⟨47993940580809723151388755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63991920774412964201851673 47993940580809723151388755)
  ·
    refine ⟨71990910871214584727083133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47993940580809723151388755 71990910871214584727083133)
    ·
      refine ⟨26996591576705469272656175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71990910871214584727083133 26996591576705469272656175)
      ·
        refine ⟨40494887365058203908984263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26996591576705469272656175 40494887365058203908984263)
        ·
          refine ⟨60742331047587305863476395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40494887365058203908984263 60742331047587305863476395)
          ·
            refine ⟨91113496571380958795214593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60742331047587305863476395 91113496571380958795214593)
            ·
              refine ⟨68335122428535719096410945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91113496571380958795214593 68335122428535719096410945)
              ·
                refine ⟨51251341821401789322308209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68335122428535719096410945 51251341821401789322308209)
                ·
                  refine ⟨38438506366051341991731157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51251341821401789322308209 38438506366051341991731157)
                  ·
                    refine ⟨900902492954328327931199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38438506366051341991731157 900902492954328327931199)
                    ·
                      rfl

theorem cell22_2631752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_2631752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631752 prefixEnd_2631752 := by exact prefixLift 2631752
  have htrace : WordTrace (prefixWord ++ tailWord_2631752) baseStart_2631752 baseEnd_2631752 := by
    simpa [prefixWord, tailWord_2631752, baseEnd_2631752] using wordTrace_append hprefix tailTrace_2631752
  have hstable : (prefixWord ++ tailWord_2631752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631752).length < 2 ^ (prefixWord ++ tailWord_2631752).sum := by decide
  have hdescent : baseEnd_2631752 < baseStart_2631752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631758 : List Nat := [4, 1, 1, 1, 1, 4, 4, 1, 2, 3]
def baseStart_2631758 : Nat := 118140960795 + 2631758 * 2 ^ 59
def prefixEnd_2631758 : Nat := 4983230072969 + 3 ^ 40 * 2631758 * 2
def baseEnd_2631758 : Nat := 900904546876946312281181

theorem tailTrace_2631758 : CollatzResearch.WordTrace tailWord_2631758 prefixEnd_2631758 900904546876946312281181 := by
  unfold tailWord_2631758
  simp only [CollatzResearch.WordTrace]
  refine ⟨11998512499949713665936991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63992066666398472884997285 11998512499949713665936991)
  ·
    refine ⟨17997768749924570498905487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11998512499949713665936991 17997768749924570498905487)
    ·
      refine ⟨26996653124886855748358231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17997768749924570498905487 26996653124886855748358231)
      ·
        refine ⟨40494979687330283622537347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26996653124886855748358231 40494979687330283622537347)
        ·
          refine ⟨60742469530995425433806021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40494979687330283622537347 60742469530995425433806021)
          ·
            refine ⟨11389213037061642268838629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60742469530995425433806021 11389213037061642268838629)
            ·
              refine ⟨2135477444449057925407243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11389213037061642268838629 2135477444449057925407243)
              ·
                refine ⟨3203216166673586888110865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2135477444449057925407243 3203216166673586888110865)
                ·
                  refine ⟨2402412125005190166083149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3203216166673586888110865 2402412125005190166083149)
                  ·
                    refine ⟨900904546876946312281181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2402412125005190166083149 900904546876946312281181)
                    ·
                      rfl

theorem cell22_2631758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_2631758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631758 prefixEnd_2631758 := by exact prefixLift 2631758
  have htrace : WordTrace (prefixWord ++ tailWord_2631758) baseStart_2631758 baseEnd_2631758 := by
    simpa [prefixWord, tailWord_2631758, baseEnd_2631758] using wordTrace_append hprefix tailTrace_2631758
  have hstable : (prefixWord ++ tailWord_2631758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631758).length < 2 ^ (prefixWord ++ tailWord_2631758).sum := by decide
  have hdescent : baseEnd_2631758 < baseStart_2631758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631769 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 5, 3]
def baseStart_2631769 : Nat := 118140960795 + 2631769 * 2 ^ 59
def prefixEnd_2631769 : Nat := 4983230072969 + 3 ^ 40 * 2631769 * 2
def baseEnd_2631769 : Nat := 900908312401745950256147

theorem tailTrace_2631769 : CollatzResearch.WordTrace tailWord_2631769 prefixEnd_2631769 900908312401745950256147 := by
  unfold tailWord_2631769
  simp only [CollatzResearch.WordTrace]
  refine ⟨95988501202557858206146361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63992334135038572137430907 95988501202557858206146361)
  ·
    refine ⟨71991375901918393654609771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95988501202557858206146361 71991375901918393654609771)
    ·
      refine ⟨107987063852877590481914657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71991375901918393654609771 107987063852877590481914657)
      ·
        refine ⟨80990297889658192861435993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107987063852877590481914657 80990297889658192861435993)
        ·
          refine ⟨60742723417243644646076995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80990297889658192861435993 60742723417243644646076995)
          ·
            refine ⟨91114085125865466969115493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60742723417243644646076995 91114085125865466969115493)
            ·
              refine ⟨17083890961099775056709155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91114085125865466969115493 17083890961099775056709155)
              ·
                refine ⟨25625836441649662585063733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17083890961099775056709155 25625836441649662585063733)
                ·
                  refine ⟨2402422166404655867349725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25625836441649662585063733 2402422166404655867349725)
                  ·
                    refine ⟨900908312401745950256147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2402422166404655867349725 900908312401745950256147)
                    ·
                      rfl

theorem cell22_2631769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 3].length) (baseStart_2631769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631769 prefixEnd_2631769 := by exact prefixLift 2631769
  have htrace : WordTrace (prefixWord ++ tailWord_2631769) baseStart_2631769 baseEnd_2631769 := by
    simpa [prefixWord, tailWord_2631769, baseEnd_2631769] using wordTrace_append hprefix tailTrace_2631769
  have hstable : (prefixWord ++ tailWord_2631769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631769).length < 2 ^ (prefixWord ++ tailWord_2631769).sum := by decide
  have hdescent : baseEnd_2631769 < baseStart_2631769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631773 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2631773 : Nat := 118140960795 + 2631773 * 2 ^ 59
def prefixEnd_2631773 : Nat := 4983230072969 + 3 ^ 40 * 2631773 * 2
def baseEnd_2631773 : Nat := 900909681683491273156135

theorem tailTrace_2631773 : CollatzResearch.WordTrace tailWord_2631773 prefixEnd_2631773 900909681683491273156135 := by
  unfold tailWord_2631773
  simp only [CollatzResearch.WordTrace]
  refine ⟨95988647094543366889291973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63992431396362244592861315 95988647094543366889291973)
  ·
    refine ⟨17997871330226881291742245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95988647094543366889291973 17997871330226881291742245)
    ·
      refine ⟨3374600874417540242201671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17997871330226881291742245 3374600874417540242201671)
      ·
        refine ⟨5061901311626310363302507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3374600874417540242201671 5061901311626310363302507)
        ·
          refine ⟨7592851967439465544953761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5061901311626310363302507 7592851967439465544953761)
          ·
            refine ⟨5694638975579599158715321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7592851967439465544953761 5694638975579599158715321)
            ·
              refine ⟨4270979231684699369036491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5694638975579599158715321 4270979231684699369036491)
              ·
                refine ⟨6406468847527049053554737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4270979231684699369036491 6406468847527049053554737)
                ·
                  refine ⟨4804851635645286790166053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6406468847527049053554737 4804851635645286790166053)
                  ·
                    refine ⟨900909681683491273156135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4804851635645286790166053 900909681683491273156135)
                    ·
                      rfl

theorem cell22_2631773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2631773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631773 prefixEnd_2631773 := by exact prefixLift 2631773
  have htrace : WordTrace (prefixWord ++ tailWord_2631773) baseStart_2631773 baseEnd_2631773 := by
    simpa [prefixWord, tailWord_2631773, baseEnd_2631773] using wordTrace_append hprefix tailTrace_2631773
  have hstable : (prefixWord ++ tailWord_2631773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631773).length < 2 ^ (prefixWord ++ tailWord_2631773).sum := by decide
  have hdescent : baseEnd_2631773 < baseStart_2631773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631799 : List Nat := [1, 1, 3, 1, 1, 5, 1, 4, 5]
def baseStart_2631799 : Nat := 118140960795 + 2631799 * 2 ^ 59
def prefixEnd_2631799 : Nat := 4983230072969 + 3 ^ 40 * 2631799 * 2
def baseEnd_2631799 : Nat := 300306194004945290668685

theorem tailTrace_2631799 : CollatzResearch.WordTrace tailWord_2631799 prefixEnd_2631799 300306194004945290668685 := by
  unfold tailWord_2631799
  simp only [CollatzResearch.WordTrace]
  refine ⟨95989595392449173329738451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63993063594966115553158967 95989595392449173329738451)
  ·
    refine ⟨143984393088673759994607677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95989595392449173329738451 143984393088673759994607677)
    ·
      refine ⟨53994147408252659997977879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143984393088673759994607677 53994147408252659997977879)
      ·
        refine ⟨80991221112378989996966819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53994147408252659997977879 80991221112378989996966819)
        ·
          refine ⟨121486831668568484995450229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80991221112378989996966819 121486831668568484995450229)
          ·
            refine ⟨11389390468928295468323459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121486831668568484995450229 11389390468928295468323459)
            ·
              refine ⟨17084085703392443202485189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11389390468928295468323459 17084085703392443202485189)
              ·
                refine ⟨3203266069386083100465973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17084085703392443202485189 3203266069386083100465973)
                ·
                  refine ⟨300306194004945290668685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3203266069386083100465973 300306194004945290668685)
                  ·
                    rfl

theorem cell22_2631799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 5].length) (baseStart_2631799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631799 prefixEnd_2631799 := by exact prefixLift 2631799
  have htrace : WordTrace (prefixWord ++ tailWord_2631799) baseStart_2631799 baseEnd_2631799 := by
    simpa [prefixWord, tailWord_2631799, baseEnd_2631799] using wordTrace_append hprefix tailTrace_2631799
  have hstable : (prefixWord ++ tailWord_2631799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631799).length < 2 ^ (prefixWord ++ tailWord_2631799).sum := by decide
  have hdescent : baseEnd_2631799 < baseStart_2631799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631816 : List Nat := [2, 1, 3, 4, 1, 1, 2, 3, 5]
def baseStart_2631816 : Nat := 118140960795 + 2631816 * 2 ^ 59
def prefixEnd_2631816 : Nat := 4983230072969 + 3 ^ 40 * 2631816 * 2
def baseEnd_2631816 : Nat := 300308133820751164777001

theorem tailTrace_2631816 : CollatzResearch.WordTrace tailWord_2631816 prefixEnd_2631816 300308133820751164777001 := by
  unfold tailWord_2631816
  simp only [CollatzResearch.WordTrace]
  refine ⟨47995107716693792616553651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63993476955591723488738201 47995107716693792616553651)
  ·
    refine ⟨71992661575040688924830477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47995107716693792616553651 71992661575040688924830477)
    ·
      refine ⟨26997248090640258346811429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71992661575040688924830477 26997248090640258346811429)
      ·
        refine ⟨5061984016995048440027143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26997248090640258346811429 5061984016995048440027143)
        ·
          refine ⟨7592976025492572660040715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5061984016995048440027143 7592976025492572660040715)
          ·
            refine ⟨11389464038238858990061073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7592976025492572660040715 11389464038238858990061073)
            ·
              refine ⟨8542098028679144242545805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11389464038238858990061073 8542098028679144242545805)
              ·
                refine ⟨3203286760754679090954677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8542098028679144242545805 3203286760754679090954677)
                ·
                  refine ⟨300308133820751164777001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3203286760754679090954677 300308133820751164777001)
                  ·
                    rfl

theorem cell22_2631816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 5].length) (baseStart_2631816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631816 prefixEnd_2631816 := by exact prefixLift 2631816
  have htrace : WordTrace (prefixWord ++ tailWord_2631816) baseStart_2631816 baseEnd_2631816 := by
    simpa [prefixWord, tailWord_2631816, baseEnd_2631816] using wordTrace_append hprefix tailTrace_2631816
  have hstable : (prefixWord ++ tailWord_2631816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631816).length < 2 ^ (prefixWord ++ tailWord_2631816).sum := by decide
  have hdescent : baseEnd_2631816 < baseStart_2631816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631829 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 3, 4]
def baseStart_2631829 : Nat := 118140960795 + 2631829 * 2 ^ 59
def prefixEnd_2631829 : Nat := 4983230072969 + 3 ^ 40 * 2631829 * 2
def baseEnd_2631829 : Nat := 900928851627925793755963

theorem tailTrace_2631829 : CollatzResearch.WordTrace tailWord_2631829 prefixEnd_2631829 900928851627925793755963 := by
  unfold tailWord_2631829
  simp only [CollatzResearch.WordTrace]
  refine ⟨95990689582340488453330541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63993793054893658968887027 95990689582340488453330541)
  ·
    refine ⟨35996508593377683169998953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95990689582340488453330541 35996508593377683169998953)
    ·
      refine ⟨26997381445033262377499215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35996508593377683169998953 26997381445033262377499215)
      ·
        refine ⟨40496072167549893566248823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26997381445033262377499215 40496072167549893566248823)
        ·
          refine ⟨60744108251324840349373235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40496072167549893566248823 60744108251324840349373235)
          ·
            refine ⟨91116162376987260524059853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60744108251324840349373235 91116162376987260524059853)
            ·
              refine ⟨34168560891370222696522445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91116162376987260524059853 34168560891370222696522445)
              ·
                refine ⟨12813210334263833511195917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34168560891370222696522445 12813210334263833511195917)
                ·
                  refine ⟨4804953875348937566698469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12813210334263833511195917 4804953875348937566698469)
                  ·
                    refine ⟨900928851627925793755963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4804953875348937566698469 900928851627925793755963)
                    ·
                      rfl

theorem cell22_2631829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_2631829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631829 prefixEnd_2631829 := by exact prefixLift 2631829
  have htrace : WordTrace (prefixWord ++ tailWord_2631829) baseStart_2631829 baseEnd_2631829 := by
    simpa [prefixWord, tailWord_2631829, baseEnd_2631829] using wordTrace_append hprefix tailTrace_2631829
  have hstable : (prefixWord ++ tailWord_2631829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631829).length < 2 ^ (prefixWord ++ tailWord_2631829).sum := by decide
  have hdescent : baseEnd_2631829 < baseStart_2631829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631850 : List Nat := [3, 1, 5, 1, 2, 2, 1, 2, 5]
def baseStart_2631850 : Nat := 118140960795 + 2631850 * 2 ^ 59
def prefixEnd_2631850 : Nat := 4983230072969 + 3 ^ 40 * 2631850 * 2
def baseEnd_2631850 : Nat := 300312013452362912993633

theorem tailTrace_2631850 : CollatzResearch.WordTrace tailWord_2631850 prefixEnd_2631850 300312013452362912993633 := by
  unfold tailWord_2631850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23997863878816102259961251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63994303676842939359896669 23997863878816102259961251)
  ·
    refine ⟨35996795818224153389941877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23997863878816102259961251 35996795818224153389941877)
    ·
      refine ⟨3374699607958514380307051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35996795818224153389941877 3374699607958514380307051)
      ·
        refine ⟨5062049411937771570460577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3374699607958514380307051 5062049411937771570460577)
        ·
          refine ⟨3796537058953328677845433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5062049411937771570460577 3796537058953328677845433)
          ·
            refine ⟨2847402794214996508384075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3796537058953328677845433 2847402794214996508384075)
            ·
              refine ⟨4271104191322494762576113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2847402794214996508384075 4271104191322494762576113)
              ·
                refine ⟨3203328143491871071932085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4271104191322494762576113 3203328143491871071932085)
                ·
                  refine ⟨300312013452362912993633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3203328143491871071932085 300312013452362912993633)
                  ·
                    rfl

theorem cell22_2631850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_2631850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631850 prefixEnd_2631850 := by exact prefixLift 2631850
  have htrace : WordTrace (prefixWord ++ tailWord_2631850) baseStart_2631850 baseEnd_2631850 := by
    simpa [prefixWord, tailWord_2631850, baseEnd_2631850] using wordTrace_append hprefix tailTrace_2631850
  have hstable : (prefixWord ++ tailWord_2631850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631850).length < 2 ^ (prefixWord ++ tailWord_2631850).sum := by decide
  have hdescent : baseEnd_2631850 < baseStart_2631850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631968 : List Nat := [2, 1, 1, 5, 2, 2, 2, 2, 5]
def baseStart_2631968 : Nat := 118140960795 + 2631968 * 2 ^ 59
def prefixEnd_2631968 : Nat := 4983230072969 + 3 ^ 40 * 2631968 * 2
def baseEnd_2631968 : Nat := 300325478056191921510179

theorem tailTrace_2631968 : CollatzResearch.WordTrace tailWord_2631968 prefixEnd_2631968 300325478056191921510179 := by
  unfold tailWord_2631968
  simp only [CollatzResearch.WordTrace]
  refine ⟨47997879664418457596320279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63997172885891276795093705 47997879664418457596320279)
  ·
    refine ⟨71996819496627686394480419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47997879664418457596320279 71996819496627686394480419)
    ·
      refine ⟨107995229244941529591720629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71996819496627686394480419 107995229244941529591720629)
      ·
        refine ⟨10124552741713268399223809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107995229244941529591720629 10124552741713268399223809)
        ·
          refine ⟨7593414556284951299417857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10124552741713268399223809 7593414556284951299417857)
          ·
            refine ⟨5695060917213713474563393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7593414556284951299417857 5695060917213713474563393)
            ·
              refine ⟨4271295687910285105922545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5695060917213713474563393 4271295687910285105922545)
              ·
                refine ⟨3203471765932713829441909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4271295687910285105922545 3203471765932713829441909)
                ·
                  refine ⟨300325478056191921510179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3203471765932713829441909 300325478056191921510179)
                  ·
                    rfl

theorem cell22_2631968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 5].length) (baseStart_2631968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631968 prefixEnd_2631968 := by exact prefixLift 2631968
  have htrace : WordTrace (prefixWord ++ tailWord_2631968) baseStart_2631968 baseEnd_2631968 := by
    simpa [prefixWord, tailWord_2631968, baseEnd_2631968] using wordTrace_append hprefix tailTrace_2631968
  have hstable : (prefixWord ++ tailWord_2631968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631968).length < 2 ^ (prefixWord ++ tailWord_2631968).sum := by decide
  have hdescent : baseEnd_2631968 < baseStart_2631968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631972 : List Nat := [2, 3, 1, 3, 1, 2, 4, 2, 1, 3]
def baseStart_2631972 : Nat := 118140960795 + 2631972 * 2 ^ 59
def prefixEnd_2631972 : Nat := 4983230072969 + 3 ^ 40 * 2631972 * 2
def baseEnd_2631972 : Nat := 900977803450321087430525

theorem tailTrace_2631972 : CollatzResearch.WordTrace tailWord_2631972 prefixEnd_2631972 900977803450321087430525 := by
  unfold tailWord_2631972
  simp only [CollatzResearch.WordTrace]
  refine ⟨47997952610411211937893085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63997270147214949250524113 47997952610411211937893085)
  ·
    refine ⟨17999232228904204476709907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47997952610411211937893085 17999232228904204476709907)
    ·
      refine ⟨26998848343356306715064861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17999232228904204476709907 26998848343356306715064861)
      ·
        refine ⟨10124568128758615018149323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26998848343356306715064861 10124568128758615018149323)
        ·
          refine ⟨15186852193137922527223985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10124568128758615018149323 15186852193137922527223985)
          ·
            refine ⟨11390139144853441895417989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15186852193137922527223985 11390139144853441895417989)
            ·
              refine ⟨2135651089660020355390873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11390139144853441895417989 2135651089660020355390873)
              ·
                refine ⟨1601738317245015266543155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2135651089660020355390873 1601738317245015266543155)
                ·
                  refine ⟨2402607475867522899814733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1601738317245015266543155 2402607475867522899814733)
                  ·
                    refine ⟨900977803450321087430525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2402607475867522899814733 900977803450321087430525)
                    ·
                      rfl

theorem cell22_2631972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_2631972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631972 prefixEnd_2631972 := by exact prefixLift 2631972
  have htrace : WordTrace (prefixWord ++ tailWord_2631972) baseStart_2631972 baseEnd_2631972 := by
    simpa [prefixWord, tailWord_2631972, baseEnd_2631972] using wordTrace_append hprefix tailTrace_2631972
  have hstable : (prefixWord ++ tailWord_2631972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631972).length < 2 ^ (prefixWord ++ tailWord_2631972).sum := by decide
  have hdescent : baseEnd_2631972 < baseStart_2631972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631996 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 6]
def baseStart_2631996 : Nat := 118140960795 + 2631996 * 2 ^ 59
def prefixEnd_2631996 : Nat := 4983230072969 + 3 ^ 40 * 2631996 * 2
def baseEnd_2631996 : Nat := 300328673046931008276817

theorem tailTrace_2631996 : CollatzResearch.WordTrace tailWord_2631996 prefixEnd_2631996 300328673046931008276817 := by
  unfold tailWord_2631996
  simp only [CollatzResearch.WordTrace]
  refine ⟨47998390286367737987329921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63997853715156983983106561 47998390286367737987329921)
  ·
    refine ⟨35998792714775803490497441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47998390286367737987329921 35998792714775803490497441)
    ·
      refine ⟨26999094536081852617873081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35998792714775803490497441 26999094536081852617873081)
      ·
        refine ⟨20249320902061389463404811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26999094536081852617873081 20249320902061389463404811)
        ·
          refine ⟨30373981353092084195107217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20249320902061389463404811 30373981353092084195107217)
          ·
            refine ⟨22780486014819063146330413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30373981353092084195107217 22780486014819063146330413)
            ·
              refine ⟨8542682255557148679873905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22780486014819063146330413 8542682255557148679873905)
              ·
                refine ⟨6407011691667861509905429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8542682255557148679873905 6407011691667861509905429)
                ·
                  refine ⟨300328673046931008276817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6407011691667861509905429 300328673046931008276817)
                  ·
                    rfl

theorem cell22_2631996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_2631996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631996 prefixEnd_2631996 := by exact prefixLift 2631996
  have htrace : WordTrace (prefixWord ++ tailWord_2631996) baseStart_2631996 baseEnd_2631996 := by
    simpa [prefixWord, tailWord_2631996, baseEnd_2631996] using wordTrace_append hprefix tailTrace_2631996
  have hstable : (prefixWord ++ tailWord_2631996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631996).length < 2 ^ (prefixWord ++ tailWord_2631996).sum := by decide
  have hdescent : baseEnd_2631996 < baseStart_2631996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631998 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_2631998 : Nat := 118140960795 + 2631998 * 2 ^ 59
def prefixEnd_2631998 : Nat := 4983230072969 + 3 ^ 40 * 2631998 * 2
def baseEnd_2631998 : Nat := 900986703781665686280445

theorem tailTrace_2631998 : CollatzResearch.WordTrace tailWord_2631998 prefixEnd_2631998 900986703781665686280445 := by
  unfold tailWord_2631998
  simp only [CollatzResearch.WordTrace]
  refine ⟨11999606689841028789529081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63997902345818820210821765 11999606689841028789529081)
  ·
    refine ⟨8999705017380771592146811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11999606689841028789529081 8999705017380771592146811)
    ·
      refine ⟨13499557526071157388220217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8999705017380771592146811 13499557526071157388220217)
      ·
        refine ⟨10124668144553368041165163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13499557526071157388220217 10124668144553368041165163)
        ·
          refine ⟨15187002216830052061747745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10124668144553368041165163 15187002216830052061747745)
          ·
            refine ⟨11390251662622539046310809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15187002216830052061747745 11390251662622539046310809)
            ·
              refine ⟨8542688746966904284733107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11390251662622539046310809 8542688746966904284733107)
              ·
                refine ⟨12814033120450356427099661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8542688746966904284733107 12814033120450356427099661)
                ·
                  refine ⟨4805262420168883660162373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12814033120450356427099661 4805262420168883660162373)
                  ·
                    refine ⟨900986703781665686280445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4805262420168883660162373 900986703781665686280445)
                    ·
                      rfl

theorem cell22_2631998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_2631998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631998 prefixEnd_2631998 := by exact prefixLift 2631998
  have htrace : WordTrace (prefixWord ++ tailWord_2631998) baseStart_2631998 baseEnd_2631998 := by
    simpa [prefixWord, tailWord_2631998, baseEnd_2631998] using wordTrace_append hprefix tailTrace_2631998
  have hstable : (prefixWord ++ tailWord_2631998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631998).length < 2 ^ (prefixWord ++ tailWord_2631998).sum := by decide
  have hdescent : baseEnd_2631998 < baseStart_2631998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632026 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 4, 4]
def baseStart_2632026 : Nat := 118140960795 + 2632026 * 2 ^ 59
def prefixEnd_2632026 : Nat := 4983230072969 + 3 ^ 40 * 2632026 * 2
def baseEnd_2632026 : Nat := 900996288753882946580359

theorem tailTrace_2632026 : CollatzResearch.WordTrace tailWord_2632026 prefixEnd_2632026 900996288753882946580359 := by
  unfold tailWord_2632026
  simp only [CollatzResearch.WordTrace]
  refine ⟨23999468690656697774562983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63998583175084527398834621 23999468690656697774562983)
  ·
    refine ⟨35999203035985046661844475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23999468690656697774562983 35999203035985046661844475)
    ·
      refine ⟨53998804553977569992766713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35999203035985046661844475 53998804553977569992766713)
      ·
        refine ⟨40499103415483177494575035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53998804553977569992766713 40499103415483177494575035)
        ·
          refine ⟨60748655123224766241862553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40499103415483177494575035 60748655123224766241862553)
          ·
            refine ⟨45561491342418574681396915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60748655123224766241862553 45561491342418574681396915)
            ·
              refine ⟨68342237013627862022095373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45561491342418574681396915 68342237013627862022095373)
              ·
                refine ⟨25628338880110448258285765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68342237013627862022095373 25628338880110448258285765)
                ·
                  refine ⟨4805313540020709048428581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25628338880110448258285765 4805313540020709048428581)
                  ·
                    refine ⟨900996288753882946580359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4805313540020709048428581 900996288753882946580359)
                    ·
                      rfl

theorem cell22_2632026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_2632026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632026 prefixEnd_2632026 := by exact prefixLift 2632026
  have htrace : WordTrace (prefixWord ++ tailWord_2632026) baseStart_2632026 baseEnd_2632026 := by
    simpa [prefixWord, tailWord_2632026, baseEnd_2632026] using wordTrace_append hprefix tailTrace_2632026
  have hstable : (prefixWord ++ tailWord_2632026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632026).length < 2 ^ (prefixWord ++ tailWord_2632026).sum := by decide
  have hdescent : baseEnd_2632026 < baseStart_2632026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632090 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 3, 3]
def baseStart_2632090 : Nat := 118140960795 + 2632090 * 2 ^ 59
def prefixEnd_2632090 : Nat := 4983230072969 + 3 ^ 40 * 2632090 * 2
def baseEnd_2632090 : Nat := 901018197261808112980163

theorem tailTrace_2632090 : CollatzResearch.WordTrace tailWord_2632090 prefixEnd_2632090 901018197261808112980163 := by
  unfold tailWord_2632090
  simp only [CollatzResearch.WordTrace]
  refine ⟨24000052258598732507145431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64000139356263286685721149 24000052258598732507145431)
  ·
    refine ⟨36000078387898098760718147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24000052258598732507145431 36000078387898098760718147)
    ·
      refine ⟨54000117581847148141077221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36000078387898098760718147 54000117581847148141077221)
      ·
        refine ⟨10125022046596340276451979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54000117581847148141077221 10125022046596340276451979)
        ·
          refine ⟨15187533069894510414677969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10125022046596340276451979 15187533069894510414677969)
          ·
            refine ⟨11390649802420882811008477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15187533069894510414677969 11390649802420882811008477)
            ·
              refine ⟨4271493675907831054128179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11390649802420882811008477 4271493675907831054128179)
              ·
                refine ⟨6407240513861746581192269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4271493675907831054128179 6407240513861746581192269)
                ·
                  refine ⟨2402715192698154967947101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6407240513861746581192269 2402715192698154967947101)
                  ·
                    refine ⟨901018197261808112980163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2402715192698154967947101 901018197261808112980163)
                    ·
                      rfl

theorem cell22_2632090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_2632090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632090 prefixEnd_2632090 := by exact prefixLift 2632090
  have htrace : WordTrace (prefixWord ++ tailWord_2632090) baseStart_2632090 baseEnd_2632090 := by
    simpa [prefixWord, tailWord_2632090, baseEnd_2632090] using wordTrace_append hprefix tailTrace_2632090
  have hstable : (prefixWord ++ tailWord_2632090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632090).length < 2 ^ (prefixWord ++ tailWord_2632090).sum := by decide
  have hdescent : baseEnd_2632090 < baseStart_2632090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632101 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_2632101 : Nat := 118140960795 + 2632101 * 2 ^ 59
def prefixEnd_2632101 : Nat := 4983230072969 + 3 ^ 40 * 2632101 * 2
def baseEnd_2632101 : Nat := 901021962786607750955129

theorem tailTrace_2632101 : CollatzResearch.WordTrace tailWord_2632101 prefixEnd_2632101 901021962786607750955129 := by
  unfold tailWord_2632101
  simp only [CollatzResearch.WordTrace]
  refine ⟨96000610237355078907232157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64000406824903385938154771 96000610237355078907232157)
  ·
    refine ⟨36000228839008154590212059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96000610237355078907232157 36000228839008154590212059)
    ·
      refine ⟨54000343258512231885318089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36000228839008154590212059 54000343258512231885318089)
      ·
        refine ⟨40500257443884173913988567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54000343258512231885318089 40500257443884173913988567)
        ·
          refine ⟨60750386165826260870982851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40500257443884173913988567 60750386165826260870982851)
          ·
            refine ⟨91125579248739391306474277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60750386165826260870982851 91125579248739391306474277)
            ·
              refine ⟨17086046109138635869963927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91125579248739391306474277 17086046109138635869963927)
              ·
                refine ⟨25629069163707953804945891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17086046109138635869963927 25629069163707953804945891)
                ·
                  refine ⟨38443603745561930707418837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25629069163707953804945891 38443603745561930707418837)
                  ·
                    refine ⟨901021962786607750955129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38443603745561930707418837 901021962786607750955129)
                    ·
                      rfl

theorem cell22_2632101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_2632101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632101 prefixEnd_2632101 := by exact prefixLift 2632101
  have htrace : WordTrace (prefixWord ++ tailWord_2632101) baseStart_2632101 baseEnd_2632101 := by
    simpa [prefixWord, tailWord_2632101, baseEnd_2632101] using wordTrace_append hprefix tailTrace_2632101
  have hstable : (prefixWord ++ tailWord_2632101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632101).length < 2 ^ (prefixWord ++ tailWord_2632101).sum := by decide
  have hdescent : baseEnd_2632101 < baseStart_2632101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632150 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2632150 : Nat := 118140960795 + 2632150 * 2 ^ 59
def prefixEnd_2632150 : Nat := 4983230072969 + 3 ^ 40 * 2632150 * 2
def baseEnd_2632150 : Nat := 901038736487987956479979

theorem tailTrace_2632150 : CollatzResearch.WordTrace tailWord_2632150 prefixEnd_2632150 901038736487987956479979 := by
  unfold tailWord_2632150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6000149838386097517235369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64001598276118373517177269 6000149838386097517235369)
  ·
    refine ⟨4500112378789573137926527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6000149838386097517235369 4500112378789573137926527)
    ·
      refine ⟨6750168568184359706889791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4500112378789573137926527 6750168568184359706889791)
      ·
        refine ⟨10125252852276539560334687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6750168568184359706889791 10125252852276539560334687)
        ·
          refine ⟨15187879278414809340502031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10125252852276539560334687 15187879278414809340502031)
          ·
            refine ⟨22781818917622214010753047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15187879278414809340502031 22781818917622214010753047)
            ·
              refine ⟨34172728376433321016129571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22781818917622214010753047 34172728376433321016129571)
              ·
                refine ⟨51259092564649981524194357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34172728376433321016129571 51259092564649981524194357)
                ·
                  refine ⟨4805539927935935767893221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51259092564649981524194357 4805539927935935767893221)
                  ·
                    refine ⟨901038736487987956479979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4805539927935935767893221 901038736487987956479979)
                    ·
                      rfl

theorem cell22_2632150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2632150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632150 prefixEnd_2632150 := by exact prefixLift 2632150
  have htrace : WordTrace (prefixWord ++ tailWord_2632150) baseStart_2632150 baseEnd_2632150 := by
    simpa [prefixWord, tailWord_2632150, baseEnd_2632150] using wordTrace_append hprefix tailTrace_2632150
  have hstable : (prefixWord ++ tailWord_2632150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632150).length < 2 ^ (prefixWord ++ tailWord_2632150).sum := by decide
  have hdescent : baseEnd_2632150 < baseStart_2632150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632165 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 6]
def baseStart_2632165 : Nat := 118140960795 + 2632165 * 2 ^ 59
def prefixEnd_2632165 : Nat := 4983230072969 + 3 ^ 40 * 2632165 * 2
def baseEnd_2632165 : Nat := 300347957098177639118311

theorem tailTrace_2632165 : CollatzResearch.WordTrace tailWord_2632165 prefixEnd_2632165 300347957098177639118311 := by
  unfold tailWord_2632165
  simp only [CollatzResearch.WordTrace]
  refine ⟨96002944509123217837561949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64001963006082145225041299 96002944509123217837561949)
  ·
    refine ⟨36001104190921206689085731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96002944509123217837561949 36001104190921206689085731)
    ·
      refine ⟨54001656286381810033628597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36001104190921206689085731 54001656286381810033628597)
      ·
        refine ⟨5062655276848294690652681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54001656286381810033628597 5062655276848294690652681)
        ·
          refine ⟨3796991457636221017989511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5062655276848294690652681 3796991457636221017989511)
          ·
            refine ⟨5695487186454331526984267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3796991457636221017989511 5695487186454331526984267)
            ·
              refine ⟨8543230779681497290476401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5695487186454331526984267 8543230779681497290476401)
              ·
                refine ⟨6407423084761122967857301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8543230779681497290476401 6407423084761122967857301)
                ·
                  refine ⟨300347957098177639118311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6407423084761122967857301 300347957098177639118311)
                  ·
                    rfl

theorem cell22_2632165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_2632165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632165 prefixEnd_2632165 := by exact prefixLift 2632165
  have htrace : WordTrace (prefixWord ++ tailWord_2632165) baseStart_2632165 baseEnd_2632165 := by
    simpa [prefixWord, tailWord_2632165, baseEnd_2632165] using wordTrace_append hprefix tailTrace_2632165
  have hstable : (prefixWord ++ tailWord_2632165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632165).length < 2 ^ (prefixWord ++ tailWord_2632165).sum := by decide
  have hdescent : baseEnd_2632165 < baseStart_2632165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632182 : List Nat := [5, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_2632182 : Nat := 118140960795 + 2632182 * 2 ^ 59
def prefixEnd_2632182 : Nat := 4983230072969 + 3 ^ 40 * 2632182 * 2
def baseEnd_2632182 : Nat := 300349896913983513226627

theorem tailTrace_2632182 : CollatzResearch.WordTrace tailWord_2632182 prefixEnd_2632182 300349896913983513226627 := by
  unfold tailWord_2632182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6000222784378851858808175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64002376366707753160620533 6000222784378851858808175)
  ·
    refine ⟨9000334176568277788212263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6000222784378851858808175 9000334176568277788212263)
    ·
      refine ⟨13500501264852416682318395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9000334176568277788212263 13500501264852416682318395)
      ·
        refine ⟨20250751897278625023477593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13500501264852416682318395 20250751897278625023477593)
        ·
          refine ⟨15188063922958968767608195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20250751897278625023477593 15188063922958968767608195)
          ·
            refine ⟨22782095884438453151412293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15188063922958968767608195 22782095884438453151412293)
            ·
              refine ⟨4271642978332209965889805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22782095884438453151412293 4271642978332209965889805)
              ·
                refine ⟨1601866116874578737208677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4271642978332209965889805 1601866116874578737208677)
                ·
                  refine ⟨300349896913983513226627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1601866116874578737208677 300349896913983513226627)
                  ·
                    rfl

theorem cell22_2632182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_2632182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632182 prefixEnd_2632182 := by exact prefixLift 2632182
  have htrace : WordTrace (prefixWord ++ tailWord_2632182) baseStart_2632182 baseEnd_2632182 := by
    simpa [prefixWord, tailWord_2632182, baseEnd_2632182] using wordTrace_append hprefix tailTrace_2632182
  have hstable : (prefixWord ++ tailWord_2632182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632182).length < 2 ^ (prefixWord ++ tailWord_2632182).sum := by decide
  have hdescent : baseEnd_2632182 < baseStart_2632182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632193 : List Nat := [1, 2, 4, 1, 3, 2, 9]
def baseStart_2632193 : Nat := 118140960795 + 2632193 * 2 ^ 59
def prefixEnd_2632193 : Nat := 4983230072969 + 3 ^ 40 * 2632193 * 2
def baseEnd_2632193 : Nat := 33372350232101858431661

theorem tailTrace_2632193 : CollatzResearch.WordTrace tailWord_2632193 prefixEnd_2632193 33372350232101858431661 := by
  unfold tailWord_2632193
  simp only [CollatzResearch.WordTrace]
  refine ⟨96003965753021778619581233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64002643835347852413054155 96003965753021778619581233)
  ·
    refine ⟨72002974314766333964685925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96003965753021778619581233 72002974314766333964685925)
    ·
      refine ⟨13500557684018687618378611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72002974314766333964685925 13500557684018687618378611)
      ·
        refine ⟨20250836526028031427567917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13500557684018687618378611 20250836526028031427567917)
        ·
          refine ⟨7594063697260511785337969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20250836526028031427567917 7594063697260511785337969)
          ·
            refine ⟨5695547772945383839003477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7594063697260511785337969 5695547772945383839003477)
            ·
              refine ⟨33372350232101858431661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5695547772945383839003477 33372350232101858431661)
              ·
                rfl

theorem cell22_2632193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 9].length) (baseStart_2632193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632193 prefixEnd_2632193 := by exact prefixLift 2632193
  have htrace : WordTrace (prefixWord ++ tailWord_2632193) baseStart_2632193 baseEnd_2632193 := by
    simpa [prefixWord, tailWord_2632193, baseEnd_2632193] using wordTrace_append hprefix tailTrace_2632193
  have hstable : (prefixWord ++ tailWord_2632193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632193).length < 2 ^ (prefixWord ++ tailWord_2632193).sum := by decide
  have hdescent : baseEnd_2632193 < baseStart_2632193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632225 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 3, 3]
def baseStart_2632225 : Nat := 118140960795 + 2632225 * 2 ^ 59
def prefixEnd_2632225 : Nat := 4983230072969 + 3 ^ 40 * 2632225 * 2
def baseEnd_2632225 : Nat := 901064410520712760854749

theorem tailTrace_2632225 : CollatzResearch.WordTrace tailWord_2632225 prefixEnd_2632225 901064410520712760854749 := by
  unfold tailWord_2632225
  simp only [CollatzResearch.WordTrace]
  refine ⟨96005132888905848084746129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64003421925937232056497419 96005132888905848084746129)
  ·
    refine ⟨72003849666679386063559597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96005132888905848084746129 72003849666679386063559597)
    ·
      refine ⟨27001443625004769773834849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72003849666679386063559597 27001443625004769773834849)
      ·
        refine ⟨20251082718753577330376137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27001443625004769773834849 20251082718753577330376137)
        ·
          refine ⟨15188312039065182997782103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20251082718753577330376137 15188312039065182997782103)
          ·
            refine ⟨22782468058597774496673155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15188312039065182997782103 22782468058597774496673155)
            ·
              refine ⟨34173702087896661745009733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22782468058597774496673155 34173702087896661745009733)
              ·
                refine ⟨6407569141480624077189325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34173702087896661745009733 6407569141480624077189325)
                ·
                  refine ⟨2402838428055234028945997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6407569141480624077189325 2402838428055234028945997)
                  ·
                    refine ⟨901064410520712760854749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2402838428055234028945997 901064410520712760854749)
                    ·
                      rfl

theorem cell22_2632225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_2632225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632225 prefixEnd_2632225 := by exact prefixLift 2632225
  have htrace : WordTrace (prefixWord ++ tailWord_2632225) baseStart_2632225 baseEnd_2632225 := by
    simpa [prefixWord, tailWord_2632225, baseEnd_2632225] using wordTrace_append hprefix tailTrace_2632225
  have hstable : (prefixWord ++ tailWord_2632225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632225).length < 2 ^ (prefixWord ++ tailWord_2632225).sum := by decide
  have hdescent : baseEnd_2632225 < baseStart_2632225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632244 : List Nat := [2, 5, 1, 3, 2, 1, 8]
def baseStart_2632244 : Nat := 118140960795 + 2632244 * 2 ^ 59
def prefixEnd_2632244 : Nat := 4983230072969 + 3 ^ 40 * 2632244 * 2
def baseEnd_2632244 : Nat := 33372996837370483134433

theorem tailTrace_2632244 : CollatzResearch.WordTrace tailWord_2632244 prefixEnd_2632244 33372996837370483134433 := by
  unfold tailWord_2632244
  simp only [CollatzResearch.WordTrace]
  refine ⟨48002912937918507164843893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64003883917224676219791857 48002912937918507164843893)
  ·
    refine ⟨4500273087929860046704115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48002912937918507164843893 4500273087929860046704115)
    ·
      refine ⟨6750409631894790070056173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4500273087929860046704115 6750409631894790070056173)
      ·
        refine ⟨2531403611960546276271065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6750409631894790070056173 2531403611960546276271065)
        ·
          refine ⟨1898552708970409707203299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2531403611960546276271065 1898552708970409707203299)
          ·
            refine ⟨2847829063455614560804949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898552708970409707203299 2847829063455614560804949)
            ·
              refine ⟨33372996837370483134433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2847829063455614560804949 33372996837370483134433)
              ·
                rfl

theorem cell22_2632244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 8].length) (baseStart_2632244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632244 prefixEnd_2632244 := by exact prefixLift 2632244
  have htrace : WordTrace (prefixWord ++ tailWord_2632244) baseStart_2632244 baseEnd_2632244 := by
    simpa [prefixWord, tailWord_2632244, baseEnd_2632244] using wordTrace_append hprefix tailTrace_2632244
  have hstable : (prefixWord ++ tailWord_2632244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632244).length < 2 ^ (prefixWord ++ tailWord_2632244).sum := by decide
  have hdescent : baseEnd_2632244 < baseStart_2632244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632310 : List Nat := [5, 1, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_2632310 : Nat := 118140960795 + 2632310 * 2 ^ 59
def prefixEnd_2632310 : Nat := 4983230072969 + 3 ^ 40 * 2632310 * 2
def baseEnd_2632310 : Nat := 901093507757800872479489

theorem tailTrace_2632310 : CollatzResearch.WordTrace tailWord_2632310 prefixEnd_2632310 901093507757800872479489 := by
  unfold tailWord_2632310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6000514568349869225099399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64005488729065271734393589 6000514568349869225099399)
  ·
    refine ⟨9000771852524803837649099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6000514568349869225099399 9000771852524803837649099)
    ·
      refine ⟨13501157778787205756473649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9000771852524803837649099 13501157778787205756473649)
      ·
        refine ⟨10125868334090404317355237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13501157778787205756473649 10125868334090404317355237)
        ·
          refine ⟨1898600312641950809504107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10125868334090404317355237 1898600312641950809504107)
          ·
            refine ⟨2847900468962926214256161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898600312641950809504107 2847900468962926214256161)
            ·
              refine ⟨2135925351722194660692121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2847900468962926214256161 2135925351722194660692121)
              ·
                refine ⟨1601944013791645995519091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2135925351722194660692121 1601944013791645995519091)
                ·
                  refine ⟨2402916020687468993278637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1601944013791645995519091 2402916020687468993278637)
                  ·
                    refine ⟨901093507757800872479489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2402916020687468993278637 901093507757800872479489)
                    ·
                      rfl

theorem cell22_2632310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_2632310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632310 prefixEnd_2632310 := by exact prefixLift 2632310
  have htrace : WordTrace (prefixWord ++ tailWord_2632310) baseStart_2632310 baseEnd_2632310 := by
    simpa [prefixWord, tailWord_2632310, baseEnd_2632310] using wordTrace_append hprefix tailTrace_2632310
  have hstable : (prefixWord ++ tailWord_2632310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632310).length < 2 ^ (prefixWord ++ tailWord_2632310).sum := by decide
  have hdescent : baseEnd_2632310 < baseStart_2632310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632345 : List Nat := [1, 2, 1, 2, 1, 2, 7, 6]
def baseStart_2632345 : Nat := 118140960795 + 2632345 * 2 ^ 59
def prefixEnd_2632345 : Nat := 4983230072969 + 3 ^ 40 * 2632345 * 2
def baseEnd_2632345 : Nat := 100122832108119160872709

theorem tailTrace_2632345 : CollatzResearch.WordTrace tailWord_2632345 prefixEnd_2632345 100122832108119160872709 := by
  unfold tailWord_2632345
  simp only [CollatzResearch.WordTrace]
  refine ⟨96009509648471108579114489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64006339765647405719409659 96009509648471108579114489)
  ·
    refine ⟨72007132236353331434335867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96009509648471108579114489 72007132236353331434335867)
    ·
      refine ⟨108010698354529997151503801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72007132236353331434335867 108010698354529997151503801)
      ·
        refine ⟨81008023765897497863627851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108010698354529997151503801 81008023765897497863627851)
        ·
          refine ⟨121512035648846246795441777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81008023765897497863627851 121512035648846246795441777)
          ·
            refine ⟨91134026736634685096581333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121512035648846246795441777 91134026736634685096581333)
            ·
              refine ⟨2135953751639875431951125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 91134026736634685096581333 2135953751639875431951125)
              ·
                refine ⟨100122832108119160872709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2135953751639875431951125 100122832108119160872709)
                ·
                  rfl

theorem cell22_2632345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 6].length) (baseStart_2632345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632345 prefixEnd_2632345 := by exact prefixLift 2632345
  have htrace : WordTrace (prefixWord ++ tailWord_2632345) baseStart_2632345 baseEnd_2632345 := by
    simpa [prefixWord, tailWord_2632345, baseEnd_2632345] using wordTrace_append hprefix tailTrace_2632345
  have hstable : (prefixWord ++ tailWord_2632345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632345).length < 2 ^ (prefixWord ++ tailWord_2632345).sum := by decide
  have hdescent : baseEnd_2632345 < baseStart_2632345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632366 : List Nat := [4, 1, 4, 1, 1, 1, 3, 2, 2, 3]
def baseStart_2632366 : Nat := 118140960795 + 2632366 * 2 ^ 59
def prefixEnd_2632366 : Nat := 4983230072969 + 3 ^ 40 * 2632366 * 2
def baseEnd_2632366 : Nat := 901112677702235393079317

theorem tailTrace_2632366 : CollatzResearch.WordTrace tailWord_2632366 prefixEnd_2632366 901112677702235393079317 := by
  unfold tailWord_2632366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12001284447674378645703619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64006850387596686110419301 12001284447674378645703619)
  ·
    refine ⟨18001926671511567968555429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12001284447674378645703619 18001926671511567968555429)
    ·
      refine ⟨3375361250908418994104143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18001926671511567968555429 3375361250908418994104143)
      ·
        refine ⟨5063041876362628491156215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3375361250908418994104143 5063041876362628491156215)
        ·
          refine ⟨7594562814543942736734323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5063041876362628491156215 7594562814543942736734323)
          ·
            refine ⟨11391844221815914105101485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7594562814543942736734323 11391844221815914105101485)
            ·
              refine ⟨4271941583180967789413057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11391844221815914105101485 4271941583180967789413057)
              ·
                refine ⟨3203956187385725842059793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4271941583180967789413057 3203956187385725842059793)
                ·
                  refine ⟨2402967140539294381544845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3203956187385725842059793 2402967140539294381544845)
                  ·
                    refine ⟨901112677702235393079317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2402967140539294381544845 901112677702235393079317)
                    ·
                      rfl

theorem cell22_2632366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_2632366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632366 prefixEnd_2632366 := by exact prefixLift 2632366
  have htrace : WordTrace (prefixWord ++ tailWord_2632366) baseStart_2632366 baseEnd_2632366 := by
    simpa [prefixWord, tailWord_2632366, baseEnd_2632366] using wordTrace_append hprefix tailTrace_2632366
  have hstable : (prefixWord ++ tailWord_2632366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632366).length < 2 ^ (prefixWord ++ tailWord_2632366).sum := by decide
  have hdescent : baseEnd_2632366 < baseStart_2632366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632465 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 1, 6]
def baseStart_2632465 : Nat := 118140960795 + 2632465 * 2 ^ 59
def prefixEnd_2632465 : Nat := 4983230072969 + 3 ^ 40 * 2632465 * 2
def baseEnd_2632465 : Nat := 901146567425432134854013

theorem tailTrace_2632465 : CollatzResearch.WordTrace tailWord_2632465 prefixEnd_2632465 901146567425432134854013 := by
  unfold tailWord_2632465
  simp only [CollatzResearch.WordTrace]
  refine ⟨96013886408036369073482849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64009257605357579382321899 96013886408036369073482849)
  ·
    refine ⟨72010414806027276805112137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96013886408036369073482849 72010414806027276805112137)
    ·
      refine ⟨54007811104520457603834103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72010414806027276805112137 54007811104520457603834103)
      ·
        refine ⟨81011716656780686405751155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54007811104520457603834103 81011716656780686405751155)
        ·
          refine ⟨121517574985171029608626733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81011716656780686405751155 121517574985171029608626733)
          ·
            refine ⟨45569090619439136103235025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121517574985171029608626733 45569090619439136103235025)
            ·
              refine ⟨34176817964579352077426269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45569090619439136103235025 34176817964579352077426269)
              ·
                refine ⟨12816306736717257029034851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34176817964579352077426269 12816306736717257029034851)
                ·
                  refine ⟨19224460105075885543552277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12816306736717257029034851 19224460105075885543552277)
                  ·
                    refine ⟨901146567425432134854013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19224460105075885543552277 901146567425432134854013)
                    ·
                      rfl

theorem cell22_2632465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_2632465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632465 prefixEnd_2632465 := by exact prefixLift 2632465
  have htrace : WordTrace (prefixWord ++ tailWord_2632465) baseStart_2632465 baseEnd_2632465 := by
    simpa [prefixWord, tailWord_2632465, baseEnd_2632465] using wordTrace_append hprefix tailTrace_2632465
  have hstable : (prefixWord ++ tailWord_2632465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632465).length < 2 ^ (prefixWord ++ tailWord_2632465).sum := by decide
  have hdescent : baseEnd_2632465 < baseStart_2632465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632471 : List Nat := [1, 1, 3, 4, 3, 1, 3, 1, 1, 4]
def baseStart_2632471 : Nat := 118140960795 + 2632471 * 2 ^ 59
def prefixEnd_2632471 : Nat := 4983230072969 + 3 ^ 40 * 2632471 * 2
def baseEnd_2632471 : Nat := 901148621348050119203995

theorem tailTrace_2632471 : CollatzResearch.WordTrace tailWord_2632471 prefixEnd_2632471 901148621348050119203995 := by
  unfold tailWord_2632471
  simp only [CollatzResearch.WordTrace]
  refine ⟨96014105246014632098201267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64009403497343088065467511 96014105246014632098201267)
  ·
    refine ⟨144021157869021948147301901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96014105246014632098201267 144021157869021948147301901)
    ·
      refine ⟨54007934200883230555238213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144021157869021948147301901 54007934200883230555238213)
      ·
        refine ⟨10126487662665605729107165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54007934200883230555238213 10126487662665605729107165)
        ·
          refine ⟨3797432873499602148415187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10126487662665605729107165 3797432873499602148415187)
          ·
            refine ⟨5696149310249403222622781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3797432873499602148415187 5696149310249403222622781)
            ·
              refine ⟨2136055991343526208483543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5696149310249403222622781 2136055991343526208483543)
              ·
                refine ⟨3204083987015289312725315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2136055991343526208483543 3204083987015289312725315)
                ·
                  refine ⟨4806125980522933969087973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204083987015289312725315 4806125980522933969087973)
                  ·
                    refine ⟨901148621348050119203995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4806125980522933969087973 901148621348050119203995)
                    ·
                      rfl

theorem cell22_2632471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_2632471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632471 prefixEnd_2632471 := by exact prefixLift 2632471
  have htrace : WordTrace (prefixWord ++ tailWord_2632471) baseStart_2632471 baseEnd_2632471 := by
    simpa [prefixWord, tailWord_2632471, baseEnd_2632471] using wordTrace_append hprefix tailTrace_2632471
  have hstable : (prefixWord ++ tailWord_2632471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632471).length < 2 ^ (prefixWord ++ tailWord_2632471).sum := by decide
  have hdescent : baseEnd_2632471 < baseStart_2632471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632480 : List Nat := [2, 1, 1, 5, 1, 12]
def baseStart_2632480 : Nat := 118140960795 + 2632480 * 2 ^ 59
def prefixEnd_2632480 : Nat := 4983230072969 + 3 ^ 40 * 2632480 * 2
def baseEnd_2632480 : Nat := 11125329657184902416407

theorem tailTrace_2632480 : CollatzResearch.WordTrace tailWord_2632480 prefixEnd_2632480 11125329657184902416407 := by
  unfold tailWord_2632480
  simp only [CollatzResearch.WordTrace]
  refine ⟨48007216751491013317639447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64009622335321351090185929 48007216751491013317639447)
  ·
    refine ⟨72010825127236519976459171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48007216751491013317639447 72010825127236519976459171)
    ·
      refine ⟨108016237690854779964688757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72010825127236519976459171 108016237690854779964688757)
      ·
        refine ⟨10126522283517635621689571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108016237690854779964688757 10126522283517635621689571)
        ·
          refine ⟨15189783425276453432534357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10126522283517635621689571 15189783425276453432534357)
          ·
            refine ⟨11125329657184902416407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15189783425276453432534357 11125329657184902416407)
            ·
              rfl

theorem cell22_2632480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 12].length) (baseStart_2632480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632480 prefixEnd_2632480 := by exact prefixLift 2632480
  have htrace : WordTrace (prefixWord ++ tailWord_2632480) baseStart_2632480 baseEnd_2632480 := by
    simpa [prefixWord, tailWord_2632480, baseEnd_2632480] using wordTrace_append hprefix tailTrace_2632480
  have hstable : (prefixWord ++ tailWord_2632480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632480).length < 2 ^ (prefixWord ++ tailWord_2632480).sum := by decide
  have hdescent : baseEnd_2632480 < baseStart_2632480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632516 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 1, 6]
def baseStart_2632516 : Nat := 118140960795 + 2632516 * 2 ^ 59
def prefixEnd_2632516 : Nat := 4983230072969 + 3 ^ 40 * 2632516 * 2
def baseEnd_2632516 : Nat := 901164025767685001828857

theorem tailTrace_2632516 : CollatzResearch.WordTrace tailWord_2632516 prefixEnd_2632516 901164025767685001828857 := by
  unfold tailWord_2632516
  simp only [CollatzResearch.WordTrace]
  refine ⟨48007873265425802391794701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64010497687234403189059601 48007873265425802391794701)
  ·
    refine ⟨18002952474534675896923013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48007873265425802391794701 18002952474534675896923013)
    ·
      refine ⟨3375553588975251730673065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18002952474534675896923013 3375553588975251730673065)
      ·
        refine ⟨2531665191731438798004799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3375553588975251730673065 2531665191731438798004799)
        ·
          refine ⟨3797497787597158197007199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2531665191731438798004799 3797497787597158197007199)
          ·
            refine ⟨5696246681395737295510799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3797497787597158197007199 5696246681395737295510799)
            ·
              refine ⟨8544370022093605943266199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5696246681395737295510799 8544370022093605943266199)
              ·
                refine ⟨12816555033140408914899299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8544370022093605943266199 12816555033140408914899299)
                ·
                  refine ⟨19224832549710613372348949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12816555033140408914899299 19224832549710613372348949)
                  ·
                    refine ⟨901164025767685001828857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19224832549710613372348949 901164025767685001828857)
                    ·
                      rfl

theorem cell22_2632516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_2632516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632516 prefixEnd_2632516 := by exact prefixLift 2632516
  have htrace : WordTrace (prefixWord ++ tailWord_2632516) baseStart_2632516 baseEnd_2632516 := by
    simpa [prefixWord, tailWord_2632516, baseEnd_2632516] using wordTrace_append hprefix tailTrace_2632516
  have hstable : (prefixWord ++ tailWord_2632516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632516).length < 2 ^ (prefixWord ++ tailWord_2632516).sum := by decide
  have hdescent : baseEnd_2632516 < baseStart_2632516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632572 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 3, 4]
def baseStart_2632572 : Nat := 118140960795 + 2632572 * 2 ^ 59
def prefixEnd_2632572 : Nat := 4983230072969 + 3 ^ 40 * 2632572 * 2
def baseEnd_2632572 : Nat := 901183195712119522428685

theorem tailTrace_2632572 : CollatzResearch.WordTrace tailWord_2632572 prefixEnd_2632572 901183195712119522428685 := by
  unfold tailWord_2632572
  simp only [CollatzResearch.WordTrace]
  refine ⟨48008894509324363173813985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64011859345765817565085313 48008894509324363173813985)
  ·
    refine ⟨36006670881993272380360489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48008894509324363173813985 36006670881993272380360489)
    ·
      refine ⟨27005003161494954285270367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36006670881993272380360489 27005003161494954285270367)
      ·
        refine ⟨40507504742242431427905551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27005003161494954285270367 40507504742242431427905551)
        ·
          refine ⟨60761257113363647141858327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40507504742242431427905551 60761257113363647141858327)
          ·
            refine ⟨91141885670045470712787491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60761257113363647141858327 91141885670045470712787491)
            ·
              refine ⟨136712828505068206069181237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91141885670045470712787491 136712828505068206069181237)
              ·
                refine ⟨12816827672350144318985741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136712828505068206069181237 12816827672350144318985741)
                ·
                  refine ⟨4806310377131304119619653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12816827672350144318985741 4806310377131304119619653)
                  ·
                    refine ⟨901183195712119522428685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4806310377131304119619653 901183195712119522428685)
                    ·
                      rfl

theorem cell22_2632572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_2632572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632572 prefixEnd_2632572 := by exact prefixLift 2632572
  have htrace : WordTrace (prefixWord ++ tailWord_2632572) baseStart_2632572 baseEnd_2632572 := by
    simpa [prefixWord, tailWord_2632572, baseEnd_2632572] using wordTrace_append hprefix tailTrace_2632572
  have hstable : (prefixWord ++ tailWord_2632572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632572).length < 2 ^ (prefixWord ++ tailWord_2632572).sum := by decide
  have hdescent : baseEnd_2632572 < baseStart_2632572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632617 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 4, 4]
def baseStart_2632617 : Nat := 118140960795 + 2632617 * 2 ^ 59
def prefixEnd_2632617 : Nat := 4983230072969 + 3 ^ 40 * 2632617 * 2
def baseEnd_2632617 : Nat := 901198600131754405053547

theorem tailTrace_2632617 : CollatzResearch.WordTrace tailWord_2632617 prefixEnd_2632617 901198600131754405053547 := by
  unfold tailWord_2632617
  simp only [CollatzResearch.WordTrace]
  refine ⟨96019430303485699033016105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64012953535657132688677403 96019430303485699033016105)
  ·
    refine ⟨72014572727614274274762079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96019430303485699033016105 72014572727614274274762079)
    ·
      refine ⟨108021859091421411412143119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72014572727614274274762079 108021859091421411412143119)
      ·
        refine ⟨162032788637132117118214679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108021859091421411412143119 162032788637132117118214679)
        ·
          refine ⟨243049182955698175677322019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162032788637132117118214679 243049182955698175677322019)
          ·
            refine ⟨364573774433547263515983029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243049182955698175677322019 364573774433547263515983029)
            ·
              refine ⟨34178791353145055954623409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 364573774433547263515983029 34178791353145055954623409)
              ·
                refine ⟨25634093514858791965967557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34178791353145055954623409 25634093514858791965967557)
                ·
                  refine ⟨4806392534036023493618917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25634093514858791965967557 4806392534036023493618917)
                  ·
                    refine ⟨901198600131754405053547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4806392534036023493618917 901198600131754405053547)
                    ·
                      rfl

theorem cell22_2632617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_2632617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632617 prefixEnd_2632617 := by exact prefixLift 2632617
  have htrace : WordTrace (prefixWord ++ tailWord_2632617) baseStart_2632617 baseEnd_2632617 := by
    simpa [prefixWord, tailWord_2632617, baseEnd_2632617] using wordTrace_append hprefix tailTrace_2632617
  have hstable : (prefixWord ++ tailWord_2632617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632617).length < 2 ^ (prefixWord ++ tailWord_2632617).sum := by decide
  have hdescent : baseEnd_2632617 < baseStart_2632617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632619 : List Nat := [1, 1, 1, 1, 2, 1, 1, 9, 2, 3]
def baseStart_2632619 : Nat := 118140960795 + 2632619 * 2 ^ 59
def prefixEnd_2632619 : Nat := 4983230072969 + 3 ^ 40 * 2632619 * 2
def baseEnd_2632619 : Nat := 901199284772627066503541

theorem tailTrace_2632619 : CollatzResearch.WordTrace tailWord_2632619 prefixEnd_2632619 901199284772627066503541 := by
  unfold tailWord_2632619
  simp only [CollatzResearch.WordTrace]
  refine ⟨96019503249478453374588911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64013002166318968916392607 96019503249478453374588911)
  ·
    refine ⟨144029254874217680061883367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96019503249478453374588911 144029254874217680061883367)
    ·
      refine ⟨216043882311326520092825051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144029254874217680061883367 216043882311326520092825051)
      ·
        refine ⟨324065823466989780139237577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216043882311326520092825051 324065823466989780139237577)
        ·
          refine ⟨243049367600242335104428183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324065823466989780139237577 243049367600242335104428183)
          ·
            refine ⟨364574051400363502656642275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243049367600242335104428183 364574051400363502656642275)
            ·
              refine ⟨546861077100545253984963413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364574051400363502656642275 546861077100545253984963413)
              ·
                refine ⟨3204264123636007347568145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 546861077100545253984963413 3204264123636007347568145)
                ·
                  refine ⟨2403198092727005510676109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3204264123636007347568145 2403198092727005510676109)
                  ·
                    refine ⟨901199284772627066503541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2403198092727005510676109 901199284772627066503541)
                    ·
                      rfl

theorem cell22_2632619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 3].length) (baseStart_2632619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632619 prefixEnd_2632619 := by exact prefixLift 2632619
  have htrace : WordTrace (prefixWord ++ tailWord_2632619) baseStart_2632619 baseEnd_2632619 := by
    simpa [prefixWord, tailWord_2632619, baseEnd_2632619] using wordTrace_append hprefix tailTrace_2632619
  have hstable : (prefixWord ++ tailWord_2632619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632619).length < 2 ^ (prefixWord ++ tailWord_2632619).sum := by decide
  have hdescent : baseEnd_2632619 < baseStart_2632619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632632 : List Nat := [2, 1, 2, 1, 2, 4, 2, 8]
def baseStart_2632632 : Nat := 118140960795 + 2632632 * 2 ^ 59
def prefixEnd_2632632 : Nat := 4983230072969 + 3 ^ 40 * 2632632 * 2
def baseEnd_2632632 : Nat := 100133748326477707325389

theorem tailTrace_2632632 : CollatzResearch.WordTrace tailWord_2632632 prefixEnd_2632632 100133748326477707325389 := by
  unfold tailWord_2632632
  simp only [CollatzResearch.WordTrace]
  refine ⟨48009988699215678297406075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64013318265620904396541433 48009988699215678297406075)
  ·
    refine ⟨72014983048823517446109113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48009988699215678297406075 72014983048823517446109113)
    ·
      refine ⟨54011237286617638084581835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72014983048823517446109113 54011237286617638084581835)
      ·
        refine ⟨81016855929926457126872753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54011237286617638084581835 81016855929926457126872753)
        ·
          refine ⟨60762641947444842845154565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81016855929926457126872753 60762641947444842845154565)
          ·
            refine ⟨11392995365145908033466481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60762641947444842845154565 11392995365145908033466481)
            ·
              refine ⟨8544746523859431025099861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11392995365145908033466481 8544746523859431025099861)
              ·
                refine ⟨100133748326477707325389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8544746523859431025099861 100133748326477707325389)
                ·
                  rfl

theorem cell22_2632632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 8].length) (baseStart_2632632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632632 prefixEnd_2632632 := by exact prefixLift 2632632
  have htrace : WordTrace (prefixWord ++ tailWord_2632632) baseStart_2632632 baseEnd_2632632 := by
    simpa [prefixWord, tailWord_2632632, baseEnd_2632632] using wordTrace_append hprefix tailTrace_2632632
  have hstable : (prefixWord ++ tailWord_2632632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632632).length < 2 ^ (prefixWord ++ tailWord_2632632).sum := by decide
  have hdescent : baseEnd_2632632 < baseStart_2632632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632634 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 2, 4]
def baseStart_2632634 : Nat := 118140960795 + 2632634 * 2 ^ 59
def prefixEnd_2632634 : Nat := 4983230072969 + 3 ^ 40 * 2632634 * 2
def baseEnd_2632634 : Nat := 901204419579172027378495

theorem tailTrace_2632634 : CollatzResearch.WordTrace tailWord_2632634 prefixEnd_2632634 901204419579172027378495 := by
  unfold tailWord_2632634
  simp only [CollatzResearch.WordTrace]
  refine ⟨24005012586106027734096239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64013366896282740624256637 24005012586106027734096239)
  ·
    refine ⟨36007518879159041601144359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24005012586106027734096239 36007518879159041601144359)
    ·
      refine ⟨54011278318738562401716539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36007518879159041601144359 54011278318738562401716539)
      ·
        refine ⟨81016917478107843602574809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54011278318738562401716539 81016917478107843602574809)
        ·
          refine ⟨60762688108580882701931107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81016917478107843602574809 60762688108580882701931107)
          ·
            refine ⟨91144032162871324052896661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60762688108580882701931107 91144032162871324052896661)
            ·
              refine ⟨4272376507634593314979531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91144032162871324052896661 4272376507634593314979531)
              ·
                refine ⟨6408564761451889972469297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4272376507634593314979531 6408564761451889972469297)
                ·
                  refine ⟨4806423571088917479351973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6408564761451889972469297 4806423571088917479351973)
                  ·
                    refine ⟨901204419579172027378495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4806423571088917479351973 901204419579172027378495)
                    ·
                      rfl

theorem cell22_2632634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_2632634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632634 prefixEnd_2632634 := by exact prefixLift 2632634
  have htrace : WordTrace (prefixWord ++ tailWord_2632634) baseStart_2632634 baseEnd_2632634 := by
    simpa [prefixWord, tailWord_2632634, baseEnd_2632634] using wordTrace_append hprefix tailTrace_2632634
  have hstable : (prefixWord ++ tailWord_2632634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632634).length < 2 ^ (prefixWord ++ tailWord_2632634).sum := by decide
  have hdescent : baseEnd_2632634 < baseStart_2632634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632739 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 6]
def baseStart_2632739 : Nat := 118140960795 + 2632739 * 2 ^ 59
def prefixEnd_2632739 : Nat := 4983230072969 + 3 ^ 40 * 2632739 * 2
def baseEnd_2632739 : Nat := 300413454408328917834391

theorem tailTrace_2632739 : CollatzResearch.WordTrace tailWord_2632739 prefixEnd_2632739 300413454408328917834391 := by
  unfold tailWord_2632739
  simp only [CollatzResearch.WordTrace]
  refine ⟨96023880009043713868957271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64015920006029142579304847 96023880009043713868957271)
  ·
    refine ⟨144035820013565570803435907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96023880009043713868957271 144035820013565570803435907)
    ·
      refine ⟨216053730020348356205153861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144035820013565570803435907 216053730020348356205153861)
      ·
        refine ⟨40510074378815316788466349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216053730020348356205153861 40510074378815316788466349)
        ·
          refine ⟨15191277892055743795674881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40510074378815316788466349 15191277892055743795674881)
          ·
            refine ⟨11393458419041807846756161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15191277892055743795674881 11393458419041807846756161)
            ·
              refine ⟨8545093814281355885067121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11393458419041807846756161 8545093814281355885067121)
              ·
                refine ⟨6408820360711016913800341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8545093814281355885067121 6408820360711016913800341)
                ·
                  refine ⟨300413454408328917834391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6408820360711016913800341 300413454408328917834391)
                  ·
                    rfl

theorem cell22_2632739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 6].length) (baseStart_2632739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632739 prefixEnd_2632739 := by exact prefixLift 2632739
  have htrace : WordTrace (prefixWord ++ tailWord_2632739) baseStart_2632739 baseEnd_2632739 := by
    simpa [prefixWord, tailWord_2632739, baseEnd_2632739] using wordTrace_append hprefix tailTrace_2632739
  have hstable : (prefixWord ++ tailWord_2632739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632739).length < 2 ^ (prefixWord ++ tailWord_2632739).sum := by decide
  have hdescent : baseEnd_2632739 < baseStart_2632739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632741 : List Nat := [1, 3, 1, 2, 2, 2, 4, 2, 1, 4]
def baseStart_2632741 : Nat := 118140960795 + 2632741 * 2 ^ 59
def prefixEnd_2632741 : Nat := 4983230072969 + 3 ^ 40 * 2632741 * 2
def baseEnd_2632741 : Nat := 901241047865859414953167

theorem tailTrace_2632741 : CollatzResearch.WordTrace tailWord_2632741 prefixEnd_2632741 901241047865859414953167 := by
  unfold tailWord_2632741
  simp only [CollatzResearch.WordTrace]
  refine ⟨96023952955036468210530077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64015968636690978807020051 96023952955036468210530077)
  ·
    refine ⟨36008982358138675578948779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96023952955036468210530077 36008982358138675578948779)
    ·
      refine ⟨54013473537208013368423169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36008982358138675578948779 54013473537208013368423169)
      ·
        refine ⟨40510105152906010026317377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54013473537208013368423169 40510105152906010026317377)
        ·
          refine ⟨30382578864679507519738033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40510105152906010026317377 30382578864679507519738033)
          ·
            refine ⟨22786934148509630639803525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30382578864679507519738033 22786934148509630639803525)
            ·
              refine ⟨4272550152845555744963161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22786934148509630639803525 4272550152845555744963161)
              ·
                refine ⟨3204412614634166808722371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4272550152845555744963161 3204412614634166808722371)
                ·
                  refine ⟨4806618921951250213083557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204412614634166808722371 4806618921951250213083557)
                  ·
                    refine ⟨901241047865859414953167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4806618921951250213083557 901241047865859414953167)
                    ·
                      rfl

theorem cell22_2632741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_2632741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632741 prefixEnd_2632741 := by exact prefixLift 2632741
  have htrace : WordTrace (prefixWord ++ tailWord_2632741) baseStart_2632741 baseEnd_2632741 := by
    simpa [prefixWord, tailWord_2632741, baseEnd_2632741] using wordTrace_append hprefix tailTrace_2632741
  have hstable : (prefixWord ++ tailWord_2632741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632741).length < 2 ^ (prefixWord ++ tailWord_2632741).sum := by decide
  have hdescent : baseEnd_2632741 < baseStart_2632741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632754 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_2632754 : Nat := 118140960795 + 2632754 * 2 ^ 59
def prefixEnd_2632754 : Nat := 4983230072969 + 3 ^ 40 * 2632754 * 2
def baseEnd_2632754 : Nat := 901245498031531714378127

theorem tailTrace_2632754 : CollatzResearch.WordTrace tailWord_2632754 prefixEnd_2632754 901245498031531714378127 := by
  unfold tailWord_2632754
  simp only [CollatzResearch.WordTrace]
  refine ⟨24006106775997342857688329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64016284735992914287168877 24006106775997342857688329)
  ·
    refine ⟨18004580081998007143266247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24006106775997342857688329 18004580081998007143266247)
    ·
      refine ⟨27006870122997010714899371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18004580081998007143266247 27006870122997010714899371)
      ·
        refine ⟨40510305184495516072349057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27006870122997010714899371 40510305184495516072349057)
        ·
          refine ⟨30382728888371637054261793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40510305184495516072349057 30382728888371637054261793)
          ·
            refine ⟨22787046666278727790696345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30382728888371637054261793 22787046666278727790696345)
            ·
              refine ⟨17090284999709045843022259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22787046666278727790696345 17090284999709045843022259)
              ·
                refine ⟨25635427499563568764533389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17090284999709045843022259 25635427499563568764533389)
                ·
                  refine ⟨9613285312336338286700021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25635427499563568764533389 9613285312336338286700021)
                  ·
                    refine ⟨901245498031531714378127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9613285312336338286700021 901245498031531714378127)
                    ·
                      rfl

theorem cell22_2632754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_2632754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632754 prefixEnd_2632754 := by exact prefixLift 2632754
  have htrace : WordTrace (prefixWord ++ tailWord_2632754) baseStart_2632754 baseEnd_2632754 := by
    simpa [prefixWord, tailWord_2632754, baseEnd_2632754] using wordTrace_append hprefix tailTrace_2632754
  have hstable : (prefixWord ++ tailWord_2632754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632754).length < 2 ^ (prefixWord ++ tailWord_2632754).sum := by decide
  have hdescent : baseEnd_2632754 < baseStart_2632754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632758 : List Nat := [5, 1, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_2632758 : Nat := 118140960795 + 2632758 * 2 ^ 59
def prefixEnd_2632758 : Nat := 4983230072969 + 3 ^ 40 * 2632758 * 2
def baseEnd_2632758 : Nat := 901246867313277037278115

theorem tailTrace_2632758 : CollatzResearch.WordTrace tailWord_2632758 prefixEnd_2632758 901246867313277037278115 := by
  unfold tailWord_2632758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6001535812248430007118683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64016381997316586742599285 6001535812248430007118683)
  ·
    refine ⟨9002303718372645010678025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6001535812248430007118683 9002303718372645010678025)
    ·
      refine ⟨6751727788779483758008519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9002303718372645010678025 6751727788779483758008519)
      ·
        refine ⟨10127591683169225637012779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6751727788779483758008519 10127591683169225637012779)
        ·
          refine ⟨15191387524753838455519169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10127591683169225637012779 15191387524753838455519169)
          ·
            refine ⟨11393540643565378841639377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15191387524753838455519169 11393540643565378841639377)
            ·
              refine ⟨8545155482674034131229533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11393540643565378841639377 8545155482674034131229533)
              ·
                refine ⟨3204433306002762799211075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8545155482674034131229533 3204433306002762799211075)
                ·
                  refine ⟨4806649959004144198816613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204433306002762799211075 4806649959004144198816613)
                  ·
                    refine ⟨901246867313277037278115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4806649959004144198816613 901246867313277037278115)
                    ·
                      rfl

theorem cell22_2632758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_2632758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632758 prefixEnd_2632758 := by exact prefixLift 2632758
  have htrace : WordTrace (prefixWord ++ tailWord_2632758) baseStart_2632758 baseEnd_2632758 := by
    simpa [prefixWord, tailWord_2632758, baseEnd_2632758] using wordTrace_append hprefix tailTrace_2632758
  have hstable : (prefixWord ++ tailWord_2632758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632758).length < 2 ^ (prefixWord ++ tailWord_2632758).sum := by decide
  have hdescent : baseEnd_2632758 < baseStart_2632758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632771 : List Nat := [1, 1, 1, 3, 1, 2, 4, 4, 2, 3]
def baseStart_2632771 : Nat := 118140960795 + 2632771 * 2 ^ 59
def prefixEnd_2632771 : Nat := 4983230072969 + 3 ^ 40 * 2632771 * 2
def baseEnd_2632771 : Nat := 901251317478949336703075

theorem tailTrace_2632771 : CollatzResearch.WordTrace tailWord_2632771 prefixEnd_2632771 901251317478949336703075 := by
  unfold tailWord_2632771
  simp only [CollatzResearch.WordTrace]
  refine ⟨96025047144927783334122167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64016698096618522222748111 96025047144927783334122167)
  ·
    refine ⟨144037570717391675001183251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96025047144927783334122167 144037570717391675001183251)
    ·
      refine ⟨216056356076087512501774877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144037570717391675001183251 216056356076087512501774877)
      ·
        refine ⟨81021133528532817188165579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216056356076087512501774877 81021133528532817188165579)
        ·
          refine ⟨121531700292799225782248369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81021133528532817188165579 121531700292799225782248369)
          ·
            refine ⟨91148775219599419336686277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121531700292799225782248369 91148775219599419336686277)
            ·
              refine ⟨17090395353674891125628677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91148775219599419336686277 17090395353674891125628677)
              ·
                refine ⟨3204449128814042086055377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17090395353674891125628677 3204449128814042086055377)
                ·
                  refine ⟨2403336846610531564541533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3204449128814042086055377 2403336846610531564541533)
                  ·
                    refine ⟨901251317478949336703075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2403336846610531564541533 901251317478949336703075)
                    ·
                      rfl

theorem cell22_2632771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 3].length) (baseStart_2632771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632771 prefixEnd_2632771 := by exact prefixLift 2632771
  have htrace : WordTrace (prefixWord ++ tailWord_2632771) baseStart_2632771 baseEnd_2632771 := by
    simpa [prefixWord, tailWord_2632771, baseEnd_2632771] using wordTrace_append hprefix tailTrace_2632771
  have hstable : (prefixWord ++ tailWord_2632771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632771).length < 2 ^ (prefixWord ++ tailWord_2632771).sum := by decide
  have hdescent : baseEnd_2632771 < baseStart_2632771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632910 : List Nat := [4, 1, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_2632910 : Nat := 118140960795 + 2632910 * 2 ^ 59
def prefixEnd_2632910 : Nat := 4983230072969 + 3 ^ 40 * 2632910 * 2
def baseEnd_2632910 : Nat := 901298900019599307477649

theorem tailTrace_2632910 : CollatzResearch.WordTrace tailWord_2632910 prefixEnd_2632910 901298900019599307477649 := by
  unfold tailWord_2632910
  simp only [CollatzResearch.WordTrace]
  refine ⟨12003764611428026259179023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64020077927616140048954789 12003764611428026259179023)
  ·
    refine ⟨18005646917142039388768535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12003764611428026259179023 18005646917142039388768535)
    ·
      refine ⟨27008470375713059083152803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18005646917142039388768535 27008470375713059083152803)
      ·
        refine ⟨40512705563569588624729205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27008470375713059083152803 40512705563569588624729205)
        ·
          refine ⟨3798066146584648933568363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40512705563569588624729205 3798066146584648933568363)
          ·
            refine ⟨5697099219876973400352545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3798066146584648933568363 5697099219876973400352545)
            ·
              refine ⟨4272824414907730050264409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5697099219876973400352545 4272824414907730050264409)
              ·
                refine ⟨3204618311180797537698307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4272824414907730050264409 3204618311180797537698307)
                ·
                  refine ⟨4806927466771196306547461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204618311180797537698307 4806927466771196306547461)
                  ·
                    refine ⟨901298900019599307477649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4806927466771196306547461 901298900019599307477649)
                    ·
                      rfl

theorem cell22_2632910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_2632910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632910 prefixEnd_2632910 := by exact prefixLift 2632910
  have htrace : WordTrace (prefixWord ++ tailWord_2632910) baseStart_2632910 baseEnd_2632910 := by
    simpa [prefixWord, tailWord_2632910, baseEnd_2632910] using wordTrace_append hprefix tailTrace_2632910
  have hstable : (prefixWord ++ tailWord_2632910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632910).length < 2 ^ (prefixWord ++ tailWord_2632910).sum := by decide
  have hdescent : baseEnd_2632910 < baseStart_2632910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632921 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 2, 4]
def baseStart_2632921 : Nat := 118140960795 + 2632921 * 2 ^ 59
def prefixEnd_2632921 : Nat := 4983230072969 + 3 ^ 40 * 2632921 * 2
def baseEnd_2632921 : Nat := 901302665544398945452615

theorem tailTrace_2632921 : CollatzResearch.WordTrace tailWord_2632921 prefixEnd_2632921 901302665544398945452615 := by
  unfold tailWord_2632921
  simp only [CollatzResearch.WordTrace]
  refine ⟨96030518094384358952082617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64020345396256239301388411 96030518094384358952082617)
  ·
    refine ⟨72022888570788269214061963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96030518094384358952082617 72022888570788269214061963)
    ·
      refine ⟨108034332856182403821092945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72022888570788269214061963 108034332856182403821092945)
      ·
        refine ⟨81025749642136802865819709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108034332856182403821092945 81025749642136802865819709)
        ·
          refine ⟨30384656115801301074682391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81025749642136802865819709 30384656115801301074682391)
          ·
            refine ⟨45576984173701951612023587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30384656115801301074682391 45576984173701951612023587)
            ·
              refine ⟨68365476260552927418035381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45576984173701951612023587 68365476260552927418035381)
              ·
                refine ⟨6409263399426836945440817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68365476260552927418035381 6409263399426836945440817)
                ·
                  refine ⟨4806947549570127709080613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6409263399426836945440817 4806947549570127709080613)
                  ·
                    refine ⟨901302665544398945452615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4806947549570127709080613 901302665544398945452615)
                    ·
                      rfl

theorem cell22_2632921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_2632921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632921 prefixEnd_2632921 := by exact prefixLift 2632921
  have htrace : WordTrace (prefixWord ++ tailWord_2632921) baseStart_2632921 baseEnd_2632921 := by
    simpa [prefixWord, tailWord_2632921, baseEnd_2632921] using wordTrace_append hprefix tailTrace_2632921
  have hstable : (prefixWord ++ tailWord_2632921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632921).length < 2 ^ (prefixWord ++ tailWord_2632921).sum := by decide
  have hdescent : baseEnd_2632921 < baseStart_2632921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632938 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 2, 4]
def baseStart_2632938 : Nat := 118140960795 + 2632938 * 2 ^ 59
def prefixEnd_2632938 : Nat := 4983230072969 + 3 ^ 40 * 2632938 * 2
def baseEnd_2632938 : Nat := 901308484991816567777563

theorem tailTrace_2632938 : CollatzResearch.WordTrace tailWord_2632938 prefixEnd_2632938 901308484991816567777563 := by
  unfold tailWord_2632938
  simp only [CollatzResearch.WordTrace]
  refine ⟨24007784533830692713862867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64020758756881847236967645 24007784533830692713862867)
  ·
    refine ⟨36011676800746039070794301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24007784533830692713862867 36011676800746039070794301)
    ·
      refine ⟨13504378800279764651547863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36011676800746039070794301 13504378800279764651547863)
      ·
        refine ⟨20256568200419646977321795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13504378800279764651547863 20256568200419646977321795)
        ·
          refine ⟨30384852300629470465982693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20256568200419646977321795 30384852300629470465982693)
          ·
            refine ⟨5697159806368025712371755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30384852300629470465982693 5697159806368025712371755)
            ·
              refine ⟨8545739709552038568557633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5697159806368025712371755 8545739709552038568557633)
              ·
                refine ⟨6409304782164028926418225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8545739709552038568557633 6409304782164028926418225)
                ·
                  refine ⟨4806978586623021694813669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6409304782164028926418225 4806978586623021694813669)
                  ·
                    refine ⟨901308484991816567777563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4806978586623021694813669 901308484991816567777563)
                    ·
                      rfl

theorem cell22_2632938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_2632938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2632938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2632938 prefixEnd_2632938 := by exact prefixLift 2632938
  have htrace : WordTrace (prefixWord ++ tailWord_2632938) baseStart_2632938 baseEnd_2632938 := by
    simpa [prefixWord, tailWord_2632938, baseEnd_2632938] using wordTrace_append hprefix tailTrace_2632938
  have hstable : (prefixWord ++ tailWord_2632938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632938).length < 2 ^ (prefixWord ++ tailWord_2632938).sum := by decide
  have hdescent : baseEnd_2632938 < baseStart_2632938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633013 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 2, 5]
def baseStart_2633013 : Nat := 118140960795 + 2633013 * 2 ^ 59
def prefixEnd_2633013 : Nat := 4983230072969 + 3 ^ 40 * 2633013 * 2
def baseEnd_2633013 : Nat := 901334159024541372152333

theorem tailTrace_2633013 : CollatzResearch.WordTrace tailWord_2633013 prefixEnd_2633013 901334159024541372152333 := by
  unfold tailWord_2633013
  simp only [CollatzResearch.WordTrace]
  refine ⟨96033873610051058664431693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64022582406700705776287795 96033873610051058664431693)
  ·
    refine ⟨36012702603769146999161885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96033873610051058664431693 36012702603769146999161885)
    ·
      refine ⟨13504763476413430124685707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36012702603769146999161885 13504763476413430124685707)
      ·
        refine ⟨20257145214620145187028561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13504763476413430124685707 20257145214620145187028561)
        ·
          refine ⟨15192858910965108890271421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20257145214620145187028561 15192858910965108890271421)
          ·
            refine ⟨5697322091611915833851783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15192858910965108890271421 5697322091611915833851783)
            ·
              refine ⟨8545983137417873750777675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5697322091611915833851783 8545983137417873750777675)
              ·
                refine ⟨12818974706126810626166513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8545983137417873750777675 12818974706126810626166513)
                ·
                  refine ⟨9614231029595107969624885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12818974706126810626166513 9614231029595107969624885)
                  ·
                    refine ⟨901334159024541372152333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9614231029595107969624885 901334159024541372152333)
                    ·
                      rfl

theorem cell22_2633013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_2633013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633013 prefixEnd_2633013 := by exact prefixLift 2633013
  have htrace : WordTrace (prefixWord ++ tailWord_2633013) baseStart_2633013 baseEnd_2633013 := by
    simpa [prefixWord, tailWord_2633013, baseEnd_2633013] using wordTrace_append hprefix tailTrace_2633013
  have hstable : (prefixWord ++ tailWord_2633013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633013).length < 2 ^ (prefixWord ++ tailWord_2633013).sum := by decide
  have hdescent : baseEnd_2633013 < baseStart_2633013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633045 : List Nat := [1, 3, 2, 2, 3, 2, 1, 3, 1, 4]
def baseStart_2633045 : Nat := 118140960795 + 2633045 * 2 ^ 59
def prefixEnd_2633045 : Nat := 4983230072969 + 3 ^ 40 * 2633045 * 2
def baseEnd_2633045 : Nat := 901345113278503955352235

theorem tailTrace_2633045 : CollatzResearch.WordTrace tailWord_2633045 prefixEnd_2633045 901345113278503955352235 := by
  unfold tailWord_2633045
  simp only [CollatzResearch.WordTrace]
  refine ⟨96035040745935128129596589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64023360497290085419731059 96035040745935128129596589)
  ·
    refine ⟨36013140279725673048598721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96035040745935128129596589 36013140279725673048598721)
    ·
      refine ⟨27009855209794254786449041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36013140279725673048598721 27009855209794254786449041)
      ·
        refine ⟨20257391407345691089836781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27009855209794254786449041 20257391407345691089836781)
        ·
          refine ⟨7596521777754634158688793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20257391407345691089836781 7596521777754634158688793)
          ·
            refine ⟨5697391333315975619016595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7596521777754634158688793 5697391333315975619016595)
            ·
              refine ⟨8546086999973963428524893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5697391333315975619016595 8546086999973963428524893)
              ·
                refine ⟨3204782624990236285696835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8546086999973963428524893 3204782624990236285696835)
                ·
                  refine ⟨4807173937485354428545253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204782624990236285696835 4807173937485354428545253)
                  ·
                    refine ⟨901345113278503955352235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4807173937485354428545253 901345113278503955352235)
                    ·
                      rfl

theorem cell22_2633045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_2633045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633045 prefixEnd_2633045 := by exact prefixLift 2633045
  have htrace : WordTrace (prefixWord ++ tailWord_2633045) baseStart_2633045 baseEnd_2633045 := by
    simpa [prefixWord, tailWord_2633045, baseEnd_2633045] using wordTrace_append hprefix tailTrace_2633045
  have hstable : (prefixWord ++ tailWord_2633045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633045).length < 2 ^ (prefixWord ++ tailWord_2633045).sum := by decide
  have hdescent : baseEnd_2633045 < baseStart_2633045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633060 : List Nat := [2, 3, 1, 1, 3, 2, 2, 4, 4]
def baseStart_2633060 : Nat := 118140960795 + 2633060 * 2 ^ 59
def prefixEnd_2633060 : Nat := 4983230072969 + 3 ^ 40 * 2633060 * 2
def baseEnd_2633060 : Nat := 300450082695016305409063

theorem tailTrace_2633060 : CollatzResearch.WordTrace tailWord_2633060 prefixEnd_2633060 300450082695016305409063 := by
  unfold tailWord_2633060
  simp only [CollatzResearch.WordTrace]
  refine ⟨48017793920440392845696317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64023725227253857127595089 48017793920440392845696317)
  ·
    refine ⟨18006672720165147317136119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48017793920440392845696317 18006672720165147317136119)
    ·
      refine ⟨27010009080247720975704179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18006672720165147317136119 27010009080247720975704179)
      ·
        refine ⟨40515013620371581463556269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27010009080247720975704179 40515013620371581463556269)
        ·
          refine ⟨15193130107639343048833601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40515013620371581463556269 15193130107639343048833601)
          ·
            refine ⟨11394847580729507286625201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15193130107639343048833601 11394847580729507286625201)
            ·
              refine ⟨8546135685547130464968901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11394847580729507286625201 8546135685547130464968901)
              ·
                refine ⟨1602400441040086962181669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8546135685547130464968901 1602400441040086962181669)
                ·
                  refine ⟨300450082695016305409063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1602400441040086962181669 300450082695016305409063)
                  ·
                    rfl

theorem cell22_2633060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_2633060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633060 prefixEnd_2633060 := by exact prefixLift 2633060
  have htrace : WordTrace (prefixWord ++ tailWord_2633060) baseStart_2633060 baseEnd_2633060 := by
    simpa [prefixWord, tailWord_2633060, baseEnd_2633060] using wordTrace_append hprefix tailTrace_2633060
  have hstable : (prefixWord ++ tailWord_2633060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633060).length < 2 ^ (prefixWord ++ tailWord_2633060).sum := by decide
  have hdescent : baseEnd_2633060 < baseStart_2633060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633071 : List Nat := [1, 1, 2, 1, 3, 1, 4, 9]
def baseStart_2633071 : Nat := 118140960795 + 2633071 * 2 ^ 59
def prefixEnd_2633071 : Nat := 4983230072969 + 3 ^ 40 * 2633071 * 2
def baseEnd_2633071 : Nat := 100150445956649839355795

theorem tailTrace_2633071 : CollatzResearch.WordTrace tailWord_2633071 prefixEnd_2633071 100150445956649839355795 := by
  unfold tailWord_2633071
  simp only [CollatzResearch.WordTrace]
  refine ⟨96035989043840934570043067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64023992695893956380028711 96035989043840934570043067)
  ·
    refine ⟨144053983565761401855064601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96035989043840934570043067 144053983565761401855064601)
    ·
      refine ⟨108040487674321051391298451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144053983565761401855064601 108040487674321051391298451)
      ·
        refine ⟨162060731511481577086947677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108040487674321051391298451 162060731511481577086947677)
        ·
          refine ⟨60772774316805591407605379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162060731511481577086947677 60772774316805591407605379)
          ·
            refine ⟨91159161475208387111408069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60772774316805591407605379 91159161475208387111408069)
            ·
              refine ⟨17092342776601572583389013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91159161475208387111408069 17092342776601572583389013)
              ·
                refine ⟨100150445956649839355795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17092342776601572583389013 100150445956649839355795)
                ·
                  rfl

theorem cell22_2633071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 9].length) (baseStart_2633071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633071 prefixEnd_2633071 := by exact prefixLift 2633071
  have htrace : WordTrace (prefixWord ++ tailWord_2633071) baseStart_2633071 baseEnd_2633071 := by
    simpa [prefixWord, tailWord_2633071, baseEnd_2633071] using wordTrace_append hprefix tailTrace_2633071
  have hstable : (prefixWord ++ tailWord_2633071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633071).length < 2 ^ (prefixWord ++ tailWord_2633071).sum := by decide
  have hdescent : baseEnd_2633071 < baseStart_2633071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633210 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 4, 3]
def baseStart_2633210 : Nat := 118140960795 + 2633210 * 2 ^ 59
def prefixEnd_2633210 : Nat := 4983230072969 + 3 ^ 40 * 2633210 * 2
def baseEnd_2633210 : Nat := 901401596150498524976729

theorem tailTrace_2633210 : CollatzResearch.WordTrace tailWord_2633210 prefixEnd_2633210 901401596150498524976729 := by
  unfold tailWord_2633210
  simp only [CollatzResearch.WordTrace]
  refine ⟨24010264697584340327338271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64027372526891574206235389 24010264697584340327338271)
  ·
    refine ⟨36015397046376510491007407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24010264697584340327338271 36015397046376510491007407)
    ·
      refine ⟨54023095569564765736511111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36015397046376510491007407 54023095569564765736511111)
      ·
        refine ⟨81034643354347148604766667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54023095569564765736511111 81034643354347148604766667)
        ·
          refine ⟨121551965031520722907150001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81034643354347148604766667 121551965031520722907150001)
          ·
            refine ⟨91163973773640542180362501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121551965031520722907150001 91163973773640542180362501)
            ·
              refine ⟨17093245082557601658817969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91163973773640542180362501 17093245082557601658817969)
              ·
                refine ⟨12819933811918201244113477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17093245082557601658817969 12819933811918201244113477)
                ·
                  refine ⟨2403737589734662733271277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12819933811918201244113477 2403737589734662733271277)
                  ·
                    refine ⟨901401596150498524976729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2403737589734662733271277 901401596150498524976729)
                    ·
                      rfl

theorem cell22_2633210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_2633210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633210 prefixEnd_2633210 := by exact prefixLift 2633210
  have htrace : WordTrace (prefixWord ++ tailWord_2633210) baseStart_2633210 baseEnd_2633210 := by
    simpa [prefixWord, tailWord_2633210, baseEnd_2633210] using wordTrace_append hprefix tailTrace_2633210
  have hstable : (prefixWord ++ tailWord_2633210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633210).length < 2 ^ (prefixWord ++ tailWord_2633210).sum := by decide
  have hdescent : baseEnd_2633210 < baseStart_2633210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633227 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 4, 3]
def baseStart_2633227 : Nat := 118140960795 + 2633227 * 2 ^ 59
def prefixEnd_2633227 : Nat := 4983230072969 + 3 ^ 40 * 2633227 * 2
def baseEnd_2633227 : Nat := 901407415597916147301677

theorem tailTrace_2633227 : CollatzResearch.WordTrace tailWord_2633227 prefixEnd_2633227 901407415597916147301677 := by
  unfold tailWord_2633227
  simp only [CollatzResearch.WordTrace]
  refine ⟨96041678831275773212721935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64027785887517182141814623 96041678831275773212721935)
  ·
    refine ⟨144062518246913659819082903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96041678831275773212721935 144062518246913659819082903)
    ·
      refine ⟨216093777370370489728624355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144062518246913659819082903 216093777370370489728624355)
      ·
        refine ⟨324140666055555734592936533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216093777370370489728624355 324140666055555734592936533)
        ·
          refine ⟨3798523430338543764760975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 324140666055555734592936533 3798523430338543764760975)
          ·
            refine ⟨5697785145507815647141463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3798523430338543764760975 5697785145507815647141463)
            ·
              refine ⟨8546677718261723470712195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5697785145507815647141463 8546677718261723470712195)
              ·
                refine ⟨12820016577392585206068293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8546677718261723470712195 12820016577392585206068293)
                ·
                  refine ⟨2403753108261109726137805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12820016577392585206068293 2403753108261109726137805)
                  ·
                    refine ⟨901407415597916147301677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2403753108261109726137805 901407415597916147301677)
                    ·
                      rfl

theorem cell22_2633227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 3].length) (baseStart_2633227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633227 prefixEnd_2633227 := by exact prefixLift 2633227
  have htrace : WordTrace (prefixWord ++ tailWord_2633227) baseStart_2633227 baseEnd_2633227 := by
    simpa [prefixWord, tailWord_2633227, baseEnd_2633227] using wordTrace_append hprefix tailTrace_2633227
  have hstable : (prefixWord ++ tailWord_2633227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633227).length < 2 ^ (prefixWord ++ tailWord_2633227).sum := by decide
  have hdescent : baseEnd_2633227 < baseStart_2633227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633244 : List Nat := [2, 2, 3, 1, 2, 1, 5, 1, 2, 3]
def baseStart_2633244 : Nat := 118140960795 + 2633244 * 2 ^ 59
def prefixEnd_2633244 : Nat := 4983230072969 + 3 ^ 40 * 2633244 * 2
def baseEnd_2633244 : Nat := 901413235045333769626625

theorem tailTrace_2633244 : CollatzResearch.WordTrace tailWord_2633244 prefixEnd_2633244 901413235045333769626625 := by
  unfold tailWord_2633244
  simp only [CollatzResearch.WordTrace]
  refine ⟨48021149436107092558045393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64028199248142790077393857 48021149436107092558045393)
  ·
    refine ⟨36015862077080319418534045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48021149436107092558045393 36015862077080319418534045)
    ·
      refine ⟨13505948278905119781950267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36015862077080319418534045 13505948278905119781950267)
      ·
        refine ⟨20258922418357679672925401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13505948278905119781950267 20258922418357679672925401)
        ·
          refine ⟨15194191813768259754694051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20258922418357679672925401 15194191813768259754694051)
          ·
            refine ⟨22791287720652389632041077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15194191813768259754694051 22791287720652389632041077)
            ·
              refine ⟨2136683223811161528003851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22791287720652389632041077 2136683223811161528003851)
              ·
                refine ⟨3205024835716742292005777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2136683223811161528003851 3205024835716742292005777)
                ·
                  refine ⟨2403768626787556719004333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3205024835716742292005777 2403768626787556719004333)
                  ·
                    refine ⟨901413235045333769626625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2403768626787556719004333 901413235045333769626625)
                    ·
                      rfl

theorem cell22_2633244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_2633244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633244 prefixEnd_2633244 := by exact prefixLift 2633244
  have htrace : WordTrace (prefixWord ++ tailWord_2633244) baseStart_2633244 baseEnd_2633244 := by
    simpa [prefixWord, tailWord_2633244, baseEnd_2633244] using wordTrace_append hprefix tailTrace_2633244
  have hstable : (prefixWord ++ tailWord_2633244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633244).length < 2 ^ (prefixWord ++ tailWord_2633244).sum := by decide
  have hdescent : baseEnd_2633244 < baseStart_2633244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633285 : List Nat := [1, 3, 1, 1, 1, 4, 2, 4, 5]
def baseStart_2633285 : Nat := 118140960795 + 2633285 * 2 ^ 59
def prefixEnd_2633285 : Nat := 4983230072969 + 3 ^ 40 * 2633285 * 2
def baseEnd_2633285 : Nat := 300475756727741109783833

theorem tailTrace_2633285 : CollatzResearch.WordTrace tailWord_2633285 prefixEnd_2633285 300475756727741109783833 := by
  unfold tailWord_2633285
  simp only [CollatzResearch.WordTrace]
  refine ⟨96043794265065649118333309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64029196176710432745555539 96043794265065649118333309)
  ·
    refine ⟨36016422849399618419374991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96043794265065649118333309 36016422849399618419374991)
    ·
      refine ⟨54024634274099427629062487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36016422849399618419374991 54024634274099427629062487)
      ·
        refine ⟨81036951411149141443593731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54024634274099427629062487 81036951411149141443593731)
        ·
          refine ⟨121555427116723712165390597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81036951411149141443593731 121555427116723712165390597)
          ·
            refine ⟨22791642584385696031010737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121555427116723712165390597 22791642584385696031010737)
            ·
              refine ⟨17093731938289272023258053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22791642584385696031010737 17093731938289272023258053)
              ·
                refine ⟨3205074738429238504360885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17093731938289272023258053 3205074738429238504360885)
                ·
                  refine ⟨300475756727741109783833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3205074738429238504360885 300475756727741109783833)
                  ·
                    rfl

theorem cell22_2633285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_2633285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633285 prefixEnd_2633285 := by exact prefixLift 2633285
  have htrace : WordTrace (prefixWord ++ tailWord_2633285) baseStart_2633285 baseEnd_2633285 := by
    simpa [prefixWord, tailWord_2633285, baseEnd_2633285] using wordTrace_append hprefix tailTrace_2633285
  have hstable : (prefixWord ++ tailWord_2633285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633285).length < 2 ^ (prefixWord ++ tailWord_2633285).sum := by decide
  have hdescent : baseEnd_2633285 < baseStart_2633285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633300 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_2633300 : Nat := 118140960795 + 2633300 * 2 ^ 59
def prefixEnd_2633300 : Nat := 4983230072969 + 3 ^ 40 * 2633300 * 2
def baseEnd_2633300 : Nat := 901432404989768290226453

theorem tailTrace_2633300 : CollatzResearch.WordTrace tailWord_2633300 prefixEnd_2633300 901432404989768290226453 := by
  unfold tailWord_2633300
  simp only [CollatzResearch.WordTrace]
  refine ⟨48022170680005653340064677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64029560906674204453419569 48022170680005653340064677)
  ·
    refine ⟨9004157002501060001262127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48022170680005653340064677 9004157002501060001262127)
    ·
      refine ⟨13506235503751590001893191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9004157002501060001262127 13506235503751590001893191)
      ·
        refine ⟨20259353255627385002839787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13506235503751590001893191 20259353255627385002839787)
        ·
          refine ⟨30389029883441077504259681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20259353255627385002839787 30389029883441077504259681)
          ·
            refine ⟨22791772412580808128194761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30389029883441077504259681 22791772412580808128194761)
            ·
              refine ⟨17093829309435606096146071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22791772412580808128194761 17093829309435606096146071)
              ·
                refine ⟨25640743964153409144219107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17093829309435606096146071 25640743964153409144219107)
                ·
                  refine ⟨38461115946230113716328661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25640743964153409144219107 38461115946230113716328661)
                  ·
                    refine ⟨901432404989768290226453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38461115946230113716328661 901432404989768290226453)
                    ·
                      rfl

theorem cell22_2633300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2633300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633300 prefixEnd_2633300 := by exact prefixLift 2633300
  have htrace : WordTrace (prefixWord ++ tailWord_2633300) baseStart_2633300 baseEnd_2633300 := by
    simpa [prefixWord, tailWord_2633300, baseEnd_2633300] using wordTrace_append hprefix tailTrace_2633300
  have hstable : (prefixWord ++ tailWord_2633300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633300).length < 2 ^ (prefixWord ++ tailWord_2633300).sum := by decide
  have hdescent : baseEnd_2633300 < baseStart_2633300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633360 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 4, 4]
def baseStart_2633360 : Nat := 118140960795 + 2633360 * 2 ^ 59
def prefixEnd_2633360 : Nat := 4983230072969 + 3 ^ 40 * 2633360 * 2
def baseEnd_2633360 : Nat := 901452944215948133726269

theorem tailTrace_2633360 : CollatzResearch.WordTrace tailWord_2633360 prefixEnd_2633360 901452944215948133726269 := by
  unfold tailWord_2633360
  simp only [CollatzResearch.WordTrace]
  refine ⟨48023264869896968463656767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64031019826529291284875689 48023264869896968463656767)
  ·
    refine ⟨72034897304845452695485151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48023264869896968463656767 72034897304845452695485151)
    ·
      refine ⟨108052345957268179043227727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72034897304845452695485151 108052345957268179043227727)
      ·
        refine ⟨162078518935902268564841591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108052345957268179043227727 162078518935902268564841591)
        ·
          refine ⟨243117778403853402847262387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162078518935902268564841591 243117778403853402847262387)
          ·
            refine ⟨364676667605780104270893581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243117778403853402847262387 364676667605780104270893581)
            ·
              refine ⟨136753750352167539101585093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 364676667605780104270893581 136753750352167539101585093)
              ·
                refine ⟨25641328191031413581547205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136753750352167539101585093 25641328191031413581547205)
                ·
                  refine ⟨4807749035818390046540101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25641328191031413581547205 4807749035818390046540101)
                  ·
                    refine ⟨901452944215948133726269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4807749035818390046540101 901452944215948133726269)
                    ·
                      rfl

theorem cell22_2633360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_2633360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633360 prefixEnd_2633360 := by exact prefixLift 2633360
  have htrace : WordTrace (prefixWord ++ tailWord_2633360) baseStart_2633360 baseEnd_2633360 := by
    simpa [prefixWord, tailWord_2633360, baseEnd_2633360] using wordTrace_append hprefix tailTrace_2633360
  have hstable : (prefixWord ++ tailWord_2633360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633360).length < 2 ^ (prefixWord ++ tailWord_2633360).sum := by decide
  have hdescent : baseEnd_2633360 < baseStart_2633360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633364 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 6]
def baseStart_2633364 : Nat := 118140960795 + 2633364 * 2 ^ 59
def prefixEnd_2633364 : Nat := 4983230072969 + 3 ^ 40 * 2633364 * 2
def baseEnd_2633364 : Nat := 300484771165897818875419

theorem tailTrace_2633364 : CollatzResearch.WordTrace tailWord_2633364 prefixEnd_2633364 300484771165897818875419 := by
  unfold tailWord_2633364
  simp only [CollatzResearch.WordTrace]
  refine ⟨48023337815889722805229573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64031117087852963740306097 48023337815889722805229573)
  ·
    refine ⟨9004375840479323025980545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48023337815889722805229573 9004375840479323025980545)
    ·
      refine ⟨6753281880359492269485409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9004375840479323025980545 6753281880359492269485409)
      ·
        refine ⟨5064961410269619202114057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6753281880359492269485409 5064961410269619202114057)
        ·
          refine ⟨3798721057702214401585543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5064961410269619202114057 3798721057702214401585543)
          ·
            refine ⟨5698081586553321602378315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3798721057702214401585543 5698081586553321602378315)
            ·
              refine ⟨8547122379829982403567473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5698081586553321602378315 8547122379829982403567473)
              ·
                refine ⟨6410341784872486802675605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8547122379829982403567473 6410341784872486802675605)
                ·
                  refine ⟨300484771165897818875419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6410341784872486802675605 300484771165897818875419)
                  ·
                    rfl

theorem cell22_2633364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_2633364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633364 prefixEnd_2633364 := by exact prefixLift 2633364
  have htrace : WordTrace (prefixWord ++ tailWord_2633364) baseStart_2633364 baseEnd_2633364 := by
    simpa [prefixWord, tailWord_2633364, baseEnd_2633364] using wordTrace_append hprefix tailTrace_2633364
  have hstable : (prefixWord ++ tailWord_2633364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633364).length < 2 ^ (prefixWord ++ tailWord_2633364).sum := by decide
  have hdescent : baseEnd_2633364 < baseStart_2633364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633377 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 1, 6]
def baseStart_2633377 : Nat := 118140960795 + 2633377 * 2 ^ 59
def prefixEnd_2633377 : Nat := 4983230072969 + 3 ^ 40 * 2633377 * 2
def baseEnd_2633377 : Nat := 901458763663365756051217

theorem tailTrace_2633377 : CollatzResearch.WordTrace tailWord_2633377 prefixEnd_2633377 901458763663365756051217 := by
  unfold tailWord_2633377
  simp only [CollatzResearch.WordTrace]
  refine ⟨96047149780732348830682385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64031433187154899220454923 96047149780732348830682385)
  ·
    refine ⟨72035362335549261623011789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96047149780732348830682385 72035362335549261623011789)
    ·
      refine ⟨27013260875830973108629421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72035362335549261623011789 27013260875830973108629421)
      ·
        refine ⟨10129972828436614915736033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27013260875830973108629421 10129972828436614915736033)
        ·
          refine ⟨7597479621327461186802025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10129972828436614915736033 7597479621327461186802025)
          ·
            refine ⟨5698109715995595890101519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7597479621327461186802025 5698109715995595890101519)
            ·
              refine ⟨8547164573993393835152279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5698109715995595890101519 8547164573993393835152279)
              ·
                refine ⟨12820746860990090752728419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8547164573993393835152279 12820746860990090752728419)
                ·
                  refine ⟨19231120291485136129092629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12820746860990090752728419 19231120291485136129092629)
                  ·
                    refine ⟨901458763663365756051217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19231120291485136129092629 901458763663365756051217)
                    ·
                      rfl

theorem cell22_2633377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_2633377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633377 prefixEnd_2633377 := by exact prefixLift 2633377
  have htrace : WordTrace (prefixWord ++ tailWord_2633377) baseStart_2633377 baseEnd_2633377 := by
    simpa [prefixWord, tailWord_2633377, baseEnd_2633377] using wordTrace_append hprefix tailTrace_2633377
  have hstable : (prefixWord ++ tailWord_2633377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633377).length < 2 ^ (prefixWord ++ tailWord_2633377).sum := by decide
  have hdescent : baseEnd_2633377 < baseStart_2633377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633458 : List Nat := [3, 2, 1, 3, 1, 1, 5, 2, 1, 3]
def baseStart_2633458 : Nat := 118140960795 + 2633458 * 2 ^ 59
def prefixEnd_2633458 : Nat := 4983230072969 + 3 ^ 40 * 2633458 * 2
def baseEnd_2633458 : Nat := 901486491618708544775969

theorem tailTrace_2633458 : CollatzResearch.WordTrace tailWord_2633458 prefixEnd_2633458 901486491618708544775969 := by
  unfold tailWord_2633458
  simp only [CollatzResearch.WordTrace]
  refine ⟨24012526023359724916095257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64033402728959266442920685 24012526023359724916095257)
  ·
    refine ⟨18009394517519793687071443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24012526023359724916095257 18009394517519793687071443)
    ·
      refine ⟨27014091776279690530607165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18009394517519793687071443 27014091776279690530607165)
      ·
        refine ⟨10130284416104883948977687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27014091776279690530607165 10130284416104883948977687)
        ·
          refine ⟨15195426624157325923466531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10130284416104883948977687 15195426624157325923466531)
          ·
            refine ⟨22793139936235988885199797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15195426624157325923466531 22793139936235988885199797)
            ·
              refine ⟨2136856869022123957987481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22793139936235988885199797 2136856869022123957987481)
              ·
                refine ⟨1602642651766592968490611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2136856869022123957987481 1602642651766592968490611)
                ·
                  refine ⟨2403963977649889452735917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1602642651766592968490611 2403963977649889452735917)
                  ·
                    refine ⟨901486491618708544775969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2403963977649889452735917 901486491618708544775969)
                    ·
                      rfl

theorem cell22_2633458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_2633458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633458 prefixEnd_2633458 := by exact prefixLift 2633458
  have htrace : WordTrace (prefixWord ++ tailWord_2633458) baseStart_2633458 baseEnd_2633458 := by
    simpa [prefixWord, tailWord_2633458, baseEnd_2633458] using wordTrace_append hprefix tailTrace_2633458
  have hstable : (prefixWord ++ tailWord_2633458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633458).length < 2 ^ (prefixWord ++ tailWord_2633458).sum := by decide
  have hdescent : baseEnd_2633458 < baseStart_2633458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633484 : List Nat := [2, 2, 1, 2, 2, 1, 5, 2, 1, 4]
def baseStart_2633484 : Nat := 118140960795 + 2633484 * 2 ^ 59
def prefixEnd_2633484 : Nat := 4983230072969 + 3 ^ 40 * 2633484 * 2
def baseEnd_2633484 : Nat := 901495391950053143625889

theorem tailTrace_2633484 : CollatzResearch.WordTrace tailWord_2633484 prefixEnd_2633484 901495391950053143625889 := by
  unfold tailWord_2633484
  simp only [CollatzResearch.WordTrace]
  refine ⟨48025526195672353052413753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64034034927563137403218337 48025526195672353052413753)
  ·
    refine ⟨36019144646754264789310315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48025526195672353052413753 36019144646754264789310315)
    ·
      refine ⟨54028716970131397183965473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36019144646754264789310315 54028716970131397183965473)
      ·
        refine ⟨40521537727598547887974105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54028716970131397183965473 40521537727598547887974105)
        ·
          refine ⟨30391153295698910915980579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40521537727598547887974105 30391153295698910915980579)
          ·
            refine ⟨45586729943548366373970869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30391153295698910915980579 45586729943548366373970869)
            ·
              refine ⟨4273755932207659347559769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45586729943548366373970869 4273755932207659347559769)
              ·
                refine ⟨3205316949155744510669827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4273755932207659347559769 3205316949155744510669827)
                ·
                  refine ⟨4807975423733616766004741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3205316949155744510669827 4807975423733616766004741)
                  ·
                    refine ⟨901495391950053143625889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4807975423733616766004741 901495391950053143625889)
                    ·
                      rfl

theorem cell22_2633484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_2633484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633484 prefixEnd_2633484 := by exact prefixLift 2633484
  have htrace : WordTrace (prefixWord ++ tailWord_2633484) baseStart_2633484 baseEnd_2633484 := by
    simpa [prefixWord, tailWord_2633484, baseEnd_2633484] using wordTrace_append hprefix tailTrace_2633484
  have hstable : (prefixWord ++ tailWord_2633484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633484).length < 2 ^ (prefixWord ++ tailWord_2633484).sum := by decide
  have hdescent : baseEnd_2633484 < baseStart_2633484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633516 : List Nat := [2, 2, 1, 1, 1, 5, 4, 2, 4]
def baseStart_2633516 : Nat := 118140960795 + 2633516 * 2 ^ 59
def prefixEnd_2633516 : Nat := 4983230072969 + 3 ^ 40 * 2633516 * 2
def baseEnd_2633516 : Nat := 300502115401338575608597

theorem tailTrace_2633516 : CollatzResearch.WordTrace tailWord_2633516 prefixEnd_2633516 300502115401338575608597 := by
  unfold tailWord_2633516
  simp only [CollatzResearch.WordTrace]
  refine ⟨48026109763614387784996201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64034813018152517046661601 48026109763614387784996201)
  ·
    refine ⟨36019582322710790838747151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48026109763614387784996201 36019582322710790838747151)
    ·
      refine ⟨54029373484066186258120727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36019582322710790838747151 54029373484066186258120727)
      ·
        refine ⟨81044060226099279387181091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54029373484066186258120727 81044060226099279387181091)
        ·
          refine ⟨121566090339148919080771637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81044060226099279387181091 121566090339148919080771637)
          ·
            refine ⟨11396820969295211163822341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121566090339148919080771637 11396820969295211163822341)
            ·
              refine ⟨2136903931742852093216689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11396820969295211163822341 2136903931742852093216689)
              ·
                refine ⟨1602677948807139069912517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2136903931742852093216689 1602677948807139069912517)
                ·
                  refine ⟨300502115401338575608597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1602677948807139069912517 300502115401338575608597)
                  ·
                    rfl

theorem cell22_2633516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_2633516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633516 prefixEnd_2633516 := by exact prefixLift 2633516
  have htrace : WordTrace (prefixWord ++ tailWord_2633516) baseStart_2633516 baseEnd_2633516 := by
    simpa [prefixWord, tailWord_2633516, baseEnd_2633516] using wordTrace_append hprefix tailTrace_2633516
  have hstable : (prefixWord ++ tailWord_2633516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633516).length < 2 ^ (prefixWord ++ tailWord_2633516).sum := by decide
  have hdescent : baseEnd_2633516 < baseStart_2633516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633544 : List Nat := [2, 1, 3, 1, 1, 5, 3, 6]
def baseStart_2633544 : Nat := 118140960795 + 2633544 * 2 ^ 59
def prefixEnd_2633544 : Nat := 4983230072969 + 3 ^ 40 * 2633544 * 2
def baseEnd_2633544 : Nat := 100168436797359220791745

theorem tailTrace_2633544 : CollatzResearch.WordTrace tailWord_2633544 prefixEnd_2633544 100168436797359220791745 := by
  unfold tailWord_2633544
  simp only [CollatzResearch.WordTrace]
  refine ⟨48026620385563668176005843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64035493847418224234674457 48026620385563668176005843)
  ·
    refine ⟨72039930578345502264008765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48026620385563668176005843 72039930578345502264008765)
    ·
      refine ⟨27014973966879563349003287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72039930578345502264008765 27014973966879563349003287)
      ·
        refine ⟨40522460950319345023504931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27014973966879563349003287 40522460950319345023504931)
        ·
          refine ⟨60783691425479017535257397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40522460950319345023504931 60783691425479017535257397)
          ·
            refine ⟨5698471071138657893930381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60783691425479017535257397 5698471071138657893930381)
            ·
              refine ⟨2136926651676996710223893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5698471071138657893930381 2136926651676996710223893)
              ·
                refine ⟨100168436797359220791745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2136926651676996710223893 100168436797359220791745)
                ·
                  rfl

theorem cell22_2633544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 6].length) (baseStart_2633544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633544 prefixEnd_2633544 := by exact prefixLift 2633544
  have htrace : WordTrace (prefixWord ++ tailWord_2633544) baseStart_2633544 baseEnd_2633544 := by
    simpa [prefixWord, tailWord_2633544, baseEnd_2633544] using wordTrace_append hprefix tailTrace_2633544
  have hstable : (prefixWord ++ tailWord_2633544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633544).length < 2 ^ (prefixWord ++ tailWord_2633544).sum := by decide
  have hdescent : baseEnd_2633544 < baseStart_2633544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633576 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 3, 3]
def baseStart_2633576 : Nat := 118140960795 + 2633576 * 2 ^ 59
def prefixEnd_2633576 : Nat := 4983230072969 + 3 ^ 40 * 2633576 * 2
def baseEnd_2633576 : Nat := 901526885430195570325607

theorem tailTrace_2633576 : CollatzResearch.WordTrace tailWord_2633576 prefixEnd_2633576 901526885430195570325607 := by
  unfold tailWord_2633576
  simp only [CollatzResearch.WordTrace]
  refine ⟨48027203953505702908588291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64036271938007603878117721 48027203953505702908588291)
  ·
    refine ⟨72040805930258554362882437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48027203953505702908588291 72040805930258554362882437)
    ·
      refine ⟨13507651111923478943040457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72040805930258554362882437 13507651111923478943040457)
      ·
        refine ⟨10130738333942609207280343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13507651111923478943040457 10130738333942609207280343)
        ·
          refine ⟨15196107500913913810920515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10130738333942609207280343 15196107500913913810920515)
          ·
            refine ⟨22794161251370870716380773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15196107500913913810920515 22794161251370870716380773)
            ·
              refine ⟨4273905234632038259321395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22794161251370870716380773 4273905234632038259321395)
              ·
                refine ⟨6410857851948057388982093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4273905234632038259321395 6410857851948057388982093)
                ·
                  refine ⟨2404071694480521520868285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6410857851948057388982093 2404071694480521520868285)
                  ·
                    refine ⟨901526885430195570325607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2404071694480521520868285 901526885430195570325607)
                    ·
                      rfl

theorem cell22_2633576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_2633576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633576 prefixEnd_2633576 := by exact prefixLift 2633576
  have htrace : WordTrace (prefixWord ++ tailWord_2633576) baseStart_2633576 baseEnd_2633576 := by
    simpa [prefixWord, tailWord_2633576, baseEnd_2633576] using wordTrace_append hprefix tailTrace_2633576
  have hstable : (prefixWord ++ tailWord_2633576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633576).length < 2 ^ (prefixWord ++ tailWord_2633576).sum := by decide
  have hdescent : baseEnd_2633576 < baseStart_2633576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633617 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 8]
def baseStart_2633617 : Nat := 118140960795 + 2633617 * 2 ^ 59
def prefixEnd_2633617 : Nat := 4983230072969 + 3 ^ 40 * 2633617 * 2
def baseEnd_2633617 : Nat := 300513640189361710016827

theorem tailTrace_2633617 : CollatzResearch.WordTrace tailWord_2633617 prefixEnd_2633617 300513640189361710016827 := by
  unfold tailWord_2633617
  simp only [CollatzResearch.WordTrace]
  refine ⟨96055903299862869819419105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64037268866575246546279403 96055903299862869819419105)
  ·
    refine ⟨72041927474897152364564329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96055903299862869819419105 72041927474897152364564329)
    ·
      refine ⟨54031445606172864273423247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72041927474897152364564329 54031445606172864273423247)
      ·
        refine ⟨81047168409259296410134871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54031445606172864273423247 81047168409259296410134871)
        ·
          refine ⟨121570752613888944615202307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81047168409259296410134871 121570752613888944615202307)
          ·
            refine ⟨182356128920833416922803461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121570752613888944615202307 182356128920833416922803461)
            ·
              refine ⟨34191774172656265673025649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182356128920833416922803461 34191774172656265673025649)
              ·
                refine ⟨25643830629492199254769237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34191774172656265673025649 25643830629492199254769237)
                ·
                  refine ⟨300513640189361710016827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25643830629492199254769237 300513640189361710016827)
                  ·
                    rfl

theorem cell22_2633617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 8].length) (baseStart_2633617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633617 prefixEnd_2633617 := by exact prefixLift 2633617
  have htrace : WordTrace (prefixWord ++ tailWord_2633617) baseStart_2633617 baseEnd_2633617 := by
    simpa [prefixWord, tailWord_2633617, baseEnd_2633617] using wordTrace_append hprefix tailTrace_2633617
  have hstable : (prefixWord ++ tailWord_2633617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633617).length < 2 ^ (prefixWord ++ tailWord_2633617).sum := by decide
  have hdescent : baseEnd_2633617 < baseStart_2633617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633653 : List Nat := [1, 3, 3, 2, 1, 4, 1, 2, 1, 4]
def baseStart_2633653 : Nat := 118140960795 + 2633653 * 2 ^ 59
def prefixEnd_2633653 : Nat := 4983230072969 + 3 ^ 40 * 2633653 * 2
def baseEnd_2633653 : Nat := 901553244103793036150371

theorem tailTrace_2633653 : CollatzResearch.WordTrace tailWord_2633653 prefixEnd_2633653 901553244103793036150371 := by
  unfold tailWord_2633653
  simp only [CollatzResearch.WordTrace]
  refine ⟨96057216327732447967729613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64038144218488298645153075 96057216327732447967729613)
  ·
    refine ⟨36021456122899667987898605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96057216327732447967729613 36021456122899667987898605)
    ·
      refine ⟨13508046046087375495461977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36021456122899667987898605 13508046046087375495461977)
      ·
        refine ⟨10131034534565531621596483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13508046046087375495461977 10131034534565531621596483)
        ·
          refine ⟨15196551801848297432394725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10131034534565531621596483 15196551801848297432394725)
          ·
            refine ⟨2849353462846555768574011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15196551801848297432394725 2849353462846555768574011)
            ·
              refine ⟨4274030194269833652861017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2849353462846555768574011 4274030194269833652861017)
              ·
                refine ⟨3205522645702375239645763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4274030194269833652861017 3205522645702375239645763)
                ·
                  refine ⟨4808283968553562859468645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3205522645702375239645763 4808283968553562859468645)
                  ·
                    refine ⟨901553244103793036150371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4808283968553562859468645 901553244103793036150371)
                    ·
                      rfl

theorem cell22_2633653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_2633653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633653 prefixEnd_2633653 := by exact prefixLift 2633653
  have htrace : WordTrace (prefixWord ++ tailWord_2633653) baseStart_2633653 baseEnd_2633653 := by
    simpa [prefixWord, tailWord_2633653, baseEnd_2633653] using wordTrace_append hprefix tailTrace_2633653
  have hstable : (prefixWord ++ tailWord_2633653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633653).length < 2 ^ (prefixWord ++ tailWord_2633653).sum := by decide
  have hdescent : baseEnd_2633653 < baseStart_2633653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633685 : List Nat := [1, 3, 2, 3, 2, 3, 2, 2, 4]
def baseStart_2633685 : Nat := 118140960795 + 2633685 * 2 ^ 59
def prefixEnd_2633685 : Nat := 4983230072969 + 3 ^ 40 * 2633685 * 2
def baseEnd_2633685 : Nat := 300521399452585206450091

theorem tailTrace_2633685 : CollatzResearch.WordTrace tailWord_2633685 prefixEnd_2633685 300521399452585206450091 := by
  unfold tailWord_2633685
  simp only [CollatzResearch.WordTrace]
  refine ⟨96058383463616517432894509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64038922309077678288596339 96058383463616517432894509)
  ·
    refine ⟨36021893798856194037335441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96058383463616517432894509 36021893798856194037335441)
    ·
      refine ⟨27016420349142145528001581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36021893798856194037335441 27016420349142145528001581)
      ·
        refine ⟨10131157630928304573000593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27016420349142145528001581 10131157630928304573000593)
        ·
          refine ⟨7598368223196228429750445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10131157630928304573000593 7598368223196228429750445)
          ·
            refine ⟨2849388083698585661156417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7598368223196228429750445 2849388083698585661156417)
            ·
              refine ⟨2137041062773939245867313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2849388083698585661156417 2137041062773939245867313)
              ·
                refine ⟨1602780797080454434400485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2137041062773939245867313 1602780797080454434400485)
                ·
                  refine ⟨300521399452585206450091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1602780797080454434400485 300521399452585206450091)
                  ·
                    rfl

theorem cell22_2633685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_2633685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633685 prefixEnd_2633685 := by exact prefixLift 2633685
  have htrace : WordTrace (prefixWord ++ tailWord_2633685) baseStart_2633685 baseEnd_2633685 := by
    simpa [prefixWord, tailWord_2633685, baseEnd_2633685] using wordTrace_append hprefix tailTrace_2633685
  have hstable : (prefixWord ++ tailWord_2633685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633685).length < 2 ^ (prefixWord ++ tailWord_2633685).sum := by decide
  have hdescent : baseEnd_2633685 < baseStart_2633685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633711 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 3, 3]
def baseStart_2633711 : Nat := 118140960795 + 2633711 * 2 ^ 59
def prefixEnd_2633711 : Nat := 4983230072969 + 3 ^ 40 * 2633711 * 2
def baseEnd_2633711 : Nat := 901573098689100218200193

theorem tailTrace_2633711 : CollatzResearch.WordTrace tailWord_2633711 prefixEnd_2633711 901573098689100218200193 := by
  unfold tailWord_2633711
  simp only [CollatzResearch.WordTrace]
  refine ⟨96059331761522323873340987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64039554507681549248893991 96059331761522323873340987)
  ·
    refine ⟨144088997642283485810011481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96059331761522323873340987 144088997642283485810011481)
    ·
      refine ⟨108066748231712614357508611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144088997642283485810011481 108066748231712614357508611)
      ·
        refine ⟨162100122347568921536262917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108066748231712614357508611 162100122347568921536262917)
        ·
          refine ⟨30393772940169172788049297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162100122347568921536262917 30393772940169172788049297)
          ·
            refine ⟨22795329705126879591036973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30393772940169172788049297 22795329705126879591036973)
            ·
              refine ⟨8548248639422579846638865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22795329705126879591036973 8548248639422579846638865)
              ·
                refine ⟨6411186479566934884979149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8548248639422579846638865 6411186479566934884979149)
                ·
                  refine ⟨2404194929837600581867181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6411186479566934884979149 2404194929837600581867181)
                  ·
                    refine ⟨901573098689100218200193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2404194929837600581867181 901573098689100218200193)
                    ·
                      rfl

theorem cell22_2633711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 3].length) (baseStart_2633711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633711 prefixEnd_2633711 := by exact prefixLift 2633711
  have htrace : WordTrace (prefixWord ++ tailWord_2633711) baseStart_2633711 baseEnd_2633711 := by
    simpa [prefixWord, tailWord_2633711, baseEnd_2633711] using wordTrace_append hprefix tailTrace_2633711
  have hstable : (prefixWord ++ tailWord_2633711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633711).length < 2 ^ (prefixWord ++ tailWord_2633711).sum := by decide
  have hdescent : baseEnd_2633711 < baseStart_2633711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633724 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 7]
def baseStart_2633724 : Nat := 118140960795 + 2633724 * 2 ^ 59
def prefixEnd_2633724 : Nat := 4983230072969 + 3 ^ 40 * 2633724 * 2
def baseEnd_2633724 : Nat := 300525849618257505875051

theorem tailTrace_2633724 : CollatzResearch.WordTrace tailWord_2633724 prefixEnd_2633724 300525849618257505875051 := by
  unfold tailWord_2633724
  simp only [CollatzResearch.WordTrace]
  refine ⟨48029902955237613546782113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64039870606983484729042817 48029902955237613546782113)
  ·
    refine ⟨36022427216428210160086585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48029902955237613546782113 36022427216428210160086585)
    ·
      refine ⟨27016820412321157620064939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36022427216428210160086585 27016820412321157620064939)
      ·
        refine ⟨40525230618481736430097409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27016820412321157620064939 40525230618481736430097409)
        ·
          refine ⟨30393922963861302322573057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40525230618481736430097409 30393922963861302322573057)
          ·
            refine ⟨22795442222895976741929793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30393922963861302322573057 22795442222895976741929793)
            ·
              refine ⟨17096581667171982556447345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22795442222895976741929793 17096581667171982556447345)
              ·
                refine ⟨12822436250378986917335509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17096581667171982556447345 12822436250378986917335509)
                ·
                  refine ⟨300525849618257505875051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12822436250378986917335509 300525849618257505875051)
                  ·
                    rfl

theorem cell22_2633724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_2633724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633724 prefixEnd_2633724 := by exact prefixLift 2633724
  have htrace : WordTrace (prefixWord ++ tailWord_2633724) baseStart_2633724 baseEnd_2633724 := by
    simpa [prefixWord, tailWord_2633724, baseEnd_2633724] using wordTrace_append hprefix tailTrace_2633724
  have hstable : (prefixWord ++ tailWord_2633724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633724).length < 2 ^ (prefixWord ++ tailWord_2633724).sum := by decide
  have hdescent : baseEnd_2633724 < baseStart_2633724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633734 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_2633734 : Nat := 118140960795 + 2633734 * 2 ^ 59
def prefixEnd_2633734 : Nat := 4983230072969 + 3 ^ 40 * 2633734 * 2
def baseEnd_2633734 : Nat := 901580972059135824875123

theorem tailTrace_2633734 : CollatzResearch.WordTrace tailWord_2633734 prefixEnd_2633734 901580972059135824875123 := by
  unfold tailWord_2633734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3001880332513718712544633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64040113760292665867618837 3001880332513718712544633)
  ·
    refine ⟨2251410249385289034408475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3001880332513718712544633 2251410249385289034408475)
    ·
      refine ⟨3377115374077933551612713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2251410249385289034408475 3377115374077933551612713)
      ·
        refine ⟨2532836530558450163709535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3377115374077933551612713 2532836530558450163709535)
        ·
          refine ⟨3799254795837675245564303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2532836530558450163709535 3799254795837675245564303)
          ·
            refine ⟨5698882193756512868346455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3799254795837675245564303 5698882193756512868346455)
            ·
              refine ⟨8548323290634769302519683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5698882193756512868346455 8548323290634769302519683)
              ·
                refine ⟨12822484935952153953779525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8548323290634769302519683 12822484935952153953779525)
                ·
                  refine ⟨2404215925491028866333661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12822484935952153953779525 2404215925491028866333661)
                  ·
                    refine ⟨901580972059135824875123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2404215925491028866333661 901580972059135824875123)
                    ·
                      rfl

theorem cell22_2633734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_2633734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633734 prefixEnd_2633734 := by exact prefixLift 2633734
  have htrace : WordTrace (prefixWord ++ tailWord_2633734) baseStart_2633734 baseEnd_2633734 := by
    simpa [prefixWord, tailWord_2633734, baseEnd_2633734] using wordTrace_append hprefix tailTrace_2633734
  have hstable : (prefixWord ++ tailWord_2633734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633734).length < 2 ^ (prefixWord ++ tailWord_2633734).sum := by decide
  have hdescent : baseEnd_2633734 < baseStart_2633734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633739 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 4, 5]
def baseStart_2633739 : Nat := 118140960795 + 2633739 * 2 ^ 59
def prefixEnd_2633739 : Nat := 4983230072969 + 3 ^ 40 * 2633739 * 2
def baseEnd_2633739 : Nat := 901582683661317478500107

theorem tailTrace_2633739 : CollatzResearch.WordTrace tailWord_2633739 prefixEnd_2633739 901582683661317478500107 := by
  unfold tailWord_2633739
  simp only [CollatzResearch.WordTrace]
  refine ⟨96060353005420884655360271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64040235336947256436906847 96060353005420884655360271)
  ·
    refine ⟨144090529508131326983040407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96060353005420884655360271 144090529508131326983040407)
    ·
      refine ⟨216135794262196990474560611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144090529508131326983040407 216135794262196990474560611)
      ·
        refine ⟨324203691393295485711840917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216135794262196990474560611 324203691393295485711840917)
        ·
          refine ⟨15197048034060725892742543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 324203691393295485711840917 15197048034060725892742543)
          ·
            refine ⟨22795572051091088839113815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15197048034060725892742543 22795572051091088839113815)
            ·
              refine ⟨34193358076636633258670723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22795572051091088839113815 34193358076636633258670723)
              ·
                refine ⟨51290037114954949888006085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34193358076636633258670723 51290037114954949888006085)
                ·
                  refine ⟨9616881959054053104001141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51290037114954949888006085 9616881959054053104001141)
                  ·
                    refine ⟨901582683661317478500107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9616881959054053104001141 901582683661317478500107)
                    ·
                      rfl

theorem cell22_2633739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 5].length) (baseStart_2633739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633739 prefixEnd_2633739 := by exact prefixLift 2633739
  have htrace : WordTrace (prefixWord ++ tailWord_2633739) baseStart_2633739 baseEnd_2633739 := by
    simpa [prefixWord, tailWord_2633739, baseEnd_2633739] using wordTrace_append hprefix tailTrace_2633739
  have hstable : (prefixWord ++ tailWord_2633739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633739).length < 2 ^ (prefixWord ++ tailWord_2633739).sum := by decide
  have hdescent : baseEnd_2633739 < baseStart_2633739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633756 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 2, 5]
def baseStart_2633756 : Nat := 118140960795 + 2633756 * 2 ^ 59
def prefixEnd_2633756 : Nat := 4983230072969 + 3 ^ 40 * 2633756 * 2
def baseEnd_2633756 : Nat := 901588503108735100825055

theorem tailTrace_2633756 : CollatzResearch.WordTrace tailWord_2633756 prefixEnd_2633756 901588503108735100825055 := by
  unfold tailWord_2633756
  simp only [CollatzResearch.WordTrace]
  refine ⟨48030486523179648279364561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64040648697572864372486081 48030486523179648279364561)
  ·
    refine ⟨36022864892384736209523421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48030486523179648279364561 36022864892384736209523421)
    ·
      refine ⟨13508574334644276078571283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36022864892384736209523421 13508574334644276078571283)
      ·
        refine ⟨20262861501966414117856925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13508574334644276078571283 20262861501966414117856925)
        ·
          refine ⟨7598573063237405294196347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20262861501966414117856925 7598573063237405294196347)
          ·
            refine ⟨11397859594856107941294521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7598573063237405294196347 11397859594856107941294521)
            ·
              refine ⟨8548394696142080955970891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11397859594856107941294521 8548394696142080955970891)
              ·
                refine ⟨12822592044213121433956337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8548394696142080955970891 12822592044213121433956337)
                ·
                  refine ⟨9616944033159841075467253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12822592044213121433956337 9616944033159841075467253)
                  ·
                    refine ⟨901588503108735100825055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9616944033159841075467253 901588503108735100825055)
                    ·
                      rfl

theorem cell22_2633756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_2633756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633756 prefixEnd_2633756 := by exact prefixLift 2633756
  have htrace : WordTrace (prefixWord ++ tailWord_2633756) baseStart_2633756 baseEnd_2633756 := by
    simpa [prefixWord, tailWord_2633756, baseEnd_2633756] using wordTrace_append hprefix tailTrace_2633756
  have hstable : (prefixWord ++ tailWord_2633756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633756).length < 2 ^ (prefixWord ++ tailWord_2633756).sum := by decide
  have hdescent : baseEnd_2633756 < baseStart_2633756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633801 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 4, 3]
def baseStart_2633801 : Nat := 118140960795 + 2633801 * 2 ^ 59
def prefixEnd_2633801 : Nat := 4983230072969 + 3 ^ 40 * 2633801 * 2
def baseEnd_2633801 : Nat := 901603907528369983449917

theorem tailTrace_2633801 : CollatzResearch.WordTrace tailWord_2633801 prefixEnd_2633801 901603907528369983449917 := by
  unfold tailWord_2633801
  simp only [CollatzResearch.WordTrace]
  refine ⟨96062614331196269244117257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64041742887464179496078171 96062614331196269244117257)
  ·
    refine ⟨72046960748397201933087943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96062614331196269244117257 72046960748397201933087943)
    ·
      refine ⟨108070441122595802899631915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72046960748397201933087943 108070441122595802899631915)
      ·
        refine ⟨162105661683893704349447873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108070441122595802899631915 162105661683893704349447873)
        ·
          refine ⟨121579246262920278262085905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162105661683893704349447873 121579246262920278262085905)
          ·
            refine ⟨91184434697190208696564429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121579246262920278262085905 91184434697190208696564429)
            ·
              refine ⟨34194163011446328261211661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91184434697190208696564429 34194163011446328261211661)
              ·
                refine ⟨12822811129292373097954373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34194163011446328261211661 12822811129292373097954373)
                ·
                  refine ⟨2404277086742319955866445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12822811129292373097954373 2404277086742319955866445)
                  ·
                    refine ⟨901603907528369983449917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2404277086742319955866445 901603907528369983449917)
                    ·
                      rfl

theorem cell22_2633801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 3].length) (baseStart_2633801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633801 prefixEnd_2633801 := by exact prefixLift 2633801
  have htrace : WordTrace (prefixWord ++ tailWord_2633801) baseStart_2633801 baseEnd_2633801 := by
    simpa [prefixWord, tailWord_2633801, baseEnd_2633801] using wordTrace_append hprefix tailTrace_2633801
  have hstable : (prefixWord ++ tailWord_2633801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633801).length < 2 ^ (prefixWord ++ tailWord_2633801).sum := by decide
  have hdescent : baseEnd_2633801 < baseStart_2633801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633818 : List Nat := [3, 1, 1, 2, 1, 1, 5, 3, 2, 3]
def baseStart_2633818 : Nat := 118140960795 + 2633818 * 2 ^ 59
def prefixEnd_2633818 : Nat := 4983230072969 + 3 ^ 40 * 2633818 * 2
def baseEnd_2633818 : Nat := 901609726975787605774865

theorem tailTrace_2633818 : CollatzResearch.WordTrace tailWord_2633818 prefixEnd_2633818 901609726975787605774865 := by
  unfold tailWord_2633818
  simp only [CollatzResearch.WordTrace]
  refine ⟨24015808593033670286871527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64042156248089787431657405 24015808593033670286871527)
  ·
    refine ⟨36023712889550505430307291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24015808593033670286871527 36023712889550505430307291)
    ·
      refine ⟨54035569334325758145460937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36023712889550505430307291 54035569334325758145460937)
      ·
        refine ⟨40526677000744318609095703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54035569334325758145460937 40526677000744318609095703)
        ·
          refine ⟨60790015501116477913643555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40526677000744318609095703 60790015501116477913643555)
          ·
            refine ⟨91185023251674716870465333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60790015501116477913643555 91185023251674716870465333)
            ·
              refine ⟨8548595929844504706606125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91185023251674716870465333 8548595929844504706606125)
              ·
                refine ⟨3205723473691689264977297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8548595929844504706606125 3205723473691689264977297)
                ·
                  refine ⟨2404292605268766948732973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3205723473691689264977297 2404292605268766948732973)
                  ·
                    refine ⟨901609726975787605774865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2404292605268766948732973 901609726975787605774865)
                    ·
                      rfl

theorem cell22_2633818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_2633818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633818 prefixEnd_2633818 := by exact prefixLift 2633818
  have htrace : WordTrace (prefixWord ++ tailWord_2633818) baseStart_2633818 baseEnd_2633818 := by
    simpa [prefixWord, tailWord_2633818, baseEnd_2633818] using wordTrace_append hprefix tailTrace_2633818
  have hstable : (prefixWord ++ tailWord_2633818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633818).length < 2 ^ (prefixWord ++ tailWord_2633818).sum := by decide
  have hdescent : baseEnd_2633818 < baseStart_2633818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633822 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2633822 : Nat := 118140960795 + 2633822 * 2 ^ 59
def prefixEnd_2633822 : Nat := 4983230072969 + 3 ^ 40 * 2633822 * 2
def baseEnd_2633822 : Nat := 901611096257532928674853

theorem tailTrace_2633822 : CollatzResearch.WordTrace tailWord_2633822 prefixEnd_2633822 901611096257532928674853 := by
  unfold tailWord_2633822
  simp only [CollatzResearch.WordTrace]
  refine ⟨12007922533015023728828965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64042253509413459887087813 12007922533015023728828965)
  ·
    refine ⟨2251485474940316949155431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12007922533015023728828965 2251485474940316949155431)
    ·
      refine ⟨3377228212410475423733147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2251485474940316949155431 3377228212410475423733147)
      ·
        refine ⟨5065842318615713135599721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3377228212410475423733147 5065842318615713135599721)
        ·
          refine ⟨3799381738961784851699791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5065842318615713135599721 3799381738961784851699791)
          ·
            refine ⟨5699072608442677277549687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3799381738961784851699791 5699072608442677277549687)
            ·
              refine ⟨8548608912664015916324531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5699072608442677277549687 8548608912664015916324531)
              ·
                refine ⟨12822913368996023874486797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8548608912664015916324531 12822913368996023874486797)
                ·
                  refine ⟨4808592513373508952932549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12822913368996023874486797 4808592513373508952932549)
                  ·
                    refine ⟨901611096257532928674853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4808592513373508952932549 901611096257532928674853)
                    ·
                      rfl

theorem cell22_2633822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2633822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633822 prefixEnd_2633822 := by exact prefixLift 2633822
  have htrace : WordTrace (prefixWord ++ tailWord_2633822) baseStart_2633822 baseEnd_2633822 := by
    simpa [prefixWord, tailWord_2633822, baseEnd_2633822] using wordTrace_append hprefix tailTrace_2633822
  have hstable : (prefixWord ++ tailWord_2633822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633822).length < 2 ^ (prefixWord ++ tailWord_2633822).sum := by decide
  have hdescent : baseEnd_2633822 < baseStart_2633822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633861 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 2, 6]
def baseStart_2633861 : Nat := 118140960795 + 2633861 * 2 ^ 59
def prefixEnd_2633861 : Nat := 4983230072969 + 3 ^ 40 * 2633861 * 2
def baseEnd_2633861 : Nat := 901624446754549826949733

theorem tailTrace_2633861 : CollatzResearch.WordTrace tailWord_2633861 prefixEnd_2633861 901624446754549826949733 := by
  unfold tailWord_2633861
  simp only [CollatzResearch.WordTrace]
  refine ⟨96064802710978899491301437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64043201807319266327534291 96064802710978899491301437)
  ·
    refine ⟨36024301016617087309238039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96064802710978899491301437 36024301016617087309238039)
    ·
      refine ⟨54036451524925630963857059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36024301016617087309238039 54036451524925630963857059)
      ·
        refine ⟨81054677287388446445785589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54036451524925630963857059 81054677287388446445785589)
        ·
          refine ⟨7598875995692666854292399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81054677287388446445785589 7598875995692666854292399)
          ·
            refine ⟨11398313993539000281438599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7598875995692666854292399 11398313993539000281438599)
            ·
              refine ⟨17097470990308500422157899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11398313993539000281438599 17097470990308500422157899)
              ·
                refine ⟨25646206485462750633236849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17097470990308500422157899 25646206485462750633236849)
                ·
                  refine ⟨19234654864097062974927637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25646206485462750633236849 19234654864097062974927637)
                  ·
                    refine ⟨901624446754549826949733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19234654864097062974927637 901624446754549826949733)
                    ·
                      rfl

theorem cell22_2633861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_2633861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633861 prefixEnd_2633861 := by exact prefixLift 2633861
  have htrace : WordTrace (prefixWord ++ tailWord_2633861) baseStart_2633861 baseEnd_2633861 := by
    simpa [prefixWord, tailWord_2633861, baseEnd_2633861] using wordTrace_append hprefix tailTrace_2633861
  have hstable : (prefixWord ++ tailWord_2633861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633861).length < 2 ^ (prefixWord ++ tailWord_2633861).sum := by decide
  have hdescent : baseEnd_2633861 < baseStart_2633861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633880 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 3, 3]
def baseStart_2633880 : Nat := 118140960795 + 2633880 * 2 ^ 59
def prefixEnd_2633880 : Nat := 4983230072969 + 3 ^ 40 * 2633880 * 2
def baseEnd_2633880 : Nat := 901630950842840110724675

theorem tailTrace_2633880 : CollatzResearch.WordTrace tailWord_2633880 prefixEnd_2633880 901630950842840110724675 := by
  unfold tailWord_2633880
  simp only [CollatzResearch.WordTrace]
  refine ⟨48032747848955032868121547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64043663798606710490828729 48032747848955032868121547)
  ·
    refine ⟨72049121773432549302182321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48032747848955032868121547 72049121773432549302182321)
    ·
      refine ⟨54036841330074411976636741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72049121773432549302182321 54036841330074411976636741)
      ·
        refine ⟨10131907749388952245619389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54036841330074411976636741 10131907749388952245619389)
        ·
          refine ⟨3799465406020857092107271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10131907749388952245619389 3799465406020857092107271)
          ·
            refine ⟨5699198109031285638160907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3799465406020857092107271 5699198109031285638160907)
            ·
              refine ⟨8548797163546928457241361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5699198109031285638160907 8548797163546928457241361)
              ·
                refine ⟨6411597872660196342931021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8548797163546928457241361 6411597872660196342931021)
                ·
                  refine ⟨2404349202247573628599133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6411597872660196342931021 2404349202247573628599133)
                  ·
                    refine ⟨901630950842840110724675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2404349202247573628599133 901630950842840110724675)
                    ·
                      rfl

theorem cell22_2633880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_2633880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633880 prefixEnd_2633880 := by exact prefixLift 2633880
  have htrace : WordTrace (prefixWord ++ tailWord_2633880) baseStart_2633880 baseEnd_2633880 := by
    simpa [prefixWord, tailWord_2633880, baseEnd_2633880] using wordTrace_append hprefix tailTrace_2633880
  have hstable : (prefixWord ++ tailWord_2633880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633880).length < 2 ^ (prefixWord ++ tailWord_2633880).sum := by decide
  have hdescent : baseEnd_2633880 < baseStart_2633880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633938 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 6]
def baseStart_2633938 : Nat := 118140960795 + 2633938 * 2 ^ 59
def prefixEnd_2633938 : Nat := 4983230072969 + 3 ^ 40 * 2633938 * 2
def baseEnd_2633938 : Nat := 300550268476049097591499

theorem tailTrace_2633938 : CollatzResearch.WordTrace tailWord_2633938 prefixEnd_2633938 300550268476049097591499 := by
  unfold tailWord_2633938
  simp only [CollatzResearch.WordTrace]
  refine ⟨24016902782924985410463617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64045074087799961094569645 24016902782924985410463617)
  ·
    refine ⟨18012677087193739057847713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24016902782924985410463617 18012677087193739057847713)
    ·
      refine ⟨13509507815395304293385785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18012677087193739057847713 13509507815395304293385785)
      ·
        refine ⟨10132130861546478220039339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13509507815395304293385785 10132130861546478220039339)
        ·
          refine ⟨15198196292319717330059009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10132130861546478220039339 15198196292319717330059009)
          ·
            refine ⟨11398647219239787997544257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15198196292319717330059009 11398647219239787997544257)
            ·
              refine ⟨8548985414429840998158193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11398647219239787997544257 8548985414429840998158193)
              ·
                refine ⟨6411739060822380748618645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8548985414429840998158193 6411739060822380748618645)
                ·
                  refine ⟨300550268476049097591499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6411739060822380748618645 300550268476049097591499)
                  ·
                    rfl

theorem cell22_2633938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_2633938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633938 prefixEnd_2633938 := by exact prefixLift 2633938
  have htrace : WordTrace (prefixWord ++ tailWord_2633938) baseStart_2633938 baseEnd_2633938 := by
    simpa [prefixWord, tailWord_2633938, baseEnd_2633938] using wordTrace_append hprefix tailTrace_2633938
  have hstable : (prefixWord ++ tailWord_2633938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633938).length < 2 ^ (prefixWord ++ tailWord_2633938).sum := by decide
  have hdescent : baseEnd_2633938 < baseStart_2633938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633948 : List Nat := [2, 2, 5, 2, 2, 1, 1, 3, 1, 3]
def baseStart_2633948 : Nat := 118140960795 + 2633948 * 2 ^ 59
def prefixEnd_2633948 : Nat := 4983230072969 + 3 ^ 40 * 2633948 * 2
def baseEnd_2633948 : Nat := 901654228632510600024467

theorem tailTrace_2633948 : CollatzResearch.WordTrace tailWord_2633948 prefixEnd_2633948 901654228632510600024467 := by
  unfold tailWord_2633948
  simp only [CollatzResearch.WordTrace]
  refine ⟨48033987930831856674859249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64045317241109142233145665 48033987930831856674859249)
  ·
    refine ⟨36025490948123892506144437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48033987930831856674859249 36025490948123892506144437)
    ·
      refine ⟨3377389776386614922451041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36025490948123892506144437 3377389776386614922451041)
      ·
        refine ⟨2533042332289961191838281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3377389776386614922451041 2533042332289961191838281)
        ·
          refine ⟨1899781749217470893878711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2533042332289961191838281 1899781749217470893878711)
          ·
            refine ⟨2849672623826206340818067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899781749217470893878711 2849672623826206340818067)
            ·
              refine ⟨4274508935739309511227101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2849672623826206340818067 4274508935739309511227101)
              ·
                refine ⟨1602940850902241066710163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4274508935739309511227101 1602940850902241066710163)
                ·
                  refine ⟨2404411276353361600065245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1602940850902241066710163 2404411276353361600065245)
                  ·
                    refine ⟨901654228632510600024467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2404411276353361600065245 901654228632510600024467)
                    ·
                      rfl

theorem cell22_2633948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_2633948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633948 prefixEnd_2633948 := by exact prefixLift 2633948
  have htrace : WordTrace (prefixWord ++ tailWord_2633948) baseStart_2633948 baseEnd_2633948 := by
    simpa [prefixWord, tailWord_2633948, baseEnd_2633948] using wordTrace_append hprefix tailTrace_2633948
  have hstable : (prefixWord ++ tailWord_2633948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633948).length < 2 ^ (prefixWord ++ tailWord_2633948).sum := by decide
  have hdescent : baseEnd_2633948 < baseStart_2633948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633953 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 6, 3]
def baseStart_2633953 : Nat := 118140960795 + 2633953 * 2 ^ 59
def prefixEnd_2633953 : Nat := 4983230072969 + 3 ^ 40 * 2633953 * 2
def baseEnd_2633953 : Nat := 901655940234692253649451

theorem tailTrace_2633953 : CollatzResearch.WordTrace tailWord_2633953 prefixEnd_2633953 901655940234692253649451 := by
  unfold tailWord_2633953
  simp only [CollatzResearch.WordTrace]
  refine ⟨96068158226645599203650513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64045438817763732802433675 96068158226645599203650513)
  ·
    refine ⟨72051118669984199402737885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96068158226645599203650513 72051118669984199402737885)
    ·
      refine ⟨27019169501244074776026707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72051118669984199402737885 27019169501244074776026707)
      ·
        refine ⟨40528754251866112164040061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27019169501244074776026707 40528754251866112164040061)
        ·
          refine ⟨15198282844449792061515023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40528754251866112164040061 15198282844449792061515023)
          ·
            refine ⟨22797424266674688092272535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15198282844449792061515023 22797424266674688092272535)
            ·
              refine ⟨34196136400012032138408803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22797424266674688092272535 34196136400012032138408803)
              ·
                refine ⟨51294204600018048207613205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34196136400012032138408803 51294204600018048207613205)
                ·
                  refine ⟨2404415840625846009731869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51294204600018048207613205 2404415840625846009731869)
                  ·
                    refine ⟨901655940234692253649451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2404415840625846009731869 901655940234692253649451)
                    ·
                      rfl

theorem cell22_2633953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_2633953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633953 prefixEnd_2633953 := by exact prefixLift 2633953
  have htrace : WordTrace (prefixWord ++ tailWord_2633953) baseStart_2633953 baseEnd_2633953 := by
    simpa [prefixWord, tailWord_2633953, baseEnd_2633953] using wordTrace_append hprefix tailTrace_2633953
  have hstable : (prefixWord ++ tailWord_2633953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633953).length < 2 ^ (prefixWord ++ tailWord_2633953).sum := by decide
  have hdescent : baseEnd_2633953 < baseStart_2633953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633970 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 4, 3]
def baseStart_2633970 : Nat := 118140960795 + 2633970 * 2 ^ 59
def prefixEnd_2633970 : Nat := 4983230072969 + 3 ^ 40 * 2633970 * 2
def baseEnd_2633970 : Nat := 901661759682109875974399

theorem tailTrace_2633970 : CollatzResearch.WordTrace tailWord_2633970 prefixEnd_2633970 901661759682109875974399 := by
  unfold tailWord_2633970
  simp only [CollatzResearch.WordTrace]
  refine ⟨24017194566896002776754841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64045852178389340738012909 24017194566896002776754841)
  ·
    refine ⟨18012895925172002082566131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24017194566896002776754841 18012895925172002082566131)
    ·
      refine ⟨27019343887758003123849197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18012895925172002082566131 27019343887758003123849197)
      ·
        refine ⟨10132253957909251171443449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27019343887758003123849197 10132253957909251171443449)
        ·
          refine ⟨7599190468431938378582587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10132253957909251171443449 7599190468431938378582587)
          ·
            refine ⟨11398785702647907567873881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7599190468431938378582587 11398785702647907567873881)
            ·
              refine ⟨8549089276985930675905411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11398785702647907567873881 8549089276985930675905411)
              ·
                refine ⟨12823633915478896013858117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8549089276985930675905411 12823633915478896013858117)
                ·
                  refine ⟨2404431359152293002598397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12823633915478896013858117 2404431359152293002598397)
                  ·
                    refine ⟨901661759682109875974399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2404431359152293002598397 901661759682109875974399)
                    ·
                      rfl

theorem cell22_2633970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_2633970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2633970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2633970 prefixEnd_2633970 := by exact prefixLift 2633970
  have htrace : WordTrace (prefixWord ++ tailWord_2633970) baseStart_2633970 baseEnd_2633970 := by
    simpa [prefixWord, tailWord_2633970, baseEnd_2633970] using wordTrace_append hprefix tailTrace_2633970
  have hstable : (prefixWord ++ tailWord_2633970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633970).length < 2 ^ (prefixWord ++ tailWord_2633970).sum := by decide
  have hdescent : baseEnd_2633970 < baseStart_2633970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634011 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 9]
def baseStart_2634011 : Nat := 118140960795 + 2634011 * 2 ^ 59
def prefixEnd_2634011 : Nat := 4983230072969 + 3 ^ 40 * 2634011 * 2
def baseEnd_2634011 : Nat := 300558598273333145233091

theorem tailTrace_2634011 : CollatzResearch.WordTrace tailWord_2634011 prefixEnd_2634011 300558598273333145233091 := by
  unfold tailWord_2634011
  simp only [CollatzResearch.WordTrace]
  refine ⟨96070273660435475109261887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64046849106956983406174591 96070273660435475109261887)
  ·
    refine ⟨144105410490653212663892831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96070273660435475109261887 144105410490653212663892831)
    ·
      refine ⟨216158115735979818995839247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144105410490653212663892831 216158115735979818995839247)
      ·
        refine ⟨324237173603969728493758871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216158115735979818995839247 324237173603969728493758871)
        ·
          refine ⟨486355760405954592740638307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324237173603969728493758871 486355760405954592740638307)
          ·
            refine ⟨729533640608931889110957461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486355760405954592740638307 729533640608931889110957461)
            ·
              refine ⟨34196889403543682302076131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 729533640608931889110957461 34196889403543682302076131)
              ·
                refine ⟨51295334105315523453114197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34196889403543682302076131 51295334105315523453114197)
                ·
                  refine ⟨300558598273333145233091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51295334105315523453114197 300558598273333145233091)
                  ·
                    rfl

theorem cell22_2634011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 9].length) (baseStart_2634011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634011 prefixEnd_2634011 := by exact prefixLift 2634011
  have htrace : WordTrace (prefixWord ++ tailWord_2634011) baseStart_2634011 baseEnd_2634011 := by
    simpa [prefixWord, tailWord_2634011, baseEnd_2634011] using wordTrace_append hprefix tailTrace_2634011
  have hstable : (prefixWord ++ tailWord_2634011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634011).length < 2 ^ (prefixWord ++ tailWord_2634011).sum := by decide
  have hdescent : baseEnd_2634011 < baseStart_2634011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634023 : List Nat := [1, 1, 8, 1, 1, 2, 2, 2, 4]
def baseStart_2634023 : Nat := 118140960795 + 2634023 * 2 ^ 59
def prefixEnd_2634023 : Nat := 4983230072969 + 3 ^ 40 * 2634023 * 2
def baseEnd_2634023 : Nat := 300559967555078468133079

theorem tailTrace_2634023 : CollatzResearch.WordTrace tailWord_2634023 prefixEnd_2634023 300559967555078468133079 := by
  unfold tailWord_2634023
  simp only [CollatzResearch.WordTrace]
  refine ⟨96070711336392001158698723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64047140890928000772465815 96070711336392001158698723)
  ·
    refine ⟨144106067004588001738048085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96070711336392001158698723 144106067004588001738048085)
    ·
      refine ⟨1688742972710015645367751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 144106067004588001738048085 1688742972710015645367751)
      ·
        refine ⟨2533114459065023468051627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1688742972710015645367751 2533114459065023468051627)
        ·
          refine ⟨3799671688597535202077441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533114459065023468051627 3799671688597535202077441)
          ·
            refine ⟨2849753766448151401558081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3799671688597535202077441 2849753766448151401558081)
            ·
              refine ⟨2137315324836113551168561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2849753766448151401558081 2137315324836113551168561)
              ·
                refine ⟨1602986493627085163376421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2137315324836113551168561 1602986493627085163376421)
                ·
                  refine ⟨300559967555078468133079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1602986493627085163376421 300559967555078468133079)
                  ·
                    rfl

theorem cell22_2634023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 4].length) (baseStart_2634023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634023 prefixEnd_2634023 := by exact prefixLift 2634023
  have htrace : WordTrace (prefixWord ++ tailWord_2634023) baseStart_2634023 baseEnd_2634023 := by
    simpa [prefixWord, tailWord_2634023, baseEnd_2634023] using wordTrace_append hprefix tailTrace_2634023
  have hstable : (prefixWord ++ tailWord_2634023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634023).length < 2 ^ (prefixWord ++ tailWord_2634023).sum := by decide
  have hdescent : baseEnd_2634023 < baseStart_2634023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634028 : List Nat := [2, 2, 1, 1, 1, 3, 3, 4, 5]
def baseStart_2634028 : Nat := 118140960795 + 2634028 * 2 ^ 59
def prefixEnd_2634028 : Nat := 4983230072969 + 3 ^ 40 * 2634028 * 2
def baseEnd_2634028 : Nat := 300560538089139019341407

theorem tailTrace_2634028 : CollatzResearch.WordTrace tailWord_2634028 prefixEnd_2634028 300560538089139019341407 := by
  unfold tailWord_2634028
  simp only [CollatzResearch.WordTrace]
  refine ⟨48035446850686943506315369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64047262467582591341753825 48035446850686943506315369)
  ·
    refine ⟨36026585138015207629736527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48035446850686943506315369 36026585138015207629736527)
    ·
      refine ⟨54039877707022811444604791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36026585138015207629736527 54039877707022811444604791)
      ·
        refine ⟨81059816560534217166907187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54039877707022811444604791 81059816560534217166907187)
        ·
          refine ⟨121589724840801325750360781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81059816560534217166907187 121589724840801325750360781)
          ·
            refine ⟨45596146815300497156385293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121589724840801325750360781 45596146815300497156385293)
            ·
              refine ⟨17098555055737686433644485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45596146815300497156385293 17098555055737686433644485)
              ·
                refine ⟨3205979072950816206308341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17098555055737686433644485 3205979072950816206308341)
                ·
                  refine ⟨300560538089139019341407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3205979072950816206308341 300560538089139019341407)
                  ·
                    rfl

theorem cell22_2634028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_2634028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634028 prefixEnd_2634028 := by exact prefixLift 2634028
  have htrace : WordTrace (prefixWord ++ tailWord_2634028) baseStart_2634028 baseEnd_2634028 := by
    simpa [prefixWord, tailWord_2634028, baseEnd_2634028] using wordTrace_append hprefix tailTrace_2634028
  have hstable : (prefixWord ++ tailWord_2634028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634028).length < 2 ^ (prefixWord ++ tailWord_2634028).sum := by decide
  have hdescent : baseEnd_2634028 < baseStart_2634028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634090 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 6]
def baseStart_2634090 : Nat := 118140960795 + 2634090 * 2 ^ 59
def prefixEnd_2634090 : Nat := 4983230072969 + 3 ^ 40 * 2634090 * 2
def baseEnd_2634090 : Nat := 300567612711489854324677

theorem tailTrace_2634090 : CollatzResearch.WordTrace tailWord_2634090 prefixEnd_2634090 300567612711489854324677 := by
  unfold tailWord_2634090
  simp only [CollatzResearch.WordTrace]
  refine ⟨24018288756787317900346931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64048770018099514400925149 24018288756787317900346931)
  ·
    refine ⟨36027433135180976850520397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24018288756787317900346931 36027433135180976850520397)
    ·
      refine ⟨13510287425692866318945149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36027433135180976850520397 13510287425692866318945149)
      ·
        refine ⟨5066357784634824869604431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13510287425692866318945149 5066357784634824869604431)
        ·
          refine ⟨7599536676952237304406647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5066357784634824869604431 7599536676952237304406647)
          ·
            refine ⟨11399305015428355956609971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7599536676952237304406647 11399305015428355956609971)
            ·
              refine ⟨17098957523142533934914957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11399305015428355956609971 17098957523142533934914957)
              ·
                refine ⟨6412109071178450225593109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17098957523142533934914957 6412109071178450225593109)
                ·
                  refine ⟨300567612711489854324677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6412109071178450225593109 300567612711489854324677)
                  ·
                    rfl

theorem cell22_2634090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_2634090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634090 prefixEnd_2634090 := by exact prefixLift 2634090
  have htrace : WordTrace (prefixWord ++ tailWord_2634090) baseStart_2634090 baseEnd_2634090 := by
    simpa [prefixWord, tailWord_2634090, baseEnd_2634090] using wordTrace_append hprefix tailTrace_2634090
  have hstable : (prefixWord ++ tailWord_2634090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634090).length < 2 ^ (prefixWord ++ tailWord_2634090).sum := by decide
  have hdescent : baseEnd_2634090 < baseStart_2634090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634103 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 6, 4]
def baseStart_2634103 : Nat := 118140960795 + 2634103 * 2 ^ 59
def prefixEnd_2634103 : Nat := 4983230072969 + 3 ^ 40 * 2634103 * 2
def baseEnd_2634103 : Nat := 901707288300141862398991

theorem tailTrace_2634103 : CollatzResearch.WordTrace tailWord_2634103 prefixEnd_2634103 901707288300141862398991 := by
  unfold tailWord_2634103
  simp only [CollatzResearch.WordTrace]
  refine ⟨96073629176102174821610963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64049086117401449881073975 96073629176102174821610963)
  ·
    refine ⟨144110443764153262232416445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96073629176102174821610963 144110443764153262232416445)
    ·
      refine ⟨54041416411557473337156167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144110443764153262232416445 54041416411557473337156167)
      ·
        refine ⟨81062124617336210005734251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54041416411557473337156167 81062124617336210005734251)
        ·
          refine ⟨121593186926004315008601377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81062124617336210005734251 121593186926004315008601377)
          ·
            refine ⟨91194890194503236256451033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121593186926004315008601377 91194890194503236256451033)
            ·
              refine ⟨68396167645877427192338275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91194890194503236256451033 68396167645877427192338275)
              ·
                refine ⟨102594251468816140788507413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68396167645877427192338275 102594251468816140788507413)
                ·
                  refine ⟨4809105537600756599461285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102594251468816140788507413 4809105537600756599461285)
                  ·
                    refine ⟨901707288300141862398991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4809105537600756599461285 901707288300141862398991)
                    ·
                      rfl

theorem cell22_2634103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_2634103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634103 prefixEnd_2634103 := by exact prefixLift 2634103
  have htrace : WordTrace (prefixWord ++ tailWord_2634103) baseStart_2634103 baseEnd_2634103 := by
    simpa [prefixWord, tailWord_2634103, baseEnd_2634103] using wordTrace_append hprefix tailTrace_2634103
  have hstable : (prefixWord ++ tailWord_2634103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634103).length < 2 ^ (prefixWord ++ tailWord_2634103).sum := by decide
  have hdescent : baseEnd_2634103 < baseStart_2634103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634120 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 2, 4]
def baseStart_2634120 : Nat := 118140960795 + 2634120 * 2 ^ 59
def prefixEnd_2634120 : Nat := 4983230072969 + 3 ^ 40 * 2634120 * 2
def baseEnd_2634120 : Nat := 901713107747559484723939

theorem tailTrace_2634120 : CollatzResearch.WordTrace tailWord_2634120 prefixEnd_2634120 901713107747559484723939 := by
  unfold tailWord_2634120
  simp only [CollatzResearch.WordTrace]
  refine ⟨48037124608520293362489907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64049499478027057816653209 48037124608520293362489907)
  ·
    refine ⟨72055686912780440043734861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48037124608520293362489907 72055686912780440043734861)
    ·
      refine ⟨27020882592292665016400573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72055686912780440043734861 27020882592292665016400573)
      ·
        refine ⟨10132830972109749381150215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27020882592292665016400573 10132830972109749381150215)
        ·
          refine ⟨15199246458164624071725323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10132830972109749381150215 15199246458164624071725323)
          ·
            refine ⟨22798869687246936107587985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15199246458164624071725323 22798869687246936107587985)
            ·
              refine ⟨17099152265435202080690989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22798869687246936107587985 17099152265435202080690989)
              ·
                refine ⟨6412182099538200780259121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17099152265435202080690989 6412182099538200780259121)
                ·
                  refine ⟨4809136574653650585194341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6412182099538200780259121 4809136574653650585194341)
                  ·
                    refine ⟨901713107747559484723939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4809136574653650585194341 901713107747559484723939)
                    ·
                      rfl

theorem cell22_2634120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_2634120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634120 prefixEnd_2634120 := by exact prefixLift 2634120
  have htrace : WordTrace (prefixWord ++ tailWord_2634120) baseStart_2634120 baseEnd_2634120 := by
    simpa [prefixWord, tailWord_2634120, baseEnd_2634120] using wordTrace_append hprefix tailTrace_2634120
  have hstable : (prefixWord ++ tailWord_2634120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634120).length < 2 ^ (prefixWord ++ tailWord_2634120).sum := by decide
  have hdescent : baseEnd_2634120 < baseStart_2634120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634152 : List Nat := [2, 1, 6, 1, 1, 2, 2, 7]
def baseStart_2634152 : Nat := 118140960795 + 2634152 * 2 ^ 59
def prefixEnd_2634152 : Nat := 4983230072969 + 3 ^ 40 * 2634152 * 2
def baseEnd_2634152 : Nat := 100191562444613563102649

theorem tailTrace_2634152 : CollatzResearch.WordTrace tailWord_2634152 prefixEnd_2634152 100191562444613563102649 := by
  unfold tailWord_2634152
  simp only [CollatzResearch.WordTrace]
  refine ⟨48037708176462328095072355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64050277568616437460096473 48037708176462328095072355)
  ·
    refine ⟨72056562264693492142608533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48037708176462328095072355 72056562264693492142608533)
    ·
      refine ⟨3377651356157507444184775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72056562264693492142608533 3377651356157507444184775)
      ·
        refine ⟨5066477034236261166277163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3377651356157507444184775 5066477034236261166277163)
        ·
          refine ⟨7599715551354391749415745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5066477034236261166277163 7599715551354391749415745)
          ·
            refine ⟨5699786663515793812061809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7599715551354391749415745 5699786663515793812061809)
            ·
              refine ⟨4274839997636845359046357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5699786663515793812061809 4274839997636845359046357)
              ·
                refine ⟨100191562444613563102649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4274839997636845359046357 100191562444613563102649)
                ·
                  rfl

theorem cell22_2634152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 7].length) (baseStart_2634152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634152 prefixEnd_2634152 := by exact prefixLift 2634152
  have htrace : WordTrace (prefixWord ++ tailWord_2634152) baseStart_2634152 baseEnd_2634152 := by
    simpa [prefixWord, tailWord_2634152, baseEnd_2634152] using wordTrace_append hprefix tailTrace_2634152
  have hstable : (prefixWord ++ tailWord_2634152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634152).length < 2 ^ (prefixWord ++ tailWord_2634152).sum := by decide
  have hdescent : baseEnd_2634152 < baseStart_2634152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634197 : List Nat := [1, 3, 2, 3, 1, 3, 2, 2, 5]
def baseStart_2634197 : Nat := 118140960795 + 2634197 * 2 ^ 59
def prefixEnd_2634197 : Nat := 4983230072969 + 3 ^ 40 * 2634197 * 2
def baseEnd_2634197 : Nat := 300579822140385650182901

theorem tailTrace_2634197 : CollatzResearch.WordTrace tailWord_2634197 prefixEnd_2634197 300579822140385650182901 := by
  unfold tailWord_2634197
  simp only [CollatzResearch.WordTrace]
  refine ⟨96077057637761628875532845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64051371758507752583688563 96077057637761628875532845)
  ·
    refine ⟨36028896614160610828324817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96077057637761628875532845 36028896614160610828324817)
    ·
      refine ⟨27021672460620458121243613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36028896614160610828324817 27021672460620458121243613)
      ·
        refine ⟨10133127172732671795466355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27021672460620458121243613 10133127172732671795466355)
        ·
          refine ⟨15199690759099007693199533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10133127172732671795466355 15199690759099007693199533)
          ·
            refine ⟨5699884034662127884949825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15199690759099007693199533 5699884034662127884949825)
            ·
              refine ⟨4274913025996595913712369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5699884034662127884949825 4274913025996595913712369)
              ·
                refine ⟨3206184769497446935284277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4274913025996595913712369 3206184769497446935284277)
                ·
                  refine ⟨300579822140385650182901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3206184769497446935284277 300579822140385650182901)
                  ·
                    rfl

theorem cell22_2634197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_2634197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634197 prefixEnd_2634197 := by exact prefixLift 2634197
  have htrace : WordTrace (prefixWord ++ tailWord_2634197) baseStart_2634197 baseEnd_2634197 := by
    simpa [prefixWord, tailWord_2634197, baseEnd_2634197] using wordTrace_append hprefix tailTrace_2634197
  have hstable : (prefixWord ++ tailWord_2634197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634197).length < 2 ^ (prefixWord ++ tailWord_2634197).sum := by decide
  have hdescent : baseEnd_2634197 < baseStart_2634197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634225 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 6]
def baseStart_2634225 : Nat := 118140960795 + 2634225 * 2 ^ 59
def prefixEnd_2634225 : Nat := 4983230072969 + 3 ^ 40 * 2634225 * 2
def baseEnd_2634225 : Nat := 300583017131124736949539

theorem tailTrace_2634225 : CollatzResearch.WordTrace tailWord_2634225 prefixEnd_2634225 300583017131124736949539 := by
  unfold tailWord_2634225
  simp only [CollatzResearch.WordTrace]
  refine ⟨96078078881660189657552129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64052052587773459771701419 96078078881660189657552129)
  ·
    refine ⟨72058559161245142243164097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96078078881660189657552129 72058559161245142243164097)
    ·
      refine ⟨54043919370933856682373073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72058559161245142243164097 54043919370933856682373073)
      ·
        refine ⟨40532939528200392511779805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54043919370933856682373073 40532939528200392511779805)
        ·
          refine ⟨15199852323075147191917427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40532939528200392511779805 15199852323075147191917427)
          ·
            refine ⟨22799778484612720787876141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15199852323075147191917427 22799778484612720787876141)
            ·
              refine ⟨8549916931729770295453553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22799778484612720787876141 8549916931729770295453553)
              ·
                refine ⟨6412437698797327721590165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8549916931729770295453553 6412437698797327721590165)
                ·
                  refine ⟨300583017131124736949539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6412437698797327721590165 300583017131124736949539)
                  ·
                    rfl

theorem cell22_2634225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 6].length) (baseStart_2634225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634225 prefixEnd_2634225 := by exact prefixLift 2634225
  have htrace : WordTrace (prefixWord ++ tailWord_2634225) baseStart_2634225 baseEnd_2634225 := by
    simpa [prefixWord, tailWord_2634225, baseEnd_2634225] using wordTrace_append hprefix tailTrace_2634225
  have hstable : (prefixWord ++ tailWord_2634225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634225).length < 2 ^ (prefixWord ++ tailWord_2634225).sum := by decide
  have hdescent : baseEnd_2634225 < baseStart_2634225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634244 : List Nat := [2, 3, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_2634244 : Nat := 118140960795 + 2634244 * 2 ^ 59
def prefixEnd_2634244 : Nat := 4983230072969 + 3 ^ 40 * 2634244 * 2
def baseEnd_2634244 : Nat := 901755555481664494623559

theorem tailTrace_2634244 : CollatzResearch.WordTrace tailWord_2634244 prefixEnd_2634244 901755555481664494623559 := by
  unfold tailWord_2634244
  simp only [CollatzResearch.WordTrace]
  refine ⟨48039385934295677951246893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64052514579060903934995857 48039385934295677951246893)
  ·
    refine ⟨18014769725360879231717585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48039385934295677951246893 18014769725360879231717585)
    ·
      refine ⟨13511077294020659423788189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18014769725360879231717585 13511077294020659423788189)
      ·
        refine ⟨5066653985257747283920571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13511077294020659423788189 5066653985257747283920571)
        ·
          refine ⟨7599980977886620925880857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5066653985257747283920571 7599980977886620925880857)
          ·
            refine ⟨5699985733414965694410643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7599980977886620925880857 5699985733414965694410643)
            ·
              refine ⟨8549978600122448541615965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5699985733414965694410643 8549978600122448541615965)
              ·
                refine ⟨3206241975045918203105987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8549978600122448541615965 3206241975045918203105987)
                ·
                  refine ⟨4809362962568877304658981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3206241975045918203105987 4809362962568877304658981)
                  ·
                    refine ⟨901755555481664494623559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4809362962568877304658981 901755555481664494623559)
                    ·
                      rfl

theorem cell22_2634244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_2634244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634244 prefixEnd_2634244 := by exact prefixLift 2634244
  have htrace : WordTrace (prefixWord ++ tailWord_2634244) baseStart_2634244 baseEnd_2634244 := by
    simpa [prefixWord, tailWord_2634244, baseEnd_2634244] using wordTrace_append hprefix tailTrace_2634244
  have hstable : (prefixWord ++ tailWord_2634244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634244).length < 2 ^ (prefixWord ++ tailWord_2634244).sum := by decide
  have hdescent : baseEnd_2634244 < baseStart_2634244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634246 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2634246 : Nat := 118140960795 + 2634246 * 2 ^ 59
def prefixEnd_2634246 : Nat := 4983230072969 + 3 ^ 40 * 2634246 * 2
def baseEnd_2634246 : Nat := 901756240122537156073553

theorem tailTrace_2634246 : CollatzResearch.WordTrace tailWord_2634246 prefixEnd_2634246 901756240122537156073553 := by
  unfold tailWord_2634246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3002463900455753445127081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64052563209722740162711061 3002463900455753445127081)
  ·
    refine ⟨2251847925341815083845311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3002463900455753445127081 2251847925341815083845311)
    ·
      refine ⟨3377771888012722625767967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2251847925341815083845311 3377771888012722625767967)
      ·
        refine ⟨5066657832019083938651951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3377771888012722625767967 5066657832019083938651951)
        ·
          refine ⟨7599986748028625907977927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5066657832019083938651951 7599986748028625907977927)
          ·
            refine ⟨11399980122042938861966891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7599986748028625907977927 11399980122042938861966891)
            ·
              refine ⟨17099970183064408292950337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11399980122042938861966891 17099970183064408292950337)
              ·
                refine ⟨12824977637298306219712753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17099970183064408292950337 12824977637298306219712753)
                ·
                  refine ⟨9618733227973729664784565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12824977637298306219712753 9618733227973729664784565)
                  ·
                    refine ⟨901756240122537156073553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9618733227973729664784565 901756240122537156073553)
                    ·
                      rfl

theorem cell22_2634246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2634246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634246 prefixEnd_2634246 := by exact prefixLift 2634246
  have htrace : WordTrace (prefixWord ++ tailWord_2634246) baseStart_2634246 baseEnd_2634246 := by
    simpa [prefixWord, tailWord_2634246, baseEnd_2634246] using wordTrace_append hprefix tailTrace_2634246
  have hstable : (prefixWord ++ tailWord_2634246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634246).length < 2 ^ (prefixWord ++ tailWord_2634246).sum := by decide
  have hdescent : baseEnd_2634246 < baseStart_2634246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634257 : List Nat := [1, 2, 2, 1, 1, 2, 2, 6, 2, 3]
def baseStart_2634257 : Nat := 118140960795 + 2634257 * 2 ^ 59
def prefixEnd_2634257 : Nat := 4983230072969 + 3 ^ 40 * 2634257 * 2
def baseEnd_2634257 : Nat := 901760005647336794048519

theorem tailTrace_2634257 : CollatzResearch.WordTrace tailWord_2634257 prefixEnd_2634257 901760005647336794048519 := by
  unfold tailWord_2634257
  simp only [CollatzResearch.WordTrace]
  refine ⟨96079246017544259122717025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64052830678362839415144683 96079246017544259122717025)
  ·
    refine ⟨72059434513158194342037769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96079246017544259122717025 72059434513158194342037769)
    ·
      refine ⟨54044575884868645756528327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72059434513158194342037769 54044575884868645756528327)
      ·
        refine ⟨81066863827302968634792491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54044575884868645756528327 81066863827302968634792491)
        ·
          refine ⟨121600295740954452952188737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81066863827302968634792491 121600295740954452952188737)
          ·
            refine ⟨91200221805715839714141553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121600295740954452952188737 91200221805715839714141553)
            ·
              refine ⟨68400166354286879785606165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91200221805715839714141553 68400166354286879785606165)
              ·
                refine ⟨3206257797857197489950289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68400166354286879785606165 3206257797857197489950289)
                ·
                  refine ⟨2404693348392898117462717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3206257797857197489950289 2404693348392898117462717)
                  ·
                    refine ⟨901760005647336794048519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2404693348392898117462717 901760005647336794048519)
                    ·
                      rfl

theorem cell22_2634257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_2634257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634257 prefixEnd_2634257 := by exact prefixLift 2634257
  have htrace : WordTrace (prefixWord ++ tailWord_2634257) baseStart_2634257 baseEnd_2634257 := by
    simpa [prefixWord, tailWord_2634257, baseEnd_2634257] using wordTrace_append hprefix tailTrace_2634257
  have hstable : (prefixWord ++ tailWord_2634257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634257).length < 2 ^ (prefixWord ++ tailWord_2634257).sum := by decide
  have hdescent : baseEnd_2634257 < baseStart_2634257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634315 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 7]
def baseStart_2634315 : Nat := 118140960795 + 2634315 * 2 ^ 59
def prefixEnd_2634315 : Nat := 4983230072969 + 3 ^ 40 * 2634315 * 2
def baseEnd_2634315 : Nat := 300593286744214658699447

theorem tailTrace_2634315 : CollatzResearch.WordTrace tailWord_2634315 prefixEnd_2634315 300593286744214658699447 := by
  unfold tailWord_2634315
  simp only [CollatzResearch.WordTrace]
  refine ⟨96081361451334135028328399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64054240967556090018885599 96081361451334135028328399)
  ·
    refine ⟨144122042177001202542492599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96081361451334135028328399 144122042177001202542492599)
    ·
      refine ⟨216183063265501803813738899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144122042177001202542492599 216183063265501803813738899)
      ·
        refine ⟨324274594898252705720608349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216183063265501803813738899 324274594898252705720608349)
        ·
          refine ⟨121602973086844764645228131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 324274594898252705720608349 121602973086844764645228131)
          ·
            refine ⟨182404459630267146967842197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121602973086844764645228131 182404459630267146967842197)
            ·
              refine ⟨8550209045168772514117603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 182404459630267146967842197 8550209045168772514117603)
              ·
                refine ⟨12825313567753158771176405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8550209045168772514117603 12825313567753158771176405)
                ·
                  refine ⟨300593286744214658699447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12825313567753158771176405 300593286744214658699447)
                  ·
                    rfl

theorem cell22_2634315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 7].length) (baseStart_2634315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634315 prefixEnd_2634315 := by exact prefixLift 2634315
  have htrace : WordTrace (prefixWord ++ tailWord_2634315) baseStart_2634315 baseEnd_2634315 := by
    simpa [prefixWord, tailWord_2634315, baseEnd_2634315] using wordTrace_append hprefix tailTrace_2634315
  have hstable : (prefixWord ++ tailWord_2634315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634315).length < 2 ^ (prefixWord ++ tailWord_2634315).sum := by decide
  have hdescent : baseEnd_2634315 < baseStart_2634315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634319 : List Nat := [1, 1, 2, 1, 1, 2, 4, 6, 1, 3]
def baseStart_2634319 : Nat := 118140960795 + 2634319 * 2 ^ 59
def prefixEnd_2634319 : Nat := 4983230072969 + 3 ^ 40 * 2634319 * 2
def baseEnd_2634319 : Nat := 901781229514389298998329

theorem tailTrace_2634319 : CollatzResearch.WordTrace tailWord_2634319 prefixEnd_2634319 901781229514389298998329 := by
  unfold tailWord_2634319
  simp only [CollatzResearch.WordTrace]
  refine ⟨96081507343319643711474011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64054338228879762474316007 96081507343319643711474011)
  ·
    refine ⟨144122261014979465567211017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96081507343319643711474011 144122261014979465567211017)
    ·
      refine ⟨108091695761234599175408263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144122261014979465567211017 108091695761234599175408263)
      ·
        refine ⟨162137543641851898763112395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108091695761234599175408263 162137543641851898763112395)
        ·
          refine ⟨243206315462777848144668593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162137543641851898763112395 243206315462777848144668593)
          ·
            refine ⟨182404736597083386108501445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243206315462777848144668593 182404736597083386108501445)
            ·
              refine ⟨34200888111953134895344021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182404736597083386108501445 34200888111953134895344021)
              ·
                refine ⟨1603166630247803198219251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34200888111953134895344021 1603166630247803198219251)
                ·
                  refine ⟨2404749945371704797328877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603166630247803198219251 2404749945371704797328877)
                  ·
                    refine ⟨901781229514389298998329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2404749945371704797328877 901781229514389298998329)
                    ·
                      rfl

theorem cell22_2634319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 1, 3].length) (baseStart_2634319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634319 prefixEnd_2634319 := by exact prefixLift 2634319
  have htrace : WordTrace (prefixWord ++ tailWord_2634319) baseStart_2634319 baseEnd_2634319 := by
    simpa [prefixWord, tailWord_2634319, baseEnd_2634319] using wordTrace_append hprefix tailTrace_2634319
  have hstable : (prefixWord ++ tailWord_2634319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634319).length < 2 ^ (prefixWord ++ tailWord_2634319).sum := by decide
  have hdescent : baseEnd_2634319 < baseStart_2634319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634360 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 8]
def baseStart_2634360 : Nat := 118140960795 + 2634360 * 2 ^ 59
def prefixEnd_2634360 : Nat := 4983230072969 + 3 ^ 40 * 2634360 * 2
def baseEnd_2634360 : Nat := 300598421550759619574401

theorem tailTrace_2634360 : CollatzResearch.WordTrace tailWord_2634360 prefixEnd_2634360 300598421550759619574401 := by
  unfold tailWord_2634360
  simp only [CollatzResearch.WordTrace]
  refine ⟨48041501368085553856858267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64055335157447405142477689 48041501368085553856858267)
  ·
    refine ⟨72062252052128330785287401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48041501368085553856858267 72062252052128330785287401)
    ·
      refine ⟨54046689039096248088965551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72062252052128330785287401 54046689039096248088965551)
      ·
        refine ⟨81070033558644372133448327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54046689039096248088965551 81070033558644372133448327)
        ·
          refine ⟨121605050337966558200172491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81070033558644372133448327 121605050337966558200172491)
          ·
            refine ⟨182407575506949837300258737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121605050337966558200172491 182407575506949837300258737)
            ·
              refine ⟨136805681630212377975194053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182407575506949837300258737 136805681630212377975194053)
              ·
                refine ⟨25651065305664820870348885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136805681630212377975194053 25651065305664820870348885)
                ·
                  refine ⟨300598421550759619574401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25651065305664820870348885 300598421550759619574401)
                  ·
                    rfl

theorem cell22_2634360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 8].length) (baseStart_2634360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634360 prefixEnd_2634360 := by exact prefixLift 2634360
  have htrace : WordTrace (prefixWord ++ tailWord_2634360) baseStart_2634360 baseEnd_2634360 := by
    simpa [prefixWord, tailWord_2634360, baseEnd_2634360] using wordTrace_append hprefix tailTrace_2634360
  have hstable : (prefixWord ++ tailWord_2634360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634360).length < 2 ^ (prefixWord ++ tailWord_2634360).sum := by decide
  have hdescent : baseEnd_2634360 < baseStart_2634360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634413 : List Nat := [1, 5, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_2634413 : Nat := 118140960795 + 2634413 * 2 ^ 59
def prefixEnd_2634413 : Nat := 4983230072969 + 3 ^ 40 * 2634413 * 2
def baseEnd_2634413 : Nat := 901813407635404387148041

theorem tailTrace_2634413 : CollatzResearch.WordTrace tailWord_2634413 prefixEnd_2634413 901813407635404387148041 := by
  unfold tailWord_2634413
  simp only [CollatzResearch.WordTrace]
  refine ⟨96084935804979097765395893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64056623869986065176930595 96084935804979097765395893)
  ·
    refine ⟨9007962731716790415505865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96084935804979097765395893 9007962731716790415505865)
    ·
      refine ⟨6755972048787592811629399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9007962731716790415505865 6755972048787592811629399)
      ·
        refine ⟨10133958073181389217444099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6755972048787592811629399 10133958073181389217444099)
        ·
          refine ⟨15200937109772083826166149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10133958073181389217444099 15200937109772083826166149)
          ·
            refine ⟨2850175708082265717406153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15200937109772083826166149 2850175708082265717406153)
            ·
              refine ⟨2137631781061699288054615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2850175708082265717406153 2137631781061699288054615)
              ·
                refine ⟨3206447671592548932081923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2137631781061699288054615 3206447671592548932081923)
                ·
                  refine ⟨4809671507388823398122885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3206447671592548932081923 4809671507388823398122885)
                  ·
                    refine ⟨901813407635404387148041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4809671507388823398122885 901813407635404387148041)
                    ·
                      rfl

theorem cell22_2634413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_2634413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634413 prefixEnd_2634413 := by exact prefixLift 2634413
  have htrace : WordTrace (prefixWord ++ tailWord_2634413) baseStart_2634413 baseEnd_2634413 := by
    simpa [prefixWord, tailWord_2634413, baseEnd_2634413] using wordTrace_append hprefix tailTrace_2634413
  have hstable : (prefixWord ++ tailWord_2634413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634413).length < 2 ^ (prefixWord ++ tailWord_2634413).sum := by decide
  have hdescent : baseEnd_2634413 < baseStart_2634413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634488 : List Nat := [2, 1, 2, 1, 1, 2, 7, 2, 1, 3]
def baseStart_2634488 : Nat := 118140960795 + 2634488 * 2 ^ 59
def prefixEnd_2634488 : Nat := 4983230072969 + 3 ^ 40 * 2634488 * 2
def baseEnd_2634488 : Nat := 901839081668129191522811

theorem tailTrace_2634488 : CollatzResearch.WordTrace tailWord_2634488 prefixEnd_2634488 901839081668129191522811 := by
  unfold tailWord_2634488
  simp only [CollatzResearch.WordTrace]
  refine ⟨48043835639853692787188059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64058447519804923716250745 48043835639853692787188059)
  ·
    refine ⟨72065753459780539180782089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48043835639853692787188059 72065753459780539180782089)
    ·
      refine ⟨54049315094835404385586567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72065753459780539180782089 54049315094835404385586567)
      ·
        refine ⟨81073972642253106578379851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54049315094835404385586567 81073972642253106578379851)
        ·
          refine ⟨121610958963379659867569777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81073972642253106578379851 121610958963379659867569777)
          ·
            refine ⟨91208219222534744900677333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121610958963379659867569777 91208219222534744900677333)
            ·
              refine ⟨2137692638028158083609625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 91208219222534744900677333 2137692638028158083609625)
              ·
                refine ⟨1603269478521118562707219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2137692638028158083609625 1603269478521118562707219)
                ·
                  refine ⟨2404904217781677844060829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603269478521118562707219 2404904217781677844060829)
                  ·
                    refine ⟨901839081668129191522811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2404904217781677844060829 901839081668129191522811)
                    ·
                      rfl

theorem cell22_2634488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_2634488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634488 prefixEnd_2634488 := by exact prefixLift 2634488
  have htrace : WordTrace (prefixWord ++ tailWord_2634488) baseStart_2634488 baseEnd_2634488 := by
    simpa [prefixWord, tailWord_2634488, baseEnd_2634488] using wordTrace_append hprefix tailTrace_2634488
  have hstable : (prefixWord ++ tailWord_2634488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634488).length < 2 ^ (prefixWord ++ tailWord_2634488).sum := by decide
  have hdescent : baseEnd_2634488 < baseStart_2634488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634497 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 2, 8]
def baseStart_2634497 : Nat := 118140960795 + 2634497 * 2 ^ 59
def prefixEnd_2634497 : Nat := 4983230072969 + 3 ^ 40 * 2634497 * 2
def baseEnd_2634497 : Nat := 901842162552056168047783

theorem tailTrace_2634497 : CollatzResearch.WordTrace tailWord_2634497 prefixEnd_2634497 901842162552056168047783 := by
  unfold tailWord_2634497
  simp only [CollatzResearch.WordTrace]
  refine ⟨96087999536674780111453745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64058666357783186740969163 96087999536674780111453745)
  ·
    refine ⟨72065999652506085083590309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96087999536674780111453745 72065999652506085083590309)
    ·
      refine ⟨13512374934844890953173183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72065999652506085083590309 13512374934844890953173183)
      ·
        refine ⟨20268562402267336429759775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13512374934844890953173183 20268562402267336429759775)
        ·
          refine ⟨30402843603401004644639663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20268562402267336429759775 30402843603401004644639663)
          ·
            refine ⟨45604265405101506966959495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30402843603401004644639663 45604265405101506966959495)
            ·
              refine ⟨68406398107652260450439243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45604265405101506966959495 68406398107652260450439243)
              ·
                refine ⟨102609597161478390675658865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68406398107652260450439243 102609597161478390675658865)
                ·
                  refine ⟨76957197871108793006744149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102609597161478390675658865 76957197871108793006744149)
                  ·
                    refine ⟨901842162552056168047783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76957197871108793006744149 901842162552056168047783)
                    ·
                      rfl

theorem cell22_2634497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_2634497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634497 prefixEnd_2634497 := by exact prefixLift 2634497
  have htrace : WordTrace (prefixWord ++ tailWord_2634497) baseStart_2634497 baseEnd_2634497 := by
    simpa [prefixWord, tailWord_2634497, baseEnd_2634497] using wordTrace_append hprefix tailTrace_2634497
  have hstable : (prefixWord ++ tailWord_2634497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634497).length < 2 ^ (prefixWord ++ tailWord_2634497).sum := by decide
  have hdescent : baseEnd_2634497 < baseStart_2634497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634544 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 4, 3]
def baseStart_2634544 : Nat := 118140960795 + 2634544 * 2 ^ 59
def prefixEnd_2634544 : Nat := 4983230072969 + 3 ^ 40 * 2634544 * 2
def baseEnd_2634544 : Nat := 901858251612563712122639

theorem tailTrace_2634544 : CollatzResearch.WordTrace tailWord_2634544 prefixEnd_2634544 901858251612563712122639 := by
  unfold tailWord_2634544
  simp only [CollatzResearch.WordTrace]
  refine ⟨48044856883752253569207343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64059809178336338092276457 48044856883752253569207343)
  ·
    refine ⟨72067285325628380353811015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48044856883752253569207343 72067285325628380353811015)
    ·
      refine ⟨108100927988442570530716523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72067285325628380353811015 108100927988442570530716523)
      ·
        refine ⟨162151391982663855796074785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108100927988442570530716523 162151391982663855796074785)
        ·
          refine ⟨121613543986997891847056089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162151391982663855796074785 121613543986997891847056089)
          ·
            refine ⟨91210157990248418885292067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121613543986997891847056089 91210157990248418885292067)
            ·
              refine ⟨136815236985372628327938101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91210157990248418885292067 136815236985372628327938101)
              ·
                refine ⟨12826428467378683905744197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136815236985372628327938101 12826428467378683905744197)
                ·
                  refine ⟨2404955337633503232327037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12826428467378683905744197 2404955337633503232327037)
                  ·
                    refine ⟨901858251612563712122639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2404955337633503232327037 901858251612563712122639)
                    ·
                      rfl

theorem cell22_2634544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 4, 3].length) (baseStart_2634544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634544 prefixEnd_2634544 := by exact prefixLift 2634544
  have htrace : WordTrace (prefixWord ++ tailWord_2634544) baseStart_2634544 baseEnd_2634544 := by
    simpa [prefixWord, tailWord_2634544, baseEnd_2634544] using wordTrace_append hprefix tailTrace_2634544
  have hstable : (prefixWord ++ tailWord_2634544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634544).length < 2 ^ (prefixWord ++ tailWord_2634544).sum := by decide
  have hdescent : baseEnd_2634544 < baseStart_2634544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634546 : List Nat := [3, 2, 1, 1, 3, 1, 3, 4, 4]
def baseStart_2634546 : Nat := 118140960795 + 2634546 * 2 ^ 59
def prefixEnd_2634546 : Nat := 4983230072969 + 3 ^ 40 * 2634546 * 2
def baseEnd_2634546 : Nat := 300619645417812124524211

theorem tailTrace_2634546 : CollatzResearch.WordTrace tailWord_2634546 prefixEnd_2634546 300619645417812124524211 := by
  unfold tailWord_2634546
  simp only [CollatzResearch.WordTrace]
  refine ⟨24022446678374315369996873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64059857808998174319991661 24022446678374315369996873)
  ·
    refine ⟨18016835008780736527497655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24022446678374315369996873 18016835008780736527497655)
    ·
      refine ⟨27025252513171104791246483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18016835008780736527497655 27025252513171104791246483)
      ·
        refine ⟨40537878769756657186869725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27025252513171104791246483 40537878769756657186869725)
        ·
          refine ⟨15201704538658746445076147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40537878769756657186869725 15201704538658746445076147)
          ·
            refine ⟨22802556807988119667614221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15201704538658746445076147 22802556807988119667614221)
            ·
              refine ⟨8550958802995544875355333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22802556807988119667614221 8550958802995544875355333)
              ·
                refine ⟨1603304775561664664129125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8550958802995544875355333 1603304775561664664129125)
                ·
                  refine ⟨300619645417812124524211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1603304775561664664129125 300619645417812124524211)
                  ·
                    rfl

theorem cell22_2634546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_2634546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634546 prefixEnd_2634546 := by exact prefixLift 2634546
  have htrace : WordTrace (prefixWord ++ tailWord_2634546) baseStart_2634546 baseEnd_2634546 := by
    simpa [prefixWord, tailWord_2634546, baseEnd_2634546] using wordTrace_append hprefix tailTrace_2634546
  have hstable : (prefixWord ++ tailWord_2634546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634546).length < 2 ^ (prefixWord ++ tailWord_2634546).sum := by decide
  have hdescent : baseEnd_2634546 < baseStart_2634546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634619 : List Nat := [1, 1, 1, 1, 1, 5, 2, 5, 5]
def baseStart_2634619 : Nat := 118140960795 + 2634619 * 2 ^ 59
def prefixEnd_2634619 : Nat := 4983230072969 + 3 ^ 40 * 2634619 * 2
def baseEnd_2634619 : Nat := 300627975215096172165803

theorem tailTrace_2634619 : CollatzResearch.WordTrace tailWord_2634619 prefixEnd_2634619 300627975215096172165803 := by
  unfold tailWord_2634619
  simp only [CollatzResearch.WordTrace]
  refine ⟨96092449242232794947394911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64061632828155196631596607 96092449242232794947394911)
  ·
    refine ⟨144138673863349192421092367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96092449242232794947394911 144138673863349192421092367)
    ·
      refine ⟨216208010795023788631638551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144138673863349192421092367 216208010795023788631638551)
      ·
        refine ⟨324312016192535682947457827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216208010795023788631638551 324312016192535682947457827)
        ·
          refine ⟨486468024288803524421186741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324312016192535682947457827 486468024288803524421186741)
          ·
            refine ⟨45606377277075330414486257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 486468024288803524421186741 45606377277075330414486257)
            ·
              refine ⟨34204782957806497810864693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45606377277075330414486257 34204782957806497810864693)
              ·
                refine ⟨3206698402294359169768565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34204782957806497810864693 3206698402294359169768565)
                ·
                  refine ⟨300627975215096172165803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3206698402294359169768565 300627975215096172165803)
                  ·
                    rfl

theorem cell22_2634619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 5].length) (baseStart_2634619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634619 prefixEnd_2634619 := by exact prefixLift 2634619
  have htrace : WordTrace (prefixWord ++ tailWord_2634619) baseStart_2634619 baseEnd_2634619 := by
    simpa [prefixWord, tailWord_2634619, baseEnd_2634619] using wordTrace_append hprefix tailTrace_2634619
  have hstable : (prefixWord ++ tailWord_2634619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634619).length < 2 ^ (prefixWord ++ tailWord_2634619).sum := by decide
  have hdescent : baseEnd_2634619 < baseStart_2634619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634649 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 5, 4]
def baseStart_2634649 : Nat := 118140960795 + 2634649 * 2 ^ 59
def prefixEnd_2634649 : Nat := 4983230072969 + 3 ^ 40 * 2634649 * 2
def baseEnd_2634649 : Nat := 901894195258378438247317

theorem tailTrace_2634649 : CollatzResearch.WordTrace tailWord_2634649 prefixEnd_2634649 901894195258378438247317 := by
  unfold tailWord_2634649
  simp only [CollatzResearch.WordTrace]
  refine ⟨96093543432124110070987001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64062362288082740047324667 96093543432124110070987001)
  ·
    refine ⟨72070157574093082553240251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96093543432124110070987001 72070157574093082553240251)
    ·
      refine ⟨108105236361139623829860377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72070157574093082553240251 108105236361139623829860377)
      ·
        refine ⟨81078927270854717872395283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108105236361139623829860377 81078927270854717872395283)
        ·
          refine ⟨121618390906282076808592925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81078927270854717872395283 121618390906282076808592925)
          ·
            refine ⟨45606896589855778803222347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121618390906282076808592925 45606896589855778803222347)
            ·
              refine ⟨68410344884783668204833521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45606896589855778803222347 68410344884783668204833521)
              ·
                refine ⟨51307758663587751153625141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68410344884783668204833521 51307758663587751153625141)
                ·
                  refine ⟨4810102374711351670652357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51307758663587751153625141 4810102374711351670652357)
                  ·
                    refine ⟨901894195258378438247317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4810102374711351670652357 901894195258378438247317)
                    ·
                      rfl

theorem cell22_2634649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_2634649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634649 prefixEnd_2634649 := by exact prefixLift 2634649
  have htrace : WordTrace (prefixWord ++ tailWord_2634649) baseStart_2634649 baseEnd_2634649 := by
    simpa [prefixWord, tailWord_2634649, baseEnd_2634649] using wordTrace_append hprefix tailTrace_2634649
  have hstable : (prefixWord ++ tailWord_2634649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634649).length < 2 ^ (prefixWord ++ tailWord_2634649).sum := by decide
  have hdescent : baseEnd_2634649 < baseStart_2634649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634657 : List Nat := [1, 2, 3, 4, 1, 2, 3, 2, 1, 3]
def baseStart_2634657 : Nat := 118140960795 + 2634657 * 2 ^ 59
def prefixEnd_2634657 : Nat := 4983230072969 + 3 ^ 40 * 2634657 * 2
def baseEnd_2634657 : Nat := 901896933821869084047293

theorem tailTrace_2634657 : CollatzResearch.WordTrace tailWord_2634657 prefixEnd_2634657 901896933821869084047293 := by
  unfold tailWord_2634657
  simp only [CollatzResearch.WordTrace]
  refine ⟨96093835216095127437278225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64062556810730084958185483 96093835216095127437278225)
  ·
    refine ⟨72070376412071345577958669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96093835216095127437278225 72070376412071345577958669)
    ·
      refine ⟨27026391154526754591734501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72070376412071345577958669 27026391154526754591734501)
      ·
        refine ⟨5067448341473766485950219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27026391154526754591734501 5067448341473766485950219)
        ·
          refine ⟨7601172512210649728925329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5067448341473766485950219 7601172512210649728925329)
          ·
            refine ⟨5700879384157987296693997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7601172512210649728925329 5700879384157987296693997)
            ·
              refine ⟨2137829769059245236260249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5700879384157987296693997 2137829769059245236260249)
              ·
                refine ⟨1603372326794433927195187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2137829769059245236260249 1603372326794433927195187)
                ·
                  refine ⟨2405058490191650890792781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603372326794433927195187 2405058490191650890792781)
                  ·
                    refine ⟨901896933821869084047293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2405058490191650890792781 901896933821869084047293)
                    ·
                      rfl

theorem cell22_2634657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_2634657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634657 prefixEnd_2634657 := by exact prefixLift 2634657
  have htrace : WordTrace (prefixWord ++ tailWord_2634657) baseStart_2634657 baseEnd_2634657 := by
    simpa [prefixWord, tailWord_2634657, baseEnd_2634657] using wordTrace_append hprefix tailTrace_2634657
  have hstable : (prefixWord ++ tailWord_2634657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634657).length < 2 ^ (prefixWord ++ tailWord_2634657).sum := by decide
  have hdescent : baseEnd_2634657 < baseStart_2634657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634709 : List Nat := [1, 3, 2, 3, 13]
def baseStart_2634709 : Nat := 118140960795 + 2634709 * 2 ^ 59
def prefixEnd_2634709 : Nat := 4983230072969 + 3 ^ 40 * 2634709 * 2
def baseEnd_2634709 : Nat := 3711583269483778937231

theorem tailTrace_2634709 : CollatzResearch.WordTrace tailWord_2634709 prefixEnd_2634709 3711583269483778937231 := by
  unfold tailWord_2634709
  simp only [CollatzResearch.WordTrace]
  refine ⟨96095731811906740318171181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64063821207937826878780787 96095731811906740318171181)
  ·
    refine ⟨36035899429465027619314193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96095731811906740318171181 36035899429465027619314193)
    ·
      refine ⟨27026924572098770714485645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36035899429465027619314193 27026924572098770714485645)
      ·
        refine ⟨10135096714537039017932117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27026924572098770714485645 10135096714537039017932117)
        ·
          refine ⟨3711583269483778937231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 10135096714537039017932117 3711583269483778937231)
          ·
            rfl

theorem cell22_2634709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 13].length) (baseStart_2634709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634709 prefixEnd_2634709 := by exact prefixLift 2634709
  have htrace : WordTrace (prefixWord ++ tailWord_2634709) baseStart_2634709 baseEnd_2634709 := by
    simpa [prefixWord, tailWord_2634709, baseEnd_2634709] using wordTrace_append hprefix tailTrace_2634709
  have hstable : (prefixWord ++ tailWord_2634709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634709).length < 2 ^ (prefixWord ++ tailWord_2634709).sum := by decide
  have hdescent : baseEnd_2634709 < baseStart_2634709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634713 : List Nat := [1, 2, 1, 2, 5, 1, 1, 4, 2, 3]
def baseStart_2634713 : Nat := 118140960795 + 2634713 * 2 ^ 59
def prefixEnd_2634713 : Nat := 4983230072969 + 3 ^ 40 * 2634713 * 2
def baseEnd_2634713 : Nat := 901916103766303604647121

theorem tailTrace_2634713 : CollatzResearch.WordTrace tailWord_2634713 prefixEnd_2634713 901916103766303604647121 := by
  unfold tailWord_2634713
  simp only [CollatzResearch.WordTrace]
  refine ⟨96095877703892249001316793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64063918469261499334211195 96095877703892249001316793)
  ·
    refine ⟨72071908277919186750987595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96095877703892249001316793 72071908277919186750987595)
    ·
      refine ⟨108107862416878780126481393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72071908277919186750987595 108107862416878780126481393)
      ·
        refine ⟨81080896812659085094861045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108107862416878780126481393 81080896812659085094861045)
        ·
          refine ⟨7601334076186789227643223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81080896812659085094861045 7601334076186789227643223)
          ·
            refine ⟨11402001114280183841464835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7601334076186789227643223 11402001114280183841464835)
            ·
              refine ⟨17103001671420275762197253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11402001114280183841464835 17103001671420275762197253)
              ·
                refine ⟨3206812813391301705411985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17103001671420275762197253 3206812813391301705411985)
                ·
                  refine ⟨2405109610043476279058989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3206812813391301705411985 2405109610043476279058989)
                  ·
                    refine ⟨901916103766303604647121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2405109610043476279058989 901916103766303604647121)
                    ·
                      rfl

theorem cell22_2634713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 3].length) (baseStart_2634713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634713 prefixEnd_2634713 := by exact prefixLift 2634713
  have htrace : WordTrace (prefixWord ++ tailWord_2634713) baseStart_2634713 baseEnd_2634713 := by
    simpa [prefixWord, tailWord_2634713, baseEnd_2634713] using wordTrace_append hprefix tailTrace_2634713
  have hstable : (prefixWord ++ tailWord_2634713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634713).length < 2 ^ (prefixWord ++ tailWord_2634713).sum := by decide
  have hdescent : baseEnd_2634713 < baseStart_2634713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634775 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 3, 3]
def baseStart_2634775 : Nat := 118140960795 + 2634775 * 2 ^ 59
def prefixEnd_2634775 : Nat := 4983230072969 + 3 ^ 40 * 2634775 * 2
def baseEnd_2634775 : Nat := 901937327633356109596931

theorem tailTrace_2634775 : CollatzResearch.WordTrace tailWord_2634775 prefixEnd_2634775 901937327633356109596931 := by
  unfold tailWord_2634775
  simp only [CollatzResearch.WordTrace]
  refine ⟨96098139029667633590073779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64065426019778422393382519 96098139029667633590073779)
  ·
    refine ⟨144147208544501450385110669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96098139029667633590073779 144147208544501450385110669)
    ·
      refine ⟨54055203204188043894416501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144147208544501450385110669 54055203204188043894416501)
      ·
        refine ⟨5067675300392629115101547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54055203204188043894416501 5067675300392629115101547)
        ·
          refine ⟨7601512950588943672652321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5067675300392629115101547 7601512950588943672652321)
          ·
            refine ⟨5701134712941707754489241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7601512950588943672652321 5701134712941707754489241)
            ·
              refine ⟨4275851034706280815866931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5701134712941707754489241 4275851034706280815866931)
              ·
                refine ⟨6413776552059421223800397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4275851034706280815866931 6413776552059421223800397)
                ·
                  refine ⟨2405166207022282958925149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6413776552059421223800397 2405166207022282958925149)
                  ·
                    refine ⟨901937327633356109596931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2405166207022282958925149 901937327633356109596931)
                    ·
                      rfl

theorem cell22_2634775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_2634775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634775 prefixEnd_2634775 := by exact prefixLift 2634775
  have htrace : WordTrace (prefixWord ++ tailWord_2634775) baseStart_2634775 baseEnd_2634775 := by
    simpa [prefixWord, tailWord_2634775, baseEnd_2634775] using wordTrace_append hprefix tailTrace_2634775
  have hstable : (prefixWord ++ tailWord_2634775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634775).length < 2 ^ (prefixWord ++ tailWord_2634775).sum := by decide
  have hdescent : baseEnd_2634775 < baseStart_2634775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634833 : List Nat := [1, 2, 2, 1, 3, 1, 2, 6, 4]
def baseStart_2634833 : Nat := 118140960795 + 2634833 * 2 ^ 59
def prefixEnd_2634833 : Nat := 4983230072969 + 3 ^ 40 * 2634833 * 2
def baseEnd_2634833 : Nat := 300652394072887763882251

theorem tailTrace_2634833 : CollatzResearch.WordTrace tailWord_2634833 prefixEnd_2634833 300652394072887763882251 := by
  unfold tailWord_2634833
  simp only [CollatzResearch.WordTrace]
  refine ⟨96100254463457509495685153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64066836308971672997123435 96100254463457509495685153)
  ·
    refine ⟨72075190847593132121763865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96100254463457509495685153 72075190847593132121763865)
    ·
      refine ⟨54056393135694849091322899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72075190847593132121763865 54056393135694849091322899)
      ·
        refine ⟨81084589703542273636984349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54056393135694849091322899 81084589703542273636984349)
        ·
          refine ⟨30406721138828352613869131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81084589703542273636984349 30406721138828352613869131)
          ·
            refine ⟨45610081708242528920803697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30406721138828352613869131 45610081708242528920803697)
            ·
              refine ⟨34207561281181896690602773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45610081708242528920803697 34207561281181896690602773)
              ·
                refine ⟨1603479435055401407372005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34207561281181896690602773 1603479435055401407372005)
                ·
                  refine ⟨300652394072887763882251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1603479435055401407372005 300652394072887763882251)
                  ·
                    rfl

theorem cell22_2634833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 4].length) (baseStart_2634833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634833 prefixEnd_2634833 := by exact prefixLift 2634833
  have htrace : WordTrace (prefixWord ++ tailWord_2634833) baseStart_2634833 baseEnd_2634833 := by
    simpa [prefixWord, tailWord_2634833, baseEnd_2634833] using wordTrace_append hprefix tailTrace_2634833
  have hstable : (prefixWord ++ tailWord_2634833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634833).length < 2 ^ (prefixWord ++ tailWord_2634833).sum := by decide
  have hdescent : baseEnd_2634833 < baseStart_2634833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634863 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 2, 4]
def baseStart_2634863 : Nat := 118140960795 + 2634863 * 2 ^ 59
def prefixEnd_2634863 : Nat := 4983230072969 + 3 ^ 40 * 2634863 * 2
def baseEnd_2634863 : Nat := 901967451831753213396661

theorem tailTrace_2634863 : CollatzResearch.WordTrace tailWord_2634863 prefixEnd_2634863 901967451831753213396661 := by
  unfold tailWord_2634863
  simp only [CollatzResearch.WordTrace]
  refine ⟨96101348653348824619277243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64067565768899216412851495 96101348653348824619277243)
  ·
    refine ⟨144152022980023236928915865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96101348653348824619277243 144152022980023236928915865)
    ·
      refine ⟨108114017235017427696686899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144152022980023236928915865 108114017235017427696686899)
      ·
        refine ⟨162171025852526141545030349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108114017235017427696686899 162171025852526141545030349)
        ·
          refine ⟨60814134694697303079386381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162171025852526141545030349 60814134694697303079386381)
          ·
            refine ⟨22805300510511488654769893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60814134694697303079386381 22805300510511488654769893)
            ·
              refine ⟨4275993845720904122769355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22805300510511488654769893 4275993845720904122769355)
              ·
                refine ⟨6413990768581356184154033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4275993845720904122769355 6413990768581356184154033)
                ·
                  refine ⟨4810493076436017138115525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6413990768581356184154033 4810493076436017138115525)
                  ·
                    refine ⟨901967451831753213396661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4810493076436017138115525 901967451831753213396661)
                    ·
                      rfl

theorem cell22_2634863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_2634863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634863 prefixEnd_2634863 := by exact prefixLift 2634863
  have htrace : WordTrace (prefixWord ++ tailWord_2634863) baseStart_2634863 baseEnd_2634863 := by
    simpa [prefixWord, tailWord_2634863, baseEnd_2634863] using wordTrace_append hprefix tailTrace_2634863
  have hstable : (prefixWord ++ tailWord_2634863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634863).length < 2 ^ (prefixWord ++ tailWord_2634863).sum := by decide
  have hdescent : baseEnd_2634863 < baseStart_2634863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634869 : List Nat := [1, 3, 4, 3, 1, 1, 3, 1, 1, 4]
def baseStart_2634869 : Nat := 118140960795 + 2634869 * 2 ^ 59
def prefixEnd_2634869 : Nat := 4983230072969 + 3 ^ 40 * 2634869 * 2
def baseEnd_2634869 : Nat := 901969505754371197746643

theorem tailTrace_2634869 : CollatzResearch.WordTrace tailWord_2634869 prefixEnd_2634869 901969505754371197746643 := by
  unfold tailWord_2634869
  simp only [CollatzResearch.WordTrace]
  refine ⟨96101567491327087643995661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64067711660884725095997107 96101567491327087643995661)
  ·
    refine ⟨36038087809247657866498373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96101567491327087643995661 36038087809247657866498373)
    ·
      refine ⟨6757141464233935849968445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36038087809247657866498373 6757141464233935849968445)
      ·
        refine ⟨2533928049087725943738167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6757141464233935849968445 2533928049087725943738167)
        ·
          refine ⟨3800892073631588915607251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533928049087725943738167 3800892073631588915607251)
          ·
            refine ⟨5701338110447383373410877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3800892073631588915607251 5701338110447383373410877)
            ·
              refine ⟨2138001791417768765029079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5701338110447383373410877 2138001791417768765029079)
              ·
                refine ⟨3207002687126653147543619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138001791417768765029079 3207002687126653147543619)
                ·
                  refine ⟨4810504030689979721315429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207002687126653147543619 4810504030689979721315429)
                  ·
                    refine ⟨901969505754371197746643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4810504030689979721315429 901969505754371197746643)
                    ·
                      rfl

theorem cell22_2634869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_2634869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634869 prefixEnd_2634869 := by exact prefixLift 2634869
  have htrace : WordTrace (prefixWord ++ tailWord_2634869) baseStart_2634869 baseEnd_2634869 := by
    simpa [prefixWord, tailWord_2634869, baseEnd_2634869] using wordTrace_append hprefix tailTrace_2634869
  have hstable : (prefixWord ++ tailWord_2634869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634869).length < 2 ^ (prefixWord ++ tailWord_2634869).sum := by decide
  have hdescent : baseEnd_2634869 < baseStart_2634869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634914 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_2634914 : Nat := 118140960795 + 2634914 * 2 ^ 59
def prefixEnd_2634914 : Nat := 4983230072969 + 3 ^ 40 * 2634914 * 2
def baseEnd_2634914 : Nat := 901984910174006080371505

theorem tailTrace_2634914 : CollatzResearch.WordTrace tailWord_2634914 prefixEnd_2634914 901984910174006080371505 := by
  unfold tailWord_2634914
  simp only [CollatzResearch.WordTrace]
  refine ⟨24025802194041015082345949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64068805850776040219589197 24025802194041015082345949)
  ·
    refine ⟨9009675822765380655879731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24025802194041015082345949 9009675822765380655879731)
    ·
      refine ⟨13514513734148070983819597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9009675822765380655879731 13514513734148070983819597)
      ·
        refine ⟨5067942650305526618932349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13514513734148070983819597 5067942650305526618932349)
        ·
          refine ⟨1900478493864572482099631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5067942650305526618932349 1900478493864572482099631)
          ·
            refine ⟨2850717740796858723149447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1900478493864572482099631 2850717740796858723149447)
            ·
              refine ⟨4276076611195288084724171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2850717740796858723149447 4276076611195288084724171)
              ·
                refine ⟨6414114916792932127086257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4276076611195288084724171 6414114916792932127086257)
                ·
                  refine ⟨4810586187594699095314693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6414114916792932127086257 4810586187594699095314693)
                  ·
                    refine ⟨901984910174006080371505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4810586187594699095314693 901984910174006080371505)
                    ·
                      rfl

theorem cell22_2634914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_2634914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634914 prefixEnd_2634914 := by exact prefixLift 2634914
  have htrace : WordTrace (prefixWord ++ tailWord_2634914) baseStart_2634914 baseEnd_2634914 := by
    simpa [prefixWord, tailWord_2634914, baseEnd_2634914] using wordTrace_append hprefix tailTrace_2634914
  have hstable : (prefixWord ++ tailWord_2634914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634914).length < 2 ^ (prefixWord ++ tailWord_2634914).sum := by decide
  have hdescent : baseEnd_2634914 < baseStart_2634914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634940 : List Nat := [2, 2, 2, 3, 2, 1, 3, 2, 5]
def baseStart_2634940 : Nat := 118140960795 + 2634940 * 2 ^ 59
def prefixEnd_2634940 : Nat := 4983230072969 + 3 ^ 40 * 2634940 * 2
def baseEnd_2634940 : Nat := 300664603501783559740475

theorem tailTrace_2634940 : CollatzResearch.WordTrace tailWord_2634940 prefixEnd_2634940 300664603501783559740475 := by
  unfold tailWord_2634940
  simp only [CollatzResearch.WordTrace]
  refine ⟨48052078537034933384915137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64069438049379911179886849 48052078537034933384915137)
  ·
    refine ⟨36039058902776200038686353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48052078537034933384915137 36039058902776200038686353)
    ·
      refine ⟨27029294177082150029014765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36039058902776200038686353 27029294177082150029014765)
      ·
        refine ⟨10135985316405806260880537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27029294177082150029014765 10135985316405806260880537)
        ·
          refine ⟨7601988987304354695660403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10135985316405806260880537 7601988987304354695660403)
          ·
            refine ⟨11402983480956532043490605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7601988987304354695660403 11402983480956532043490605)
            ·
              refine ⟨4276118805358699516308977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11402983480956532043490605 4276118805358699516308977)
              ·
                refine ⟨3207089104019024637231733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4276118805358699516308977 3207089104019024637231733)
                ·
                  refine ⟨300664603501783559740475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3207089104019024637231733 300664603501783559740475)
                  ·
                    rfl

theorem cell22_2634940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_2634940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2634940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2634940 prefixEnd_2634940 := by exact prefixLift 2634940
  have htrace : WordTrace (prefixWord ++ tailWord_2634940) baseStart_2634940 baseEnd_2634940 := by
    simpa [prefixWord, tailWord_2634940, baseEnd_2634940] using wordTrace_append hprefix tailTrace_2634940
  have hstable : (prefixWord ++ tailWord_2634940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634940).length < 2 ^ (prefixWord ++ tailWord_2634940).sum := by decide
  have hdescent : baseEnd_2634940 < baseStart_2634940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635002 : List Nat := [3, 1, 1, 1, 1, 4, 5, 2, 4]
def baseStart_2635002 : Nat := 118140960795 + 2635002 * 2 ^ 59
def prefixEnd_2635002 : Nat := 4983230072969 + 3 ^ 40 * 2635002 * 2
def baseEnd_2635002 : Nat := 300671678124134394723745

theorem tailTrace_2635002 : CollatzResearch.WordTrace tailWord_2635002 prefixEnd_2635002 300671678124134394723745 := by
  unfold tailWord_2635002
  simp only [CollatzResearch.WordTrace]
  refine ⟨24026604599961312839646815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64070945599896834239058173 24026604599961312839646815)
  ·
    refine ⟨36039906899941969259470223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24026604599961312839646815 36039906899941969259470223)
    ·
      refine ⟨54059860349912953889205335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36039906899941969259470223 54059860349912953889205335)
      ·
        refine ⟨81089790524869430833808003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54059860349912953889205335 81089790524869430833808003)
        ·
          refine ⟨121634685787304146250712005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81089790524869430833808003 121634685787304146250712005)
          ·
            refine ⟨22806503585119527422008501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121634685787304146250712005 22806503585119527422008501)
            ·
              refine ⟨2138109711104955695813297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22806503585119527422008501 2138109711104955695813297)
              ·
                refine ⟨1603582283328716771859973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2138109711104955695813297 1603582283328716771859973)
                ·
                  refine ⟨300671678124134394723745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1603582283328716771859973 300671678124134394723745)
                  ·
                    rfl

theorem cell22_2635002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_2635002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635002 prefixEnd_2635002 := by exact prefixLift 2635002
  have htrace : WordTrace (prefixWord ++ tailWord_2635002) baseStart_2635002 baseEnd_2635002 := by
    simpa [prefixWord, tailWord_2635002, baseEnd_2635002] using wordTrace_append hprefix tailTrace_2635002
  have hstable : (prefixWord ++ tailWord_2635002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635002).length < 2 ^ (prefixWord ++ tailWord_2635002).sum := by decide
  have hdescent : baseEnd_2635002 < baseStart_2635002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635013 : List Nat := [1, 3, 1, 1, 2, 1, 6, 7]
def baseStart_2635013 : Nat := 118140960795 + 2635013 * 2 ^ 59
def prefixEnd_2635013 : Nat := 4983230072969 + 3 ^ 40 * 2635013 * 2
def baseEnd_2635013 : Nat := 100224311099689202460689

theorem tailTrace_2635013 : CollatzResearch.WordTrace tailWord_2635013 prefixEnd_2635013 100224311099689202460689 := by
  unfold tailWord_2635013
  simp only [CollatzResearch.WordTrace]
  refine ⟨96106819602805400237237693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64071213068536933491491795 96106819602805400237237693)
  ·
    refine ⟨36040057351052025088964135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96106819602805400237237693 36040057351052025088964135)
    ·
      refine ⟨54060086026578037633446203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36040057351052025088964135 54060086026578037633446203)
      ·
        refine ⟨81090129039867056450169305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54060086026578037633446203 81090129039867056450169305)
        ·
          refine ⟨60817596779900292337626979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81090129039867056450169305 60817596779900292337626979)
          ·
            refine ⟨91226395169850438506440469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60817596779900292337626979 91226395169850438506440469)
            ·
              refine ⟨4276237273586739304989397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91226395169850438506440469 4276237273586739304989397)
              ·
                refine ⟨100224311099689202460689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4276237273586739304989397 100224311099689202460689)
                ·
                  rfl

theorem cell22_2635013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 7].length) (baseStart_2635013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635013 prefixEnd_2635013 := by exact prefixLift 2635013
  have htrace : WordTrace (prefixWord ++ tailWord_2635013) baseStart_2635013 baseEnd_2635013 := by
    simpa [prefixWord, tailWord_2635013, baseEnd_2635013] using wordTrace_append hprefix tailTrace_2635013
  have hstable : (prefixWord ++ tailWord_2635013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635013).length < 2 ^ (prefixWord ++ tailWord_2635013).sum := by decide
  have hdescent : baseEnd_2635013 < baseStart_2635013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635060 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_2635060 : Nat := 118140960795 + 2635060 * 2 ^ 59
def prefixEnd_2635060 : Nat := 4983230072969 + 3 ^ 40 * 2635060 * 2
def baseEnd_2635060 : Nat := 902034888957710366221057

theorem tailTrace_2635060 : CollatzResearch.WordTrace tailWord_2635060 prefixEnd_2635060 902034888957710366221057 := by
  unfold tailWord_2635060
  simp only [CollatzResearch.WordTrace]
  refine ⟨48054266916817563632099317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64072355889090084842799089 48054266916817563632099317)
  ·
    refine ⟨4505087523451646590509311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48054266916817563632099317 4505087523451646590509311)
    ·
      refine ⟨6757631285177469885763967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4505087523451646590509311 6757631285177469885763967)
      ·
        refine ⟨10136446927766204828645951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6757631285177469885763967 10136446927766204828645951)
        ·
          refine ⟨15204670391649307242968927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10136446927766204828645951 15204670391649307242968927)
          ·
            refine ⟨22807005587473960864453391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15204670391649307242968927 22807005587473960864453391)
            ·
              refine ⟨34210508381210941296680087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22807005587473960864453391 34210508381210941296680087)
              ·
                refine ⟨51315762571816411945020131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34210508381210941296680087 51315762571816411945020131)
                ·
                  refine ⟨76973643857724617917530197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51315762571816411945020131 76973643857724617917530197)
                  ·
                    refine ⟨902034888957710366221057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76973643857724617917530197 902034888957710366221057)
                    ·
                      rfl

theorem cell22_2635060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_2635060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635060 prefixEnd_2635060 := by exact prefixLift 2635060
  have htrace : WordTrace (prefixWord ++ tailWord_2635060) baseStart_2635060 baseEnd_2635060 := by
    simpa [prefixWord, tailWord_2635060, baseEnd_2635060] using wordTrace_append hprefix tailTrace_2635060
  have hstable : (prefixWord ++ tailWord_2635060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635060).length < 2 ^ (prefixWord ++ tailWord_2635060).sum := by decide
  have hdescent : baseEnd_2635060 < baseStart_2635060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635103 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 10]
def baseStart_2635103 : Nat := 118140960795 + 2635103 * 2 ^ 59
def prefixEnd_2635103 : Nat := 4983230072969 + 3 ^ 40 * 2635103 * 2
def baseEnd_2635103 : Nat := 300683202912157529131975

theorem tailTrace_2635103 : CollatzResearch.WordTrace tailWord_2635103 prefixEnd_2635103 300683202912157529131975 := by
  unfold tailWord_2635103
  simp only [CollatzResearch.WordTrace]
  refine ⟨96110102172479345608013963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64073401448319563738675975 96110102172479345608013963)
  ·
    refine ⟨144165153258719018412020945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96110102172479345608013963 144165153258719018412020945)
    ·
      refine ⟨108123864944039263809015709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144165153258719018412020945 108123864944039263809015709)
      ·
        refine ⟨40546449354014723928380891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108123864944039263809015709 40546449354014723928380891)
        ·
          refine ⟨60819674031022085892571337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40546449354014723928380891 60819674031022085892571337)
          ·
            refine ⟨45614755523266564419428503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60819674031022085892571337 45614755523266564419428503)
            ·
              refine ⟨68422133284899846629142755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45614755523266564419428503 68422133284899846629142755)
              ·
                refine ⟨102633199927349769943714133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68422133284899846629142755 102633199927349769943714133)
                ·
                  refine ⟨300683202912157529131975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 102633199927349769943714133 300683202912157529131975)
                  ·
                    rfl

theorem cell22_2635103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 10].length) (baseStart_2635103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635103 prefixEnd_2635103 := by exact prefixLift 2635103
  have htrace : WordTrace (prefixWord ++ tailWord_2635103) baseStart_2635103 baseEnd_2635103 := by
    simpa [prefixWord, tailWord_2635103, baseEnd_2635103] using wordTrace_append hprefix tailTrace_2635103
  have hstable : (prefixWord ++ tailWord_2635103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635103).length < 2 ^ (prefixWord ++ tailWord_2635103).sum := by decide
  have hdescent : baseEnd_2635103 < baseStart_2635103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635120 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 6]
def baseStart_2635120 : Nat := 118140960795 + 2635120 * 2 ^ 59
def prefixEnd_2635120 : Nat := 4983230072969 + 3 ^ 40 * 2635120 * 2
def baseEnd_2635120 : Nat := 300685142727963403240291

theorem tailTrace_2635120 : CollatzResearch.WordTrace tailWord_2635120 prefixEnd_2635120 300685142727963403240291 := by
  unfold tailWord_2635120
  simp only [CollatzResearch.WordTrace]
  refine ⟨48055361106708878755691407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64073814808945171674255209 48055361106708878755691407)
  ·
    refine ⟨72083041660063318133537111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48055361106708878755691407 72083041660063318133537111)
    ·
      refine ⟨108124562490094977200305667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72083041660063318133537111 108124562490094977200305667)
      ·
        refine ⟨162186843735142465800458501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108124562490094977200305667 162186843735142465800458501)
        ·
          refine ⟨30410033200339212337585969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162186843735142465800458501 30410033200339212337585969)
          ·
            refine ⟨22807524900254409253189477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30410033200339212337585969 22807524900254409253189477)
            ·
              refine ⟨4276410918797701734973027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22807524900254409253189477 4276410918797701734973027)
              ·
                refine ⟨6414616378196552602459541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4276410918797701734973027 6414616378196552602459541)
                ·
                  refine ⟨300685142727963403240291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6414616378196552602459541 300685142727963403240291)
                  ·
                    rfl

theorem cell22_2635120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 6].length) (baseStart_2635120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635120 prefixEnd_2635120 := by exact prefixLift 2635120
  have htrace : WordTrace (prefixWord ++ tailWord_2635120) baseStart_2635120 baseEnd_2635120 := by
    simpa [prefixWord, tailWord_2635120, baseEnd_2635120] using wordTrace_append hprefix tailTrace_2635120
  have hstable : (prefixWord ++ tailWord_2635120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635120).length < 2 ^ (prefixWord ++ tailWord_2635120).sum := by decide
  have hdescent : baseEnd_2635120 < baseStart_2635120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635135 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 8, 3]
def baseStart_2635135 : Nat := 118140960795 + 2635135 * 2 ^ 59
def prefixEnd_2635135 : Nat := 4983230072969 + 3 ^ 40 * 2635135 * 2
def baseEnd_2635135 : Nat := 902060562990435170595827

theorem tailTrace_2635135 : CollatzResearch.WordTrace tailWord_2635135 prefixEnd_2635135 902060562990435170595827 := by
  unfold tailWord_2635135
  simp only [CollatzResearch.WordTrace]
  refine ⟨96111269308363415073178859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64074179538908943382119239 96111269308363415073178859)
  ·
    refine ⟨144166903962545122609768289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96111269308363415073178859 144166903962545122609768289)
    ·
      refine ⟨108125177971908841957326217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144166903962545122609768289 108125177971908841957326217)
      ·
        refine ⟨81093883478931631467994663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108125177971908841957326217 81093883478931631467994663)
        ·
          refine ⟨121640825218397447201991995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81093883478931631467994663 121640825218397447201991995)
          ·
            refine ⟨182461237827596170802987993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121640825218397447201991995 182461237827596170802987993)
            ·
              refine ⟨136845928370697128102240995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182461237827596170802987993 136845928370697128102240995)
              ·
                refine ⟨205268892556045692153361493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136845928370697128102240995 205268892556045692153361493)
                ·
                  refine ⟨2405494834641160454922205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 205268892556045692153361493 2405494834641160454922205)
                  ·
                    refine ⟨902060562990435170595827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2405494834641160454922205 902060562990435170595827)
                    ·
                      rfl

theorem cell22_2635135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 3].length) (baseStart_2635135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635135 prefixEnd_2635135 := by exact prefixLift 2635135
  have htrace : WordTrace (prefixWord ++ tailWord_2635135) baseStart_2635135 baseEnd_2635135 := by
    simpa [prefixWord, tailWord_2635135, baseEnd_2635135] using wordTrace_append hprefix tailTrace_2635135
  have hstable : (prefixWord ++ tailWord_2635135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635135).length < 2 ^ (prefixWord ++ tailWord_2635135).sum := by decide
  have hdescent : baseEnd_2635135 < baseStart_2635135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635165 : List Nat := [1, 4, 2, 1, 3, 1, 10]
def baseStart_2635165 : Nat := 118140960795 + 2635165 * 2 ^ 59
def prefixEnd_2635165 : Nat := 4983230072969 + 3 ^ 40 * 2635165 * 2
def baseEnd_2635165 : Nat := 33410030837167596012805

theorem tailTrace_2635165 : CollatzResearch.WordTrace tailWord_2635165 prefixEnd_2635165 33410030837167596012805 := by
  unfold tailWord_2635165
  simp only [CollatzResearch.WordTrace]
  refine ⟨96112363498254730196770949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64074908998836486797847299 96112363498254730196770949)
  ·
    refine ⟨18021068155922761911894553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96112363498254730196770949 18021068155922761911894553)
    ·
      refine ⟨13515801116942071433920915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18021068155922761911894553 13515801116942071433920915)
      ·
        refine ⟨20273701675413107150881373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13515801116942071433920915 20273701675413107150881373)
        ·
          refine ⟨7602638128279915181580515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20273701675413107150881373 7602638128279915181580515)
          ·
            refine ⟨11403957192419872772370773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7602638128279915181580515 11403957192419872772370773)
            ·
              refine ⟨33410030837167596012805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11403957192419872772370773 33410030837167596012805)
              ·
                rfl

theorem cell22_2635165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 10].length) (baseStart_2635165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635165 prefixEnd_2635165 := by exact prefixLift 2635165
  have htrace : WordTrace (prefixWord ++ tailWord_2635165) baseStart_2635165 baseEnd_2635165 := by
    simpa [prefixWord, tailWord_2635165, baseEnd_2635165] using wordTrace_append hprefix tailTrace_2635165
  have hstable : (prefixWord ++ tailWord_2635165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635165).length < 2 ^ (prefixWord ++ tailWord_2635165).sum := by decide
  have hdescent : baseEnd_2635165 < baseStart_2635165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635167 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 2, 4]
def baseStart_2635167 : Nat := 118140960795 + 2635167 * 2 ^ 59
def prefixEnd_2635167 : Nat := 4983230072969 + 3 ^ 40 * 2635167 * 2
def baseEnd_2635167 : Nat := 902071517244397753795729

theorem tailTrace_2635167 : CollatzResearch.WordTrace tailWord_2635167 prefixEnd_2635167 902071517244397753795729 := by
  unfold tailWord_2635167
  simp only [CollatzResearch.WordTrace]
  refine ⟨96112436444247484538343755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64074957629498323025562503 96112436444247484538343755)
  ·
    refine ⟨144168654666371226807515633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96112436444247484538343755 144168654666371226807515633)
    ·
      refine ⟨108126490999778420105636725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144168654666371226807515633 108126490999778420105636725)
      ·
        refine ⟨10136858531229226884903443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108126490999778420105636725 10136858531229226884903443)
        ·
          refine ⟨15205287796843840327355165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10136858531229226884903443 15205287796843840327355165)
          ·
            refine ⟨5701982923816440122758187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15205287796843840327355165 5701982923816440122758187)
            ·
              refine ⟨8552974385724660184137281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5701982923816440122758187 8552974385724660184137281)
              ·
                refine ⟨6414730789293495138102961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8552974385724660184137281 6414730789293495138102961)
                ·
                  refine ⟨4811048091970121353577221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6414730789293495138102961 4811048091970121353577221)
                  ·
                    refine ⟨902071517244397753795729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4811048091970121353577221 902071517244397753795729)
                    ·
                      rfl

theorem cell22_2635167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_2635167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635167 prefixEnd_2635167 := by exact prefixLift 2635167
  have htrace : WordTrace (prefixWord ++ tailWord_2635167) baseStart_2635167 baseEnd_2635167 := by
    simpa [prefixWord, tailWord_2635167, baseEnd_2635167] using wordTrace_append hprefix tailTrace_2635167
  have hstable : (prefixWord ++ tailWord_2635167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635167).length < 2 ^ (prefixWord ++ tailWord_2635167).sum := by decide
  have hdescent : baseEnd_2635167 < baseStart_2635167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635197 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 5, 3]
def baseStart_2635197 : Nat := 118140960795 + 2635197 * 2 ^ 59
def prefixEnd_2635197 : Nat := 4983230072969 + 3 ^ 40 * 2635197 * 2
def baseEnd_2635197 : Nat := 902081786857487675545637

theorem tailTrace_2635197 : CollatzResearch.WordTrace tailWord_2635197 prefixEnd_2635197 902081786857487675545637 := by
  unfold tailWord_2635197
  simp only [CollatzResearch.WordTrace]
  refine ⟨96113530634138799661935845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64075687089425866441290563 96113530634138799661935845)
  ·
    refine ⟨18021286993901024936612971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96113530634138799661935845 18021286993901024936612971)
    ·
      refine ⟨27031930490851537404919457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18021286993901024936612971 27031930490851537404919457)
      ·
        refine ⟨20273947868138653053689593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27031930490851537404919457 20273947868138653053689593)
        ·
          refine ⟨15205460901103989790267195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20273947868138653053689593 15205460901103989790267195)
          ·
            refine ⟨22808191351655984685400793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15205460901103989790267195 22808191351655984685400793)
            ·
              refine ⟨17106143513741988514050595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22808191351655984685400793 17106143513741988514050595)
              ·
                refine ⟨25659215270612982771075893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17106143513741988514050595 25659215270612982771075893)
                ·
                  refine ⟨2405551431619967134788365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25659215270612982771075893 2405551431619967134788365)
                  ·
                    refine ⟨902081786857487675545637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2405551431619967134788365 902081786857487675545637)
                    ·
                      rfl

theorem cell22_2635197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_2635197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635197 prefixEnd_2635197 := by exact prefixLift 2635197
  have htrace : WordTrace (prefixWord ++ tailWord_2635197) baseStart_2635197 baseEnd_2635197 := by
    simpa [prefixWord, tailWord_2635197, baseEnd_2635197] using wordTrace_append hprefix tailTrace_2635197
  have hstable : (prefixWord ++ tailWord_2635197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635197).length < 2 ^ (prefixWord ++ tailWord_2635197).sum := by decide
  have hdescent : baseEnd_2635197 < baseStart_2635197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635257 : List Nat := [1, 2, 1, 3, 1, 2, 1, 6, 1, 4]
def baseStart_2635257 : Nat := 118140960795 + 2635257 * 2 ^ 59
def prefixEnd_2635257 : Nat := 4983230072969 + 3 ^ 40 * 2635257 * 2
def baseEnd_2635257 : Nat := 902102326083667519045453

theorem tailTrace_2635257 : CollatzResearch.WordTrace tailWord_2635257 prefixEnd_2635257 902102326083667519045453 := by
  unfold tailWord_2635257
  simp only [CollatzResearch.WordTrace]
  refine ⟨96115719013921429909120025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64077146009280953272746683 96115719013921429909120025)
  ·
    refine ⟨72086789260441072431840019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96115719013921429909120025 72086789260441072431840019)
    ·
      refine ⟨108130183890661608647760029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72086789260441072431840019 108130183890661608647760029)
      ·
        refine ⟨40548818958998103242910011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108130183890661608647760029 40548818958998103242910011)
        ·
          refine ⟨60823228438497154864365017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40548818958998103242910011 60823228438497154864365017)
          ·
            refine ⟨45617421328872866148273763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60823228438497154864365017 45617421328872866148273763)
            ·
              refine ⟨68426131993309299222410645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45617421328872866148273763 68426131993309299222410645)
              ·
                refine ⟨3207474937186373401050499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68426131993309299222410645 3207474937186373401050499)
                ·
                  refine ⟨4811212405779560101575749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207474937186373401050499 4811212405779560101575749)
                  ·
                    refine ⟨902102326083667519045453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4811212405779560101575749 902102326083667519045453)
                    ·
                      rfl

theorem cell22_2635257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_2635257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635257 prefixEnd_2635257 := by exact prefixLift 2635257
  have htrace : WordTrace (prefixWord ++ tailWord_2635257) baseStart_2635257 baseEnd_2635257 := by
    simpa [prefixWord, tailWord_2635257, baseEnd_2635257] using wordTrace_append hprefix tailTrace_2635257
  have hstable : (prefixWord ++ tailWord_2635257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635257).length < 2 ^ (prefixWord ++ tailWord_2635257).sum := by decide
  have hdescent : baseEnd_2635257 < baseStart_2635257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635274 : List Nat := [3, 1, 2, 2, 2, 3, 1, 3, 1, 4]
def baseStart_2635274 : Nat := 118140960795 + 2635274 * 2 ^ 59
def prefixEnd_2635274 : Nat := 4983230072969 + 3 ^ 40 * 2635274 * 2
def baseEnd_2635274 : Nat := 902108145531085141370401

theorem tailTrace_2635274 : CollatzResearch.WordTrace tailWord_2635274 prefixEnd_2635274 902108145531085141370401 := by
  unfold tailWord_2635274
  simp only [CollatzResearch.WordTrace]
  refine ⟨24029084763714960453122219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64077559369906561208325917 24029084763714960453122219)
  ·
    refine ⟨36043627145572440679683329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24029084763714960453122219 36043627145572440679683329)
    ·
      refine ⟨27032720359179330509762497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36043627145572440679683329 27032720359179330509762497)
      ·
        refine ⟨20274540269384497882321873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27032720359179330509762497 20274540269384497882321873)
        ·
          refine ⟨15205905202038373411741405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20274540269384497882321873 15205905202038373411741405)
          ·
            refine ⟨5702214450764390029403027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15205905202038373411741405 5702214450764390029403027)
            ·
              refine ⟨8553321676146585044104541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5702214450764390029403027 8553321676146585044104541)
              ·
                refine ⟨3207495628554969391539203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8553321676146585044104541 3207495628554969391539203)
                ·
                  refine ⟨4811243442832454087308805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207495628554969391539203 4811243442832454087308805)
                  ·
                    refine ⟨902108145531085141370401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4811243442832454087308805 902108145531085141370401)
                    ·
                      rfl

theorem cell22_2635274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_2635274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635274 prefixEnd_2635274 := by exact prefixLift 2635274
  have htrace : WordTrace (prefixWord ++ tailWord_2635274) baseStart_2635274 baseEnd_2635274 := by
    simpa [prefixWord, tailWord_2635274, baseEnd_2635274] using wordTrace_append hprefix tailTrace_2635274
  have hstable : (prefixWord ++ tailWord_2635274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635274).length < 2 ^ (prefixWord ++ tailWord_2635274).sum := by decide
  have hdescent : baseEnd_2635274 < baseStart_2635274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635317 : List Nat := [1, 3, 3, 1, 1, 4, 1, 8]
def baseStart_2635317 : Nat := 118140960795 + 2635317 * 2 ^ 59
def prefixEnd_2635317 : Nat := 4983230072969 + 3 ^ 40 * 2635317 * 2
def baseEnd_2635317 : Nat := 100235873923316373616141

theorem tailTrace_2635317 : CollatzResearch.WordTrace tailWord_2635317 prefixEnd_2635317 100235873923316373616141 := by
  unfold tailWord_2635317
  simp only [CollatzResearch.WordTrace]
  refine ⟨96117907393704060156304205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64078604929136040104202803 96117907393704060156304205)
  ·
    refine ⟨36044215272639022558614077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96117907393704060156304205 36044215272639022558614077)
    ·
      refine ⟨13516580727239633459480279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36044215272639022558614077 13516580727239633459480279)
      ·
        refine ⟨20274871090859450189220419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13516580727239633459480279 20274871090859450189220419)
        ·
          refine ⟨30412306636289175283830629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20274871090859450189220419 30412306636289175283830629)
          ·
            refine ⟨5702307494304220365718243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30412306636289175283830629 5702307494304220365718243)
            ·
              refine ⟨8553461241456330548577365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5702307494304220365718243 8553461241456330548577365)
              ·
                refine ⟨100235873923316373616141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8553461241456330548577365 100235873923316373616141)
                ·
                  rfl

theorem cell22_2635317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 8].length) (baseStart_2635317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635317 prefixEnd_2635317 := by exact prefixLift 2635317
  have htrace : WordTrace (prefixWord ++ tailWord_2635317) baseStart_2635317 baseEnd_2635317 := by
    simpa [prefixWord, tailWord_2635317, baseEnd_2635317] using wordTrace_append hprefix tailTrace_2635317
  have hstable : (prefixWord ++ tailWord_2635317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635317).length < 2 ^ (prefixWord ++ tailWord_2635317).sum := by decide
  have hdescent : baseEnd_2635317 < baseStart_2635317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635396 : List Nat := [2, 3, 2, 1, 4, 1, 2, 2, 5]
def baseStart_2635396 : Nat := 118140960795 + 2635396 * 2 ^ 59
def prefixEnd_2635396 : Nat := 4983230072969 + 3 ^ 40 * 2635396 * 2
def baseEnd_2635396 : Nat := 300716636208105829940009

theorem tailTrace_2635396 : CollatzResearch.WordTrace tailWord_2635396 prefixEnd_2635396 300716636208105829940009 := by
  unfold tailWord_2635396
  simp only [CollatzResearch.WordTrace]
  refine ⟨48060394380208928324215021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64080525840278571098953361 48060394380208928324215021)
  ·
    refine ⟨18022647892578348121580633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48060394380208928324215021 18022647892578348121580633)
    ·
      refine ⟨13516985919433761091185475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18022647892578348121580633 13516985919433761091185475)
      ·
        refine ⟨20275478879150641636778213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13516985919433761091185475 20275478879150641636778213)
        ·
          refine ⟨3801652289840745306895915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20275478879150641636778213 3801652289840745306895915)
          ·
            refine ⟨5702478434761117960343873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3801652289840745306895915 5702478434761117960343873)
            ·
              refine ⟨4276858826070838470257905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5702478434761117960343873 4276858826070838470257905)
              ·
                refine ⟨3207644119553128852693429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4276858826070838470257905 3207644119553128852693429)
                ·
                  refine ⟨300716636208105829940009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3207644119553128852693429 300716636208105829940009)
                  ·
                    rfl

theorem cell22_2635396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_2635396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635396 prefixEnd_2635396 := by exact prefixLift 2635396
  have htrace : WordTrace (prefixWord ++ tailWord_2635396) baseStart_2635396 baseEnd_2635396 := by
    simpa [prefixWord, tailWord_2635396, baseEnd_2635396] using wordTrace_append hprefix tailTrace_2635396
  have hstable : (prefixWord ++ tailWord_2635396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635396).length < 2 ^ (prefixWord ++ tailWord_2635396).sum := by decide
  have hdescent : baseEnd_2635396 < baseStart_2635396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635400 : List Nat := [2, 1, 3, 5, 1, 1, 1, 4, 1, 3]
def baseStart_2635400 : Nat := 118140960795 + 2635400 * 2 ^ 59
def prefixEnd_2635400 : Nat := 4983230072969 + 3 ^ 40 * 2635400 * 2
def baseEnd_2635400 : Nat := 902151277906062812720015

theorem tailTrace_2635400 : CollatzResearch.WordTrace tailWord_2635400 prefixEnd_2635400 902151277906062812720015 := by
  unfold tailWord_2635400
  simp only [CollatzResearch.WordTrace]
  refine ⟨48060467326201682665787827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64080623101602243554383769 48060467326201682665787827)
  ·
    refine ⟨72090700989302523998681741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48060467326201682665787827 72090700989302523998681741)
    ·
      refine ⟨27034012870988446499505653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72090700989302523998681741 27034012870988446499505653)
      ·
        refine ⟨2534438706655166859328655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27034012870988446499505653 2534438706655166859328655)
        ·
          refine ⟨3801658059982750288992983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2534438706655166859328655 3801658059982750288992983)
          ·
            refine ⟨5702487089974125433489475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3801658059982750288992983 5702487089974125433489475)
            ·
              refine ⟨8553730634961188150234213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5702487089974125433489475 8553730634961188150234213)
              ·
                refine ⟨1603824494055222778168915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8553730634961188150234213 1603824494055222778168915)
                ·
                  refine ⟨2405736741082834167253373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603824494055222778168915 2405736741082834167253373)
                  ·
                    refine ⟨902151277906062812720015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2405736741082834167253373 902151277906062812720015)
                    ·
                      rfl

theorem cell22_2635400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_2635400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635400 prefixEnd_2635400 := by exact prefixLift 2635400
  have htrace : WordTrace (prefixWord ++ tailWord_2635400) baseStart_2635400 baseEnd_2635400 := by
    simpa [prefixWord, tailWord_2635400, baseEnd_2635400] using wordTrace_append hprefix tailTrace_2635400
  have hstable : (prefixWord ++ tailWord_2635400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635400).length < 2 ^ (prefixWord ++ tailWord_2635400).sum := by decide
  have hdescent : baseEnd_2635400 < baseStart_2635400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635424 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 6]
def baseStart_2635424 : Nat := 118140960795 + 2635424 * 2 ^ 59
def prefixEnd_2635424 : Nat := 4983230072969 + 3 ^ 40 * 2635424 * 2
def baseEnd_2635424 : Nat := 300719831198844916706647

theorem tailTrace_2635424 : CollatzResearch.WordTrace tailWord_2635424 prefixEnd_2635424 300719831198844916706647 := by
  unfold tailWord_2635424
  simp only [CollatzResearch.WordTrace]
  refine ⟨48060905002158208715224663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64081206669544278286966217 48060905002158208715224663)
  ·
    refine ⟨72091357503237313072836995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48060905002158208715224663 72091357503237313072836995)
    ·
      refine ⟨108137036254855969609255493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72091357503237313072836995 108137036254855969609255493)
      ·
        refine ⟨20275694297785494301735405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108137036254855969609255493 20275694297785494301735405)
        ·
          refine ⟨7603385361669560363150777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20275694297785494301735405 7603385361669560363150777)
          ·
            refine ⟨5702539021252170272363083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7603385361669560363150777 5702539021252170272363083)
            ·
              refine ⟨8553808531878255408544625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5702539021252170272363083 8553808531878255408544625)
              ·
                refine ⟨6415356398908691556408469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8553808531878255408544625 6415356398908691556408469)
                ·
                  refine ⟨300719831198844916706647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6415356398908691556408469 300719831198844916706647)
                  ·
                    rfl

theorem cell22_2635424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 6].length) (baseStart_2635424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635424 prefixEnd_2635424 := by exact prefixLift 2635424
  have htrace : WordTrace (prefixWord ++ tailWord_2635424) baseStart_2635424 baseEnd_2635424 := by
    simpa [prefixWord, tailWord_2635424, baseEnd_2635424] using wordTrace_append hprefix tailTrace_2635424
  have hstable : (prefixWord ++ tailWord_2635424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635424).length < 2 ^ (prefixWord ++ tailWord_2635424).sum := by decide
  have hdescent : baseEnd_2635424 < baseStart_2635424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635439 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 4, 3]
def baseStart_2635439 : Nat := 118140960795 + 2635439 * 2 ^ 59
def prefixEnd_2635439 : Nat := 4983230072969 + 3 ^ 40 * 2635439 * 2
def baseEnd_2635439 : Nat := 902164628403079710994895

theorem tailTrace_2635439 : CollatzResearch.WordTrace tailWord_2635439 prefixEnd_2635439 902164628403079710994895 := by
  unfold tailWord_2635439
  simp only [CollatzResearch.WordTrace]
  refine ⟨96122357099262074992245371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64081571399508049994830247 96122357099262074992245371)
  ·
    refine ⟨144183535648893112488368057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96122357099262074992245371 144183535648893112488368057)
    ·
      refine ⟨108137651736669834366276043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144183535648893112488368057 108137651736669834366276043)
      ·
        refine ⟨162206477605004751549414065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108137651736669834366276043 162206477605004751549414065)
        ·
          refine ⟨121654858203753563662060549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162206477605004751549414065 121654858203753563662060549)
          ·
            refine ⟨22810285913203793186636353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121654858203753563662060549 22810285913203793186636353)
            ·
              refine ⟨17107714434902844889977265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22810285913203793186636353 17107714434902844889977265)
              ·
                refine ⟨12830785826177133667482949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17107714434902844889977265 12830785826177133667482949)
                ·
                  refine ⟨2405772342408212562653053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12830785826177133667482949 2405772342408212562653053)
                  ·
                    refine ⟨902164628403079710994895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2405772342408212562653053 902164628403079710994895)
                    ·
                      rfl

theorem cell22_2635439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 3].length) (baseStart_2635439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635439 prefixEnd_2635439 := by exact prefixLift 2635439
  have htrace : WordTrace (prefixWord ++ tailWord_2635439) baseStart_2635439 baseEnd_2635439 := by
    simpa [prefixWord, tailWord_2635439, baseEnd_2635439] using wordTrace_append hprefix tailTrace_2635439
  have hstable : (prefixWord ++ tailWord_2635439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635439).length < 2 ^ (prefixWord ++ tailWord_2635439).sum := by decide
  have hdescent : baseEnd_2635439 < baseStart_2635439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635473 : List Nat := [1, 2, 2, 1, 2, 5, 3, 1, 2, 3]
def baseStart_2635473 : Nat := 118140960795 + 2635473 * 2 ^ 59
def prefixEnd_2635473 : Nat := 4983230072969 + 3 ^ 40 * 2635473 * 2
def baseEnd_2635473 : Nat := 902176267297914955644791

theorem tailTrace_2635473 : CollatzResearch.WordTrace tailWord_2635473 prefixEnd_2635473 902176267297914955644791 := by
  unfold tailWord_2635473
  simp only [CollatzResearch.WordTrace]
  refine ⟨96123597181138898798983073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64082398120759265865988715 96123597181138898798983073)
  ·
    refine ⟨72092697885854174099237305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96123597181138898798983073 72092697885854174099237305)
    ·
      refine ⟨54069523414390630574427979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72092697885854174099237305 54069523414390630574427979)
      ·
        refine ⟨81104285121585945861641969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54069523414390630574427979 81104285121585945861641969)
        ·
          refine ⟨60828213841189459396231477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81104285121585945861641969 60828213841189459396231477)
          ·
            refine ⟨5702645047611511818396701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60828213841189459396231477 5702645047611511818396701)
            ·
              refine ⟨2138491892854316931898763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5702645047611511818396701 2138491892854316931898763)
              ·
                refine ⟨3207737839281475397848145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138491892854316931898763 3207737839281475397848145)
                ·
                  refine ⟨2405803379461106548386109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3207737839281475397848145 2405803379461106548386109)
                  ·
                    refine ⟨902176267297914955644791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2405803379461106548386109 902176267297914955644791)
                    ·
                      rfl

theorem cell22_2635473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_2635473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635473 prefixEnd_2635473 := by exact prefixLift 2635473
  have htrace : WordTrace (prefixWord ++ tailWord_2635473) baseStart_2635473 baseEnd_2635473 := by
    simpa [prefixWord, tailWord_2635473, baseEnd_2635473] using wordTrace_append hprefix tailTrace_2635473
  have hstable : (prefixWord ++ tailWord_2635473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635473).length < 2 ^ (prefixWord ++ tailWord_2635473).sum := by decide
  have hdescent : baseEnd_2635473 < baseStart_2635473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635514 : List Nat := [3, 1, 1, 1, 1, 3, 1, 6, 5]
def baseStart_2635514 : Nat := 118140960795 + 2635514 * 2 ^ 59
def prefixEnd_2635514 : Nat := 4983230072969 + 3 ^ 40 * 2635514 * 2
def baseEnd_2635514 : Nat := 300730100811934838456555

theorem tailTrace_2635514 : CollatzResearch.WordTrace tailWord_2635514 prefixEnd_2635514 300730100811934838456555 := by
  unfold tailWord_2635514
  simp only [CollatzResearch.WordTrace]
  refine ⟨24031273143497590700306399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64083395049326908534150397 24031273143497590700306399)
  ·
    refine ⟨36046909715246386050459599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24031273143497590700306399 36046909715246386050459599)
    ·
      refine ⟨54070364572869579075689399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36046909715246386050459599 54070364572869579075689399)
      ·
        refine ⟨81105546859304368613534099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54070364572869579075689399 81105546859304368613534099)
        ·
          refine ⟨121658320288956552920301149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81105546859304368613534099 121658320288956552920301149)
          ·
            refine ⟨45621870108358707345112931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121658320288956552920301149 45621870108358707345112931)
            ·
              refine ⟨68432805162538061017669397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45621870108358707345112931 68432805162538061017669397)
              ·
                refine ⟨3207787741993971610203253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68432805162538061017669397 3207787741993971610203253)
                ·
                  refine ⟨300730100811934838456555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3207787741993971610203253 300730100811934838456555)
                  ·
                    rfl

theorem cell22_2635514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_2635514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635514 prefixEnd_2635514 := by exact prefixLift 2635514
  have htrace : WordTrace (prefixWord ++ tailWord_2635514) baseStart_2635514 baseEnd_2635514 := by
    simpa [prefixWord, tailWord_2635514, baseEnd_2635514] using wordTrace_append hprefix tailTrace_2635514
  have hstable : (prefixWord ++ tailWord_2635514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635514).length < 2 ^ (prefixWord ++ tailWord_2635514).sum := by decide
  have hdescent : baseEnd_2635514 < baseStart_2635514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635531 : List Nat := [1, 1, 1, 1, 5, 1, 6, 1, 5]
def baseStart_2635531 : Nat := 118140960795 + 2635531 * 2 ^ 59
def prefixEnd_2635531 : Nat := 4983230072969 + 3 ^ 40 * 2635531 * 2
def baseEnd_2635531 : Nat := 300732040627740712564871

theorem tailTrace_2635531 : CollatzResearch.WordTrace tailWord_2635531 prefixEnd_2635531 300732040627740712564871 := by
  unfold tailWord_2635531
  simp only [CollatzResearch.WordTrace]
  refine ⟨96125712614928774704594447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64083808409952516469729631 96125712614928774704594447)
  ·
    refine ⟨144188568922393162056891671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96125712614928774704594447 144188568922393162056891671)
    ·
      refine ⟨216282853383589743085337507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144188568922393162056891671 216282853383589743085337507)
      ·
        refine ⟨324424280075384614628006261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216282853383589743085337507 324424280075384614628006261)
        ·
          refine ⟨30414776257067307621375587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 324424280075384614628006261 30414776257067307621375587)
          ·
            refine ⟨45622164385600961432063381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30414776257067307621375587 45622164385600961432063381)
            ·
              refine ⟨2138538955575045067127971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45622164385600961432063381 2138538955575045067127971)
              ·
                refine ⟨3207808433362567600691957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138538955575045067127971 3207808433362567600691957)
                ·
                  refine ⟨300732040627740712564871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3207808433362567600691957 300732040627740712564871)
                  ·
                    rfl

theorem cell22_2635531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 5].length) (baseStart_2635531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635531 prefixEnd_2635531 := by exact prefixLift 2635531
  have htrace : WordTrace (prefixWord ++ tailWord_2635531) baseStart_2635531 baseEnd_2635531 := by
    simpa [prefixWord, tailWord_2635531, baseEnd_2635531] using wordTrace_append hprefix tailTrace_2635531
  have hstable : (prefixWord ++ tailWord_2635531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635531).length < 2 ^ (prefixWord ++ tailWord_2635531).sum := by decide
  have hdescent : baseEnd_2635531 < baseStart_2635531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635589 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_2635589 : Nat := 118140960795 + 2635589 * 2 ^ 59
def prefixEnd_2635589 : Nat := 4983230072969 + 3 ^ 40 * 2635589 * 2
def baseEnd_2635589 : Nat := 902215976468529319744435

theorem tailTrace_2635589 : CollatzResearch.WordTrace tailWord_2635589 prefixEnd_2635589 902215976468529319744435 := by
  unfold tailWord_2635589
  simp only [CollatzResearch.WordTrace]
  refine ⟨96127828048718650610205821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64085218699145767073470547 96127828048718650610205821)
  ·
    refine ⟨36047935518269493978827183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96127828048718650610205821 36047935518269493978827183)
    ·
      refine ⟨54071903277404240968240775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36047935518269493978827183 54071903277404240968240775)
      ·
        refine ⟨81107854916106361452361163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54071903277404240968240775 81107854916106361452361163)
        ·
          refine ⟨121661782374159542178541745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81107854916106361452361163 121661782374159542178541745)
          ·
            refine ⟨91246336780619656633906309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121661782374159542178541745 91246336780619656633906309)
            ·
              refine ⟨17108688146366185618857433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91246336780619656633906309 17108688146366185618857433)
              ·
                refine ⟨12831516109774639214143075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17108688146366185618857433 12831516109774639214143075)
                ·
                  refine ⟨19247274164661958821214613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12831516109774639214143075 19247274164661958821214613)
                  ·
                    refine ⟨902215976468529319744435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19247274164661958821214613 902215976468529319744435)
                    ·
                      rfl

theorem cell22_2635589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_2635589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635589 prefixEnd_2635589 := by exact prefixLift 2635589
  have htrace : WordTrace (prefixWord ++ tailWord_2635589) baseStart_2635589 baseEnd_2635589 := by
    simpa [prefixWord, tailWord_2635589, baseEnd_2635589] using wordTrace_append hprefix tailTrace_2635589
  have hstable : (prefixWord ++ tailWord_2635589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635589).length < 2 ^ (prefixWord ++ tailWord_2635589).sum := by decide
  have hdescent : baseEnd_2635589 < baseStart_2635589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635612 : List Nat := [2, 2, 4, 2, 2, 2, 2, 1, 1, 4]
def baseStart_2635612 : Nat := 118140960795 + 2635612 * 2 ^ 59
def prefixEnd_2635612 : Nat := 4983230072969 + 3 ^ 40 * 2635612 * 2
def baseEnd_2635612 : Nat := 902223849838564926419365

theorem tailTrace_2635612 : CollatzResearch.WordTrace tailWord_2635612 prefixEnd_2635612 902223849838564926419365 := by
  unfold tailWord_2635612
  simp only [CollatzResearch.WordTrace]
  refine ⟨48064333463817662769146545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64085777951756883692195393 48064333463817662769146545)
  ·
    refine ⟨36048250097863247076859909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48064333463817662769146545 36048250097863247076859909)
    ·
      refine ⟨6759046893349358826911233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36048250097863247076859909 6759046893349358826911233)
      ·
        refine ⟨5069285170012019120183425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6759046893349358826911233 5069285170012019120183425)
        ·
          refine ⟨3801963877509014340137569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5069285170012019120183425 3801963877509014340137569)
          ·
            refine ⟨2851472908131760755103177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3801963877509014340137569 2851472908131760755103177)
            ·
              refine ⟨2138604681098820566327383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2851472908131760755103177 2138604681098820566327383)
              ·
                refine ⟨3207907021648230849491075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138604681098820566327383 3207907021648230849491075)
                ·
                  refine ⟨4811860532472346274236613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207907021648230849491075 4811860532472346274236613)
                  ·
                    refine ⟨902223849838564926419365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4811860532472346274236613 902223849838564926419365)
                    ·
                      rfl

theorem cell22_2635612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_2635612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635612 prefixEnd_2635612 := by exact prefixLift 2635612
  have htrace : WordTrace (prefixWord ++ tailWord_2635612) baseStart_2635612 baseEnd_2635612 := by
    simpa [prefixWord, tailWord_2635612, baseEnd_2635612] using wordTrace_append hprefix tailTrace_2635612
  have hstable : (prefixWord ++ tailWord_2635612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635612).length < 2 ^ (prefixWord ++ tailWord_2635612).sum := by decide
  have hdescent : baseEnd_2635612 < baseStart_2635612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635655 : List Nat := [1, 1, 4, 2, 5, 1, 2, 6]
def baseStart_2635655 : Nat := 118140960795 + 2635655 * 2 ^ 59
def prefixEnd_2635655 : Nat := 4983230072969 + 3 ^ 40 * 2635655 * 2
def baseEnd_2635655 : Nat := 100248729957480794177137

theorem tailTrace_2635655 : CollatzResearch.WordTrace tailWord_2635655 prefixEnd_2635655 100248729957480794177137 := by
  unfold tailWord_2635655
  simp only [CollatzResearch.WordTrace]
  refine ⟨96130235266479543882108419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64086823510986362588072279 96130235266479543882108419)
  ·
    refine ⟨144195352899719315823162629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96130235266479543882108419 144195352899719315823162629)
    ·
      refine ⟨27036628668697371716842993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144195352899719315823162629 27036628668697371716842993)
      ·
        refine ⟨20277471501523028787632245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27036628668697371716842993 20277471501523028787632245)
        ·
          refine ⟨1901012953267783948840523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20277471501523028787632245 1901012953267783948840523)
          ·
            refine ⟨2851519429901675923260785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1901012953267783948840523 2851519429901675923260785)
            ·
              refine ⟨2138639572426256942445589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2851519429901675923260785 2138639572426256942445589)
              ·
                refine ⟨100248729957480794177137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2138639572426256942445589 100248729957480794177137)
                ·
                  rfl

theorem cell22_2635655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 6].length) (baseStart_2635655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635655 prefixEnd_2635655 := by exact prefixLift 2635655
  have htrace : WordTrace (prefixWord ++ tailWord_2635655) baseStart_2635655 baseEnd_2635655 := by
    simpa [prefixWord, tailWord_2635655, baseEnd_2635655] using wordTrace_append hprefix tailTrace_2635655
  have hstable : (prefixWord ++ tailWord_2635655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635655).length < 2 ^ (prefixWord ++ tailWord_2635655).sum := by decide
  have hdescent : baseEnd_2635655 < baseStart_2635655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635664 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 3, 7]
def baseStart_2635664 : Nat := 118140960795 + 2635664 * 2 ^ 59
def prefixEnd_2635664 : Nat := 4983230072969 + 3 ^ 40 * 2635664 * 2
def baseEnd_2635664 : Nat := 902241650501254124119205

theorem tailTrace_2635664 : CollatzResearch.WordTrace tailWord_2635664 prefixEnd_2635664 902241650501254124119205 := by
  unfold tailWord_2635664
  simp only [CollatzResearch.WordTrace]
  refine ⟨48065281761723469209593023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64087042348964625612790697 48065281761723469209593023)
  ·
    refine ⟨72097922642585203814389535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48065281761723469209593023 72097922642585203814389535)
    ·
      refine ⟨108146883963877805721584303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72097922642585203814389535 108146883963877805721584303)
      ·
        refine ⟨162220325945816708582376455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108146883963877805721584303 162220325945816708582376455)
        ·
          refine ⟨243330488918725062873564683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162220325945816708582376455 243330488918725062873564683)
          ·
            refine ⟨364995733378087594310347025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243330488918725062873564683 364995733378087594310347025)
            ·
              refine ⟨273746800033565695732760269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364995733378087594310347025 273746800033565695732760269)
              ·
                refine ⟨102655050012587135899785101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 273746800033565695732760269 102655050012587135899785101)
                ·
                  refine ⟨38495643754720175962419413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102655050012587135899785101 38495643754720175962419413)
                  ·
                    refine ⟨902241650501254124119205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38495643754720175962419413 902241650501254124119205)
                    ·
                      rfl

theorem cell22_2635664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_2635664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635664 prefixEnd_2635664 := by exact prefixLift 2635664
  have htrace : WordTrace (prefixWord ++ tailWord_2635664) baseStart_2635664 baseEnd_2635664 := by
    simpa [prefixWord, tailWord_2635664, baseEnd_2635664] using wordTrace_append hprefix tailTrace_2635664
  have hstable : (prefixWord ++ tailWord_2635664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635664).length < 2 ^ (prefixWord ++ tailWord_2635664).sum := by decide
  have hdescent : baseEnd_2635664 < baseStart_2635664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635745 : List Nat := [1, 2, 3, 1, 2, 1, 6, 2, 4]
def baseStart_2635745 : Nat := 118140960795 + 2635745 * 2 ^ 59
def prefixEnd_2635745 : Nat := 4983230072969 + 3 ^ 40 * 2635745 * 2
def baseEnd_2635745 : Nat := 300756459485532304281319

theorem tailTrace_2635745 : CollatzResearch.WordTrace tailWord_2635745 prefixEnd_2635745 300756459485532304281319 := by
  unfold tailWord_2635745
  simp only [CollatzResearch.WordTrace]
  refine ⟨96133517836153489252884689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64089011890768992835256459 96133517836153489252884689)
  ·
    refine ⟨72100138377115116939663517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96133517836153489252884689 72100138377115116939663517)
    ·
      refine ⟨27037551891418168852373819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72100138377115116939663517 27037551891418168852373819)
      ·
        refine ⟨40556327837127253278560729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27037551891418168852373819 40556327837127253278560729)
        ·
          refine ⟨30417245877845439958920547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40556327837127253278560729 30417245877845439958920547)
          ·
            refine ⟨45625868816768159938380821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30417245877845439958920547 45625868816768159938380821)
            ·
              refine ⟨2138712600786007497111601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45625868816768159938380821 2138712600786007497111601)
              ·
                refine ⟨1604034450589505622833701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2138712600786007497111601 1604034450589505622833701)
                ·
                  refine ⟨300756459485532304281319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1604034450589505622833701 300756459485532304281319)
                  ·
                    rfl

theorem cell22_2635745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 4].length) (baseStart_2635745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635745 prefixEnd_2635745 := by exact prefixLift 2635745
  have htrace : WordTrace (prefixWord ++ tailWord_2635745) baseStart_2635745 baseEnd_2635745 := by
    simpa [prefixWord, tailWord_2635745, baseEnd_2635745] using wordTrace_append hprefix tailTrace_2635745
  have hstable : (prefixWord ++ tailWord_2635745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635745).length < 2 ^ (prefixWord ++ tailWord_2635745).sum := by decide
  have hdescent : baseEnd_2635745 < baseStart_2635745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635788 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 5, 3]
def baseStart_2635788 : Nat := 118140960795 + 2635788 * 2 ^ 59
def prefixEnd_2635788 : Nat := 4983230072969 + 3 ^ 40 * 2635788 * 2
def baseEnd_2635788 : Nat := 902284098235359134018825

theorem tailTrace_2635788 : CollatzResearch.WordTrace tailWord_2635788 prefixEnd_2635788 902284098235359134018825 := by
  unfold tailWord_2635788
  simp only [CollatzResearch.WordTrace]
  refine ⟨48067543087498853798350009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64090057449998471731133345 48067543087498853798350009)
  ·
    refine ⟨36050657315624140348762507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48067543087498853798350009 36050657315624140348762507)
    ·
      refine ⟨54075985973436210523143761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36050657315624140348762507 54075985973436210523143761)
      ·
        refine ⟨40556989480077157892357821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54075985973436210523143761 40556989480077157892357821)
        ·
          refine ⟨15208871055028934209634183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40556989480077157892357821 15208871055028934209634183)
          ·
            refine ⟨22813306582543401314451275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15208871055028934209634183 22813306582543401314451275)
            ·
              refine ⟨34219959873815101971676913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22813306582543401314451275 34219959873815101971676913)
              ·
                refine ⟨25664969905361326478757685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34219959873815101971676913 25664969905361326478757685)
                ·
                  refine ⟨2406090928627624357383533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25664969905361326478757685 2406090928627624357383533)
                  ·
                    refine ⟨902284098235359134018825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2406090928627624357383533 902284098235359134018825)
                    ·
                      rfl

theorem cell22_2635788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_2635788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635788 prefixEnd_2635788 := by exact prefixLift 2635788
  have htrace : WordTrace (prefixWord ++ tailWord_2635788) baseStart_2635788 baseEnd_2635788 := by
    simpa [prefixWord, tailWord_2635788, baseEnd_2635788] using wordTrace_append hprefix tailTrace_2635788
  have hstable : (prefixWord ++ tailWord_2635788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635788).length < 2 ^ (prefixWord ++ tailWord_2635788).sum := by decide
  have hdescent : baseEnd_2635788 < baseStart_2635788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635805 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 3, 3]
def baseStart_2635805 : Nat := 118140960795 + 2635805 * 2 ^ 59
def prefixEnd_2635805 : Nat := 4983230072969 + 3 ^ 40 * 2635805 * 2
def baseEnd_2635805 : Nat := 902289917682776756343773

theorem tailTrace_2635805 : CollatzResearch.WordTrace tailWord_2635805 prefixEnd_2635805 902289917682776756343773 := by
  unfold tailWord_2635805
  simp only [CollatzResearch.WordTrace]
  refine ⟨96135706215936119500068869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64090470810624079666712579 96135706215936119500068869)
  ·
    refine ⟨18025444915488022406262913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96135706215936119500068869 18025444915488022406262913)
    ·
      refine ⟨13519083686616016804697185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18025444915488022406262913 13519083686616016804697185)
      ·
        refine ⟨10139312764962012603522889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13519083686616016804697185 10139312764962012603522889)
        ·
          refine ⟨7604484573721509452642167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10139312764962012603522889 7604484573721509452642167)
          ·
            refine ⟨11406726860582264178963251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7604484573721509452642167 11406726860582264178963251)
            ·
              refine ⟨17110090290873396268444877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11406726860582264178963251 17110090290873396268444877)
              ·
                refine ⟨6416283859077523600666829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17110090290873396268444877 6416283859077523600666829)
                ·
                  refine ⟨2406106447154071350250061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6416283859077523600666829 2406106447154071350250061)
                  ·
                    refine ⟨902289917682776756343773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2406106447154071350250061 902289917682776756343773)
                    ·
                      rfl

theorem cell22_2635805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_2635805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635805 prefixEnd_2635805 := by exact prefixLift 2635805
  have htrace : WordTrace (prefixWord ++ tailWord_2635805) baseStart_2635805 baseEnd_2635805 := by
    simpa [prefixWord, tailWord_2635805, baseEnd_2635805] using wordTrace_append hprefix tailTrace_2635805
  have hstable : (prefixWord ++ tailWord_2635805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635805).length < 2 ^ (prefixWord ++ tailWord_2635805).sum := by decide
  have hdescent : baseEnd_2635805 < baseStart_2635805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635863 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 6]
def baseStart_2635863 : Nat := 118140960795 + 2635863 * 2 ^ 59
def prefixEnd_2635863 : Nat := 4983230072969 + 3 ^ 40 * 2635863 * 2
def baseEnd_2635863 : Nat := 300769924089361312797865

theorem tailTrace_2635863 : CollatzResearch.WordTrace tailWord_2635863 prefixEnd_2635863 300769924089361312797865 := by
  unfold tailWord_2635863
  simp only [CollatzResearch.WordTrace]
  refine ⟨96137821649725995405680243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64091881099817330270453495 96137821649725995405680243)
  ·
    refine ⟨144206732474588993108520365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96137821649725995405680243 144206732474588993108520365)
    ·
      refine ⟨54077524677970872415695137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144206732474588993108520365 54077524677970872415695137)
      ·
        refine ⟨40558143508478154311771353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54077524677970872415695137 40558143508478154311771353)
        ·
          refine ⟨30418607631358615733828515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40558143508478154311771353 30418607631358615733828515)
          ·
            refine ⟨45627911447037923600742773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30418607631358615733828515 45627911447037923600742773)
            ·
              refine ⟨4277616698159805337569635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45627911447037923600742773 4277616698159805337569635)
              ·
                refine ⟨6416425047239708006354453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4277616698159805337569635 6416425047239708006354453)
                ·
                  refine ⟨300769924089361312797865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6416425047239708006354453 300769924089361312797865)
                  ·
                    rfl

theorem cell22_2635863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 6].length) (baseStart_2635863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635863 prefixEnd_2635863 := by exact prefixLift 2635863
  have htrace : WordTrace (prefixWord ++ tailWord_2635863) baseStart_2635863 baseEnd_2635863 := by
    simpa [prefixWord, tailWord_2635863, baseEnd_2635863] using wordTrace_append hprefix tailTrace_2635863
  have hstable : (prefixWord ++ tailWord_2635863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635863).length < 2 ^ (prefixWord ++ tailWord_2635863).sum := by decide
  have hdescent : baseEnd_2635863 < baseStart_2635863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635869 : List Nat := [1, 4, 4, 1, 1, 3, 2, 1, 5]
def baseStart_2635869 : Nat := 118140960795 + 2635869 * 2 ^ 59
def prefixEnd_2635869 : Nat := 4983230072969 + 3 ^ 40 * 2635869 * 2
def baseEnd_2635869 : Nat := 300770608730233974247859

theorem tailTrace_2635869 : CollatzResearch.WordTrace tailWord_2635869 prefixEnd_2635869 300770608730233974247859 := by
  unfold tailWord_2635869
  simp only [CollatzResearch.WordTrace]
  refine ⟨96138040487704258430398661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64092026991802838953599107 96138040487704258430398661)
  ·
    refine ⟨18025882591444548455699749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96138040487704258430398661 18025882591444548455699749)
    ·
      refine ⟨3379852985895852835443703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18025882591444548455699749 3379852985895852835443703)
      ·
        refine ⟨5069779478843779253165555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3379852985895852835443703 5069779478843779253165555)
        ·
          refine ⟨7604669218265668879748333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5069779478843779253165555 7604669218265668879748333)
          ·
            refine ⟨2851750956849625829905625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7604669218265668879748333 2851750956849625829905625)
            ·
              refine ⟨2138813217637219372429219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2851750956849625829905625 2138813217637219372429219)
              ·
                refine ⟨3208219826455829058643829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138813217637219372429219 3208219826455829058643829)
                ·
                  refine ⟨300770608730233974247859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3208219826455829058643829 300770608730233974247859)
                  ·
                    rfl

theorem cell22_2635869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_2635869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635869 prefixEnd_2635869 := by exact prefixLift 2635869
  have htrace : WordTrace (prefixWord ++ tailWord_2635869) baseStart_2635869 baseEnd_2635869 := by
    simpa [prefixWord, tailWord_2635869, baseEnd_2635869] using wordTrace_append hprefix tailTrace_2635869
  have hstable : (prefixWord ++ tailWord_2635869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635869).length < 2 ^ (prefixWord ++ tailWord_2635869).sum := by decide
  have hdescent : baseEnd_2635869 < baseStart_2635869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635912 : List Nat := [2, 1, 3, 4, 1, 1, 1, 4, 2, 3]
def baseStart_2635912 : Nat := 118140960795 + 2635912 * 2 ^ 59
def prefixEnd_2635912 : Nat := 4983230072969 + 3 ^ 40 * 2635912 * 2
def baseEnd_2635912 : Nat := 902326545969464143918445

theorem tailTrace_2635912 : CollatzResearch.WordTrace tailWord_2635912 prefixEnd_2635912 902326545969464143918445 := by
  unfold tailWord_2635912
  simp only [CollatzResearch.WordTrace]
  refine ⟨48069804413274238387106995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64093072551032317849475993 48069804413274238387106995)
  ·
    refine ⟨72104706619911357580660493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48069804413274238387106995 72104706619911357580660493)
    ·
      refine ⟨27039264982466759092747685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72104706619911357580660493 27039264982466759092747685)
      ·
        refine ⟨5069862184212517329890191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27039264982466759092747685 5069862184212517329890191)
        ·
          refine ⟨7604793276318775994835287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5069862184212517329890191 7604793276318775994835287)
          ·
            refine ⟨11407189914478163992252931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7604793276318775994835287 11407189914478163992252931)
            ·
              refine ⟨17110784871717245988379397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11407189914478163992252931 17110784871717245988379397)
              ·
                refine ⟨3208272163446983622821137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17110784871717245988379397 3208272163446983622821137)
                ·
                  refine ⟨2406204122585237717115853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3208272163446983622821137 2406204122585237717115853)
                  ·
                    refine ⟨902326545969464143918445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2406204122585237717115853 902326545969464143918445)
                    ·
                      rfl

theorem cell22_2635912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_2635912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635912 prefixEnd_2635912 := by exact prefixLift 2635912
  have htrace : WordTrace (prefixWord ++ tailWord_2635912) baseStart_2635912 baseEnd_2635912 := by
    simpa [prefixWord, tailWord_2635912, baseEnd_2635912] using wordTrace_append hprefix tailTrace_2635912
  have hstable : (prefixWord ++ tailWord_2635912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635912).length < 2 ^ (prefixWord ++ tailWord_2635912).sum := by decide
  have hdescent : baseEnd_2635912 < baseStart_2635912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635914 : List Nat := [3, 1, 2, 3, 1, 4, 2, 2, 4]
def baseStart_2635914 : Nat := 118140960795 + 2635914 * 2 ^ 59
def prefixEnd_2635914 : Nat := 4983230072969 + 3 ^ 40 * 2635914 * 2
def baseEnd_2635914 : Nat := 300775743536778935122813

theorem tailTrace_2635914 : CollatzResearch.WordTrace tailWord_2635914 prefixEnd_2635914 300775743536778935122813 := by
  unfold tailWord_2635914
  simp only [CollatzResearch.WordTrace]
  refine ⟨24034920443135307778946699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64093121181694154077191197 24034920443135307778946699)
  ·
    refine ⟨36052380664702961668420049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24034920443135307778946699 36052380664702961668420049)
    ·
      refine ⟨27039285498527221251315037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36052380664702961668420049 27039285498527221251315037)
      ·
        refine ⟨10139732061947707969243139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27039285498527221251315037 10139732061947707969243139)
        ·
          refine ⟨15209598092921561953864709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10139732061947707969243139 15209598092921561953864709)
          ·
            refine ⟨2851799642422792866349633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15209598092921561953864709 2851799642422792866349633)
            ·
              refine ⟨2138849731817094649762225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2851799642422792866349633 2138849731817094649762225)
              ·
                refine ⟨1604137298862820987321669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2138849731817094649762225 1604137298862820987321669)
                ·
                  refine ⟨300775743536778935122813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1604137298862820987321669 300775743536778935122813)
                  ·
                    rfl

theorem cell22_2635914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_2635914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2635914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2635914 prefixEnd_2635914 := by exact prefixLift 2635914
  have htrace : WordTrace (prefixWord ++ tailWord_2635914) baseStart_2635914 baseEnd_2635914 := by
    simpa [prefixWord, tailWord_2635914, baseEnd_2635914] using wordTrace_append hprefix tailTrace_2635914
  have hstable : (prefixWord ++ tailWord_2635914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635914).length < 2 ^ (prefixWord ++ tailWord_2635914).sum := by decide
  have hdescent : baseEnd_2635914 < baseStart_2635914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636077 : List Nat := [1, 5, 3, 1, 2, 10]
def baseStart_2636077 : Nat := 118140960795 + 2636077 * 2 ^ 59
def prefixEnd_2636077 : Nat := 4983230072969 + 3 ^ 40 * 2636077 * 2
def baseEnd_2636077 : Nat := 11140531220264922389419

theorem tailTrace_2636077 : CollatzResearch.WordTrace tailWord_2636077 prefixEnd_2636077 11140531220264922389419 := by
  unfold tailWord_2636077
  simp only [CollatzResearch.WordTrace]
  refine ⟨96145626870950709953970485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64097084580633806635980323 96145626870950709953970485)
  ·
    refine ⟨9013652519151629058184733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96145626870950709953970485 9013652519151629058184733)
    ·
      refine ⟨3380119694681860896819275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9013652519151629058184733 3380119694681860896819275)
      ·
        refine ⟨5070179542022791345228913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3380119694681860896819275 5070179542022791345228913)
        ·
          refine ⟨3802634656517093508921685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5070179542022791345228913 3802634656517093508921685)
          ·
            refine ⟨11140531220264922389419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3802634656517093508921685 11140531220264922389419)
            ·
              rfl

theorem cell22_2636077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 10].length) (baseStart_2636077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636077 prefixEnd_2636077 := by exact prefixLift 2636077
  have htrace : WordTrace (prefixWord ++ tailWord_2636077) baseStart_2636077 baseEnd_2636077 := by
    simpa [prefixWord, tailWord_2636077, baseEnd_2636077] using wordTrace_append hprefix tailTrace_2636077
  have hstable : (prefixWord ++ tailWord_2636077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636077).length < 2 ^ (prefixWord ++ tailWord_2636077).sum := by decide
  have hdescent : baseEnd_2636077 < baseStart_2636077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636090 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_2636090 : Nat := 118140960795 + 2636090 * 2 ^ 59
def prefixEnd_2636090 : Nat := 4983230072969 + 3 ^ 40 * 2636090 * 2
def baseEnd_2636090 : Nat := 902387479007131012967899

theorem tailTrace_2636090 : CollatzResearch.WordTrace tailWord_2636090 prefixEnd_2636090 902387479007131012967899 := by
  unfold tailWord_2636090
  simp only [CollatzResearch.WordTrace]
  refine ⟨24036525254975903293548431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64097400679935742116129149 24036525254975903293548431)
  ·
    refine ⟨36054787882463854940322647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24036525254975903293548431 36054787882463854940322647)
    ·
      refine ⟨54082181823695782410483971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36054787882463854940322647 54082181823695782410483971)
      ·
        refine ⟨81123272735543673615725957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54082181823695782410483971 81123272735543673615725957)
        ·
          refine ⟨15210613637914438802948617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81123272735543673615725957 15210613637914438802948617)
          ·
            refine ⟨11407960228435829102211463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15210613637914438802948617 11407960228435829102211463)
            ·
              refine ⟨17111940342653743653317195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11407960228435829102211463 17111940342653743653317195)
              ·
                refine ⟨25667910513980615479975793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17111940342653743653317195 25667910513980615479975793)
                ·
                  refine ⟨19250932885485461609981845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25667910513980615479975793 19250932885485461609981845)
                  ·
                    refine ⟨902387479007131012967899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19250932885485461609981845 902387479007131012967899)
                    ·
                      rfl

theorem cell22_2636090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_2636090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636090 prefixEnd_2636090 := by exact prefixLift 2636090
  have htrace : WordTrace (prefixWord ++ tailWord_2636090) baseStart_2636090 baseEnd_2636090 := by
    simpa [prefixWord, tailWord_2636090, baseEnd_2636090] using wordTrace_append hprefix tailTrace_2636090
  have hstable : (prefixWord ++ tailWord_2636090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636090).length < 2 ^ (prefixWord ++ tailWord_2636090).sum := by decide
  have hdescent : baseEnd_2636090 < baseStart_2636090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636092 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 3, 3]
def baseStart_2636092 : Nat := 118140960795 + 2636092 * 2 ^ 59
def prefixEnd_2636092 : Nat := 4983230072969 + 3 ^ 40 * 2636092 * 2
def baseEnd_2636092 : Nat := 902388163648003674417893

theorem tailTrace_2636092 : CollatzResearch.WordTrace tailWord_2636092 prefixEnd_2636092 902388163648003674417893 := by
  unfold tailWord_2636092
  simp only [CollatzResearch.WordTrace]
  refine ⟨48073086982948183757883265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64097449310597578343844353 48073086982948183757883265)
  ·
    refine ⟨36054815237211137818412449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48073086982948183757883265 36054815237211137818412449)
    ·
      refine ⟨27041111427908353363809337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36054815237211137818412449 27041111427908353363809337)
      ·
        refine ⟨20280833570931265022857003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27041111427908353363809337 20280833570931265022857003)
        ·
          refine ⟨30421250356396897534285505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20280833570931265022857003 30421250356396897534285505)
          ·
            refine ⟨22815937767297673150714129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30421250356396897534285505 22815937767297673150714129)
            ·
              refine ⟨17111953325473254863035597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22815937767297673150714129 17111953325473254863035597)
              ·
                refine ⟨6416982497052470573638349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17111953325473254863035597 6416982497052470573638349)
                ·
                  refine ⟨2406368436394676465114381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6416982497052470573638349 2406368436394676465114381)
                  ·
                    refine ⟨902388163648003674417893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2406368436394676465114381 902388163648003674417893)
                    ·
                      rfl

theorem cell22_2636092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_2636092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636092 prefixEnd_2636092 := by exact prefixLift 2636092
  have htrace : WordTrace (prefixWord ++ tailWord_2636092) baseStart_2636092 baseEnd_2636092 := by
    simpa [prefixWord, tailWord_2636092, baseEnd_2636092] using wordTrace_append hprefix tailTrace_2636092
  have hstable : (prefixWord ++ tailWord_2636092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636092).length < 2 ^ (prefixWord ++ tailWord_2636092).sum := by decide
  have hdescent : baseEnd_2636092 < baseStart_2636092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636169 : List Nat := [1, 2, 1, 1, 6, 2, 2, 2, 1, 4]
def baseStart_2636169 : Nat := 118140960795 + 2636169 * 2 ^ 59
def prefixEnd_2636169 : Nat := 4983230072969 + 3 ^ 40 * 2636169 * 2
def baseEnd_2636169 : Nat := 902414522321601140242657

theorem tailTrace_2636169 : CollatzResearch.WordTrace tailWord_2636169 prefixEnd_2636169 902414522321601140242657 := by
  unfold tailWord_2636169
  simp only [CollatzResearch.WordTrace]
  refine ⟨96148982386617409666319561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64099321591078273110879707 96148982386617409666319561)
  ·
    refine ⟨72111736789963057249739671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96148982386617409666319561 72111736789963057249739671)
    ·
      refine ⟨108167605184944585874609507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72111736789963057249739671 108167605184944585874609507)
      ·
        refine ⟨162251407777416878811914261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108167605184944585874609507 162251407777416878811914261)
        ·
          refine ⟨7605534739566416194308481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 162251407777416878811914261 7605534739566416194308481)
          ·
            refine ⟨5704151054674812145731361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7605534739566416194308481 5704151054674812145731361)
            ·
              refine ⟨4278113291006109109298521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5704151054674812145731361 4278113291006109109298521)
              ·
                refine ⟨3208584968254581831973891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4278113291006109109298521 3208584968254581831973891)
                ·
                  refine ⟨4812877452381872747960837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3208584968254581831973891 4812877452381872747960837)
                  ·
                    refine ⟨902414522321601140242657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4812877452381872747960837 902414522321601140242657)
                    ·
                      rfl

theorem cell22_2636169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_2636169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636169 prefixEnd_2636169 := by exact prefixLift 2636169
  have htrace : WordTrace (prefixWord ++ tailWord_2636169) baseStart_2636169 baseEnd_2636169 := by
    simpa [prefixWord, tailWord_2636169, baseEnd_2636169] using wordTrace_append hprefix tailTrace_2636169
  have hstable : (prefixWord ++ tailWord_2636169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636169).length < 2 ^ (prefixWord ++ tailWord_2636169).sum := by decide
  have hdescent : baseEnd_2636169 < baseStart_2636169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636195 : List Nat := [1, 1, 1, 4, 1, 4, 10]
def baseStart_2636195 : Nat := 118140960795 + 2636195 * 2 ^ 59
def prefixEnd_2636195 : Nat := 4983230072969 + 3 ^ 40 * 2636195 * 2
def baseEnd_2636195 : Nat := 33423089727886879225651

theorem tailTrace_2636195 : CollatzResearch.WordTrace tailWord_2636195 prefixEnd_2636195 33423089727886879225651 := by
  unfold tailWord_2636195
  simp only [CollatzResearch.WordTrace]
  refine ⟨96149930684523216106766039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64099953789682144071177359 96149930684523216106766039)
  ·
    refine ⟨144224896026784824160149059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96149930684523216106766039 144224896026784824160149059)
    ·
      refine ⟨216337344040177236240223589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144224896026784824160149059 216337344040177236240223589)
      ·
        refine ⟨40563252007533231795041923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216337344040177236240223589 40563252007533231795041923)
        ·
          refine ⟨60844878011299847692562885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40563252007533231795041923 60844878011299847692562885)
          ·
            refine ⟨11408414627118721442355541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60844878011299847692562885 11408414627118721442355541)
            ·
              refine ⟨33423089727886879225651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11408414627118721442355541 33423089727886879225651)
              ·
                rfl

theorem cell22_2636195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 10].length) (baseStart_2636195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636195 prefixEnd_2636195 := by exact prefixLift 2636195
  have htrace : WordTrace (prefixWord ++ tailWord_2636195) baseStart_2636195 baseEnd_2636195 := by
    simpa [prefixWord, tailWord_2636195, baseEnd_2636195] using wordTrace_append hprefix tailTrace_2636195
  have hstable : (prefixWord ++ tailWord_2636195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636195).length < 2 ^ (prefixWord ++ tailWord_2636195).sum := by decide
  have hdescent : baseEnd_2636195 < baseStart_2636195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636197 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 2, 4]
def baseStart_2636197 : Nat := 118140960795 + 2636197 * 2 ^ 59
def prefixEnd_2636197 : Nat := 4983230072969 + 3 ^ 40 * 2636197 * 2
def baseEnd_2636197 : Nat := 902424107293818400542571

theorem tailTrace_2636197 : CollatzResearch.WordTrace tailWord_2636197 prefixEnd_2636197 902424107293818400542571 := by
  unfold tailWord_2636197
  simp only [CollatzResearch.WordTrace]
  refine ⟨96150003630515970448338845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64100002420343980298892563 96150003630515970448338845)
  ·
    refine ⟨36056251361443488918127067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96150003630515970448338845 36056251361443488918127067)
    ·
      refine ⟨54084377042165233377190601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36056251361443488918127067 54084377042165233377190601)
      ·
        refine ⟨40563282781623925032892951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54084377042165233377190601 40563282781623925032892951)
        ·
          refine ⟨60844924172435887549339427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40563282781623925032892951 60844924172435887549339427)
          ·
            refine ⟨91267386258653831324009141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60844924172435887549339427 91267386258653831324009141)
            ·
              refine ⟨8556317461748796686625857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91267386258653831324009141 8556317461748796686625857)
              ·
                refine ⟨6417238096311597514969393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8556317461748796686625857 6417238096311597514969393)
                ·
                  refine ⟨4812928572233698136227045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6417238096311597514969393 4812928572233698136227045)
                  ·
                    refine ⟨902424107293818400542571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4812928572233698136227045 902424107293818400542571)
                    ·
                      rfl

theorem cell22_2636197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_2636197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636197 prefixEnd_2636197 := by exact prefixLift 2636197
  have htrace : WordTrace (prefixWord ++ tailWord_2636197) baseStart_2636197 baseEnd_2636197 := by
    simpa [prefixWord, tailWord_2636197, baseEnd_2636197] using wordTrace_append hprefix tailTrace_2636197
  have hstable : (prefixWord ++ tailWord_2636197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636197).length < 2 ^ (prefixWord ++ tailWord_2636197).sum := by decide
  have hdescent : baseEnd_2636197 < baseStart_2636197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636199 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 4, 3]
def baseStart_2636199 : Nat := 118140960795 + 2636199 * 2 ^ 59
def prefixEnd_2636199 : Nat := 4983230072969 + 3 ^ 40 * 2636199 * 2
def baseEnd_2636199 : Nat := 902424791934691061992565

theorem tailTrace_2636199 : CollatzResearch.WordTrace tailWord_2636199 prefixEnd_2636199 902424791934691061992565 := by
  unfold tailWord_2636199
  simp only [CollatzResearch.WordTrace]
  refine ⟨96150076576508724789911651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64100051051005816526607767 96150076576508724789911651)
  ·
    refine ⟨144225114864763087184867477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96150076576508724789911651 144225114864763087184867477)
    ·
      refine ⟨6760552259285769711790663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 144225114864763087184867477 6760552259285769711790663)
      ·
        refine ⟨10140828388928654567685995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6760552259285769711790663 10140828388928654567685995)
        ·
          refine ⟨15211242583392981851528993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10140828388928654567685995 15211242583392981851528993)
          ·
            refine ⟨11408431937544736388646745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15211242583392981851528993 11408431937544736388646745)
            ·
              refine ⟨8556323953158552291485059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11408431937544736388646745 8556323953158552291485059)
              ·
                refine ⟨12834485929737828437227589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8556323953158552291485059 12834485929737828437227589)
                ·
                  refine ⟨2406466111825842831980173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12834485929737828437227589 2406466111825842831980173)
                  ·
                    refine ⟨902424791934691061992565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2406466111825842831980173 902424791934691061992565)
                    ·
                      rfl

theorem cell22_2636199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_2636199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636199 prefixEnd_2636199 := by exact prefixLift 2636199
  have htrace : WordTrace (prefixWord ++ tailWord_2636199) baseStart_2636199 baseEnd_2636199 := by
    simpa [prefixWord, tailWord_2636199, baseEnd_2636199] using wordTrace_append hprefix tailTrace_2636199
  have hstable : (prefixWord ++ tailWord_2636199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636199).length < 2 ^ (prefixWord ++ tailWord_2636199).sum := by decide
  have hdescent : baseEnd_2636199 < baseStart_2636199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636227 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 5, 3]
def baseStart_2636227 : Nat := 118140960795 + 2636227 * 2 ^ 59
def prefixEnd_2636227 : Nat := 4983230072969 + 3 ^ 40 * 2636227 * 2
def baseEnd_2636227 : Nat := 902434376906908322292479

theorem tailTrace_2636227 : CollatzResearch.WordTrace tailWord_2636227 prefixEnd_2636227 902434376906908322292479 := by
  unfold tailWord_2636227
  simp only [CollatzResearch.WordTrace]
  refine ⟨96151097820407285571930935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64100731880271523714620623 96151097820407285571930935)
  ·
    refine ⟨144226646730610928357896403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96151097820407285571930935 144226646730610928357896403)
    ·
      refine ⟨216339970095916392536844605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144226646730610928357896403 216339970095916392536844605)
      ·
        refine ⟨81127488785968647201316727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216339970095916392536844605 81127488785968647201316727)
        ·
          refine ⟨121691233178952970801975091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81127488785968647201316727 121691233178952970801975091)
          ·
            refine ⟨182536849768429456202962637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121691233178952970801975091 182536849768429456202962637)
            ·
              refine ⟨68451318663161046076110989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182536849768429456202962637 68451318663161046076110989)
              ·
                refine ⟨25669244498685392278541621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68451318663161046076110989 25669244498685392278541621)
                ·
                  refine ⟨2406491671751755526113277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25669244498685392278541621 2406491671751755526113277)
                  ·
                    refine ⟨902434376906908322292479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2406491671751755526113277 902434376906908322292479)
                    ·
                      rfl

theorem cell22_2636227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 3].length) (baseStart_2636227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636227 prefixEnd_2636227 := by exact prefixLift 2636227
  have htrace : WordTrace (prefixWord ++ tailWord_2636227) baseStart_2636227 baseEnd_2636227 := by
    simpa [prefixWord, tailWord_2636227, baseEnd_2636227] using wordTrace_append hprefix tailTrace_2636227
  have hstable : (prefixWord ++ tailWord_2636227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636227).length < 2 ^ (prefixWord ++ tailWord_2636227).sum := by decide
  have hdescent : baseEnd_2636227 < baseStart_2636227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636272 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 2, 5]
def baseStart_2636272 : Nat := 118140960795 + 2636272 * 2 ^ 59
def prefixEnd_2636272 : Nat := 4983230072969 + 3 ^ 40 * 2636272 * 2
def baseEnd_2636272 : Nat := 902449781326543204917341

theorem tailTrace_2636272 : CollatzResearch.WordTrace tailWord_2636272 prefixEnd_2636272 902449781326543204917341 := by
  unfold tailWord_2636272
  simp only [CollatzResearch.WordTrace]
  refine ⟨48076369552622129128659535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64101826070162838838212713 48076369552622129128659535)
  ·
    refine ⟨72114554328933193692989303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48076369552622129128659535 72114554328933193692989303)
    ·
      refine ⟨108171831493399790539483955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72114554328933193692989303 108171831493399790539483955)
      ·
        refine ⟨162257747240099685809225933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108171831493399790539483955 162257747240099685809225933)
        ·
          refine ⟨60846655215037382178459725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162257747240099685809225933 60846655215037382178459725)
          ·
            refine ⟨22817495705639018316922397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60846655215037382178459725 22817495705639018316922397)
            ·
              refine ⟨8556560889614631868845899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22817495705639018316922397 8556560889614631868845899)
              ·
                refine ⟨12834841334421947803268849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8556560889614631868845899 12834841334421947803268849)
                ·
                  refine ⟨9626131000816460852451637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12834841334421947803268849 9626131000816460852451637)
                  ·
                    refine ⟨902449781326543204917341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9626131000816460852451637 902449781326543204917341)
                    ·
                      rfl

theorem cell22_2636272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_2636272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636272 prefixEnd_2636272 := by exact prefixLift 2636272
  have htrace : WordTrace (prefixWord ++ tailWord_2636272) baseStart_2636272 baseEnd_2636272 := by
    simpa [prefixWord, tailWord_2636272, baseEnd_2636272] using wordTrace_append hprefix tailTrace_2636272
  have hstable : (prefixWord ++ tailWord_2636272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636272).length < 2 ^ (prefixWord ++ tailWord_2636272).sum := by decide
  have hdescent : baseEnd_2636272 < baseStart_2636272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636287 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 3, 4]
def baseStart_2636287 : Nat := 118140960795 + 2636287 * 2 ^ 59
def prefixEnd_2636287 : Nat := 4983230072969 + 3 ^ 40 * 2636287 * 2
def baseEnd_2636287 : Nat := 902454916133088165792295

theorem tailTrace_2636287 : CollatzResearch.WordTrace tailWord_2636287 prefixEnd_2636287 902454916133088165792295 := by
  unfold tailWord_2636287
  simp only [CollatzResearch.WordTrace]
  refine ⟨96153286200189915819115115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64102190800126610546076743 96153286200189915819115115)
  ·
    refine ⟨144229929300284873728672673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96153286200189915819115115 144229929300284873728672673)
    ·
      refine ⟨108172446975213655296504505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144229929300284873728672673 108172446975213655296504505)
      ·
        refine ⟨81129335231410241472378379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108172446975213655296504505 81129335231410241472378379)
        ·
          refine ⟨121694002847115362208567569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81129335231410241472378379 121694002847115362208567569)
          ·
            refine ⟨91270502135336521656425677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121694002847115362208567569 91270502135336521656425677)
            ·
              refine ⟨34226438300751195621159629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91270502135336521656425677 34226438300751195621159629)
              ·
                refine ⟨12834914362781698357934861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34226438300751195621159629 12834914362781698357934861)
                ·
                  refine ⟨4813092886043136884225573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12834914362781698357934861 4813092886043136884225573)
                  ·
                    refine ⟨902454916133088165792295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4813092886043136884225573 902454916133088165792295)
                    ·
                      rfl

theorem cell22_2636287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_2636287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636287 prefixEnd_2636287 := by exact prefixLift 2636287
  have htrace : WordTrace (prefixWord ++ tailWord_2636287) baseStart_2636287 baseEnd_2636287 := by
    simpa [prefixWord, tailWord_2636287, baseEnd_2636287] using wordTrace_append hprefix tailTrace_2636287
  have hstable : (prefixWord ++ tailWord_2636287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636287).length < 2 ^ (prefixWord ++ tailWord_2636287).sum := by decide
  have hdescent : baseEnd_2636287 < baseStart_2636287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636308 : List Nat := [2, 4, 3, 1, 1, 3, 1, 2, 5]
def baseStart_2636308 : Nat := 118140960795 + 2636308 * 2 ^ 59
def prefixEnd_2636308 : Nat := 4983230072969 + 3 ^ 40 * 2636308 * 2
def baseEnd_2636308 : Nat := 300820701620750370339077

theorem tailTrace_2636308 : CollatzResearch.WordTrace tailWord_2636308 prefixEnd_2636308 300820701620750370339077 := by
  unfold tailWord_2636308
  simp only [CollatzResearch.WordTrace]
  refine ⟨48077026066556918202814789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64102701422075890937086385 48077026066556918202814789)
  ·
    refine ⟨9014442387479422163027773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48077026066556918202814789 9014442387479422163027773)
    ·
      refine ⟨3380415895304783311135415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9014442387479422163027773 3380415895304783311135415)
      ·
        refine ⟨5070623842957174966703123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3380415895304783311135415 5070623842957174966703123)
        ·
          refine ⟨7605935764435762450054685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5070623842957174966703123 7605935764435762450054685)
          ·
            refine ⟨2852225911663410918770507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7605935764435762450054685 2852225911663410918770507)
            ·
              refine ⟨4278338867495116378155761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2852225911663410918770507 4278338867495116378155761)
              ·
                refine ⟨3208754150621337283616821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4278338867495116378155761 3208754150621337283616821)
                ·
                  refine ⟨300820701620750370339077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3208754150621337283616821 300820701620750370339077)
                  ·
                    rfl

theorem cell22_2636308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_2636308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636308 prefixEnd_2636308 := by exact prefixLift 2636308
  have htrace : WordTrace (prefixWord ++ tailWord_2636308) baseStart_2636308 baseEnd_2636308 := by
    simpa [prefixWord, tailWord_2636308, baseEnd_2636308] using wordTrace_append hprefix tailTrace_2636308
  have hstable : (prefixWord ++ tailWord_2636308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636308).length < 2 ^ (prefixWord ++ tailWord_2636308).sum := by decide
  have hdescent : baseEnd_2636308 < baseStart_2636308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636349 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_2636349 : Nat := 118140960795 + 2636349 * 2 ^ 59
def prefixEnd_2636349 : Nat := 4983230072969 + 3 ^ 40 * 2636349 * 2
def baseEnd_2636349 : Nat := 902476140000140670742105

theorem tailTrace_2636349 : CollatzResearch.WordTrace tailWord_2636349 prefixEnd_2636349 902476140000140670742105 := by
  unfold tailWord_2636349
  simp only [CollatzResearch.WordTrace]
  refine ⟨96155547525965300407872101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64103698350643533605248067 96155547525965300407872101)
  ·
    refine ⟨18029165161118493826476019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96155547525965300407872101 18029165161118493826476019)
    ·
      refine ⟨27043747741677740739714029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18029165161118493826476019 27043747741677740739714029)
      ·
        refine ⟨10141405403129152777392761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27043747741677740739714029 10141405403129152777392761)
        ·
          refine ⟨7606054052346864583044571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10141405403129152777392761 7606054052346864583044571)
          ·
            refine ⟨11409081078520296874566857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7606054052346864583044571 11409081078520296874566857)
            ·
              refine ⟨8556810808890222655925143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11409081078520296874566857 8556810808890222655925143)
              ·
                refine ⟨12835216213335333983887715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8556810808890222655925143 12835216213335333983887715)
                ·
                  refine ⟨19252824320003000975831573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12835216213335333983887715 19252824320003000975831573)
                  ·
                    refine ⟨902476140000140670742105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19252824320003000975831573 902476140000140670742105)
                    ·
                      rfl

theorem cell22_2636349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_2636349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636349 prefixEnd_2636349 := by exact prefixLift 2636349
  have htrace : WordTrace (prefixWord ++ tailWord_2636349) baseStart_2636349 baseEnd_2636349 := by
    simpa [prefixWord, tailWord_2636349, baseEnd_2636349] using wordTrace_append hprefix tailTrace_2636349
  have hstable : (prefixWord ++ tailWord_2636349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636349).length < 2 ^ (prefixWord ++ tailWord_2636349).sum := by decide
  have hdescent : baseEnd_2636349 < baseStart_2636349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636353 : List Nat := [1, 2, 5, 1, 1, 4, 1, 3, 4]
def baseStart_2636353 : Nat := 118140960795 + 2636353 * 2 ^ 59
def prefixEnd_2636353 : Nat := 4983230072969 + 3 ^ 40 * 2636353 * 2
def baseEnd_2636353 : Nat := 300825836427295331214031

theorem tailTrace_2636353 : CollatzResearch.WordTrace tailWord_2636353 prefixEnd_2636353 300825836427295331214031 := by
  unfold tailWord_2636353
  simp only [CollatzResearch.WordTrace]
  refine ⟨96155693417950809091017713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64103795611967206060678475 96155693417950809091017713)
  ·
    refine ⟨72116770063463106818263285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96155693417950809091017713 72116770063463106818263285)
    ·
      refine ⟨6760947193449666264212183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72116770063463106818263285 6760947193449666264212183)
      ·
        refine ⟨10141420790174499396318275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6760947193449666264212183 10141420790174499396318275)
        ·
          refine ⟨15212131185261749094477413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10141420790174499396318275 15212131185261749094477413)
          ·
            refine ⟨2852274597236577955214515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15212131185261749094477413 2852274597236577955214515)
            ·
              refine ⟨4278411895854866932821773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2852274597236577955214515 4278411895854866932821773)
              ·
                refine ⟨1604404460945575099808165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4278411895854866932821773 1604404460945575099808165)
                ·
                  refine ⟨300825836427295331214031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1604404460945575099808165 300825836427295331214031)
                  ·
                    rfl

theorem cell22_2636353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 4].length) (baseStart_2636353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636353 prefixEnd_2636353 := by exact prefixLift 2636353
  have htrace : WordTrace (prefixWord ++ tailWord_2636353) baseStart_2636353 baseEnd_2636353 := by
    simpa [prefixWord, tailWord_2636353, baseEnd_2636353] using wordTrace_append hprefix tailTrace_2636353
  have hstable : (prefixWord ++ tailWord_2636353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636353).length < 2 ^ (prefixWord ++ tailWord_2636353).sum := by decide
  have hdescent : baseEnd_2636353 < baseStart_2636353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636439 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 5, 4]
def baseStart_2636439 : Nat := 118140960795 + 2636439 * 2 ^ 59
def prefixEnd_2636439 : Nat := 4983230072969 + 3 ^ 40 * 2636439 * 2
def baseEnd_2636439 : Nat := 902506948839410435991829

theorem tailTrace_2636439 : CollatzResearch.WordTrace tailWord_2636439 prefixEnd_2636439 902506948839410435991829 := by
  unfold tailWord_2636439
  simp only [CollatzResearch.WordTrace]
  refine ⟨96158830095639245778648371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64105886730426163852432247 96158830095639245778648371)
  ·
    refine ⟨144238245143458868667972557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96158830095639245778648371 144238245143458868667972557)
    ·
      refine ⟨54089341928797075750489709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144238245143458868667972557 54089341928797075750489709)
      ·
        refine ⟨20283503223298903406433641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54089341928797075750489709 20283503223298903406433641)
        ·
          refine ⟨15212627417474177554825231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20283503223298903406433641 15212627417474177554825231)
          ·
            refine ⟨22818941126211266332237847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15212627417474177554825231 22818941126211266332237847)
            ·
              refine ⟨34228411689316899498356771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22818941126211266332237847 34228411689316899498356771)
              ·
                refine ⟨51342617533975349247535157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34228411689316899498356771 51342617533975349247535157)
                ·
                  refine ⟨4813370393810188991956421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51342617533975349247535157 4813370393810188991956421)
                  ·
                    refine ⟨902506948839410435991829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4813370393810188991956421 902506948839410435991829)
                    ·
                      rfl

theorem cell22_2636439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_2636439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636439 prefixEnd_2636439 := by exact prefixLift 2636439
  have htrace : WordTrace (prefixWord ++ tailWord_2636439) baseStart_2636439 baseEnd_2636439 := by
    simpa [prefixWord, tailWord_2636439, baseEnd_2636439] using wordTrace_append hprefix tailTrace_2636439
  have hstable : (prefixWord ++ tailWord_2636439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636439).length < 2 ^ (prefixWord ++ tailWord_2636439).sum := by decide
  have hdescent : baseEnd_2636439 < baseStart_2636439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636516 : List Nat := [2, 3, 1, 1, 1, 4, 4, 6]
def baseStart_2636516 : Nat := 118140960795 + 2636516 * 2 ^ 59
def prefixEnd_2636516 : Nat := 4983230072969 + 3 ^ 40 * 2636516 * 2
def baseEnd_2636516 : Nat := 100281478612556433535177

theorem tailTrace_2636516 : CollatzResearch.WordTrace tailWord_2636516 prefixEnd_2636516 100281478612556433535177 := by
  unfold tailWord_2636516
  simp only [CollatzResearch.WordTrace]
  refine ⟨48080819258180143964600701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64107759010906858619467601 48080819258180143964600701)
  ·
    refine ⟨18030307221817553986725263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48080819258180143964600701 18030307221817553986725263)
    ·
      refine ⟨27045460832726330980087895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18030307221817553986725263 27045460832726330980087895)
      ·
        refine ⟨40568191249089496470131843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27045460832726330980087895 40568191249089496470131843)
        ·
          refine ⟨60852286873634244705197765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40568191249089496470131843 60852286873634244705197765)
          ·
            refine ⟨11409803788806420882224581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60852286873634244705197765 11409803788806420882224581)
            ·
              refine ⟨2139338210401203915417109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11409803788806420882224581 2139338210401203915417109)
              ·
                refine ⟨100281478612556433535177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2139338210401203915417109 100281478612556433535177)
                ·
                  rfl

theorem cell22_2636516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 6].length) (baseStart_2636516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636516 prefixEnd_2636516 := by exact prefixLift 2636516
  have htrace : WordTrace (prefixWord ++ tailWord_2636516) baseStart_2636516 baseEnd_2636516 := by
    simpa [prefixWord, tailWord_2636516, baseEnd_2636516] using wordTrace_append hprefix tailTrace_2636516
  have hstable : (prefixWord ++ tailWord_2636516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636516).length < 2 ^ (prefixWord ++ tailWord_2636516).sum := by decide
  have hdescent : baseEnd_2636516 < baseStart_2636516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636559 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 1, 7]
def baseStart_2636559 : Nat := 118140960795 + 2636559 * 2 ^ 59
def prefixEnd_2636559 : Nat := 4983230072969 + 3 ^ 40 * 2636559 * 2
def baseEnd_2636559 : Nat := 902548027291770122991461

theorem tailTrace_2636559 : CollatzResearch.WordTrace tailWord_2636559 prefixEnd_2636559 902548027291770122991461 := by
  unfold tailWord_2636559
  simp only [CollatzResearch.WordTrace]
  refine ⟨96163206855204506273016731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64108804570136337515344487 96163206855204506273016731)
  ·
    refine ⟨144244810282806759409525097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96163206855204506273016731 144244810282806759409525097)
    ·
      refine ⟨108183607712105069557143823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144244810282806759409525097 108183607712105069557143823)
      ·
        refine ⟨162275411568157604335715735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108183607712105069557143823 162275411568157604335715735)
        ·
          refine ⟨243413117352236406503573603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162275411568157604335715735 243413117352236406503573603)
          ·
            refine ⟨365119676028354609755360405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243413117352236406503573603 365119676028354609755360405)
            ·
              refine ⟨17114984813829122332282519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 365119676028354609755360405 17114984813829122332282519)
              ·
                refine ⟨25672477220743683498423779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17114984813829122332282519 25672477220743683498423779)
                ·
                  refine ⟨38508715831115525247635669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25672477220743683498423779 38508715831115525247635669)
                  ·
                    refine ⟨902548027291770122991461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38508715831115525247635669 902548027291770122991461)
                    ·
                      rfl

theorem cell22_2636559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_2636559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636559 prefixEnd_2636559 := by exact prefixLift 2636559
  have htrace : WordTrace (prefixWord ++ tailWord_2636559) baseStart_2636559 baseEnd_2636559 := by
    simpa [prefixWord, tailWord_2636559, baseEnd_2636559] using wordTrace_append hprefix tailTrace_2636559
  have hstable : (prefixWord ++ tailWord_2636559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636559).length < 2 ^ (prefixWord ++ tailWord_2636559).sum := by decide
  have hdescent : baseEnd_2636559 < baseStart_2636559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636683 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 3, 3]
def baseStart_2636683 : Nat := 118140960795 + 2636683 * 2 ^ 59
def prefixEnd_2636683 : Nat := 4983230072969 + 3 ^ 40 * 2636683 * 2
def baseEnd_2636683 : Nat := 902590475025875132891081

theorem tailTrace_2636683 : CollatzResearch.WordTrace tailWord_2636683 prefixEnd_2636683 902590475025875132891081 := by
  unfold tailWord_2636683
  simp only [CollatzResearch.WordTrace]
  refine ⟨96167729506755275450530703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64111819671170183633687135 96167729506755275450530703)
  ·
    refine ⟨144251594260132913175796055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96167729506755275450530703 144251594260132913175796055)
    ·
      refine ⟨216377391390199369763694083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144251594260132913175796055 216377391390199369763694083)
      ·
        refine ⟨324566087085299054645541125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216377391390199369763694083 324566087085299054645541125)
        ·
          refine ⟨60856141328493572746038961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 324566087085299054645541125 60856141328493572746038961)
          ·
            refine ⟨45642105996370179559529221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60856141328493572746038961 45642105996370179559529221)
            ·
              refine ⟨8557894874319408667411729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45642105996370179559529221 8557894874319408667411729)
              ·
                refine ⟨6418421155739556500558797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8557894874319408667411729 6418421155739556500558797)
                ·
                  refine ⟨2406907933402333687709549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6418421155739556500558797 2406907933402333687709549)
                  ·
                    refine ⟨902590475025875132891081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2406907933402333687709549 902590475025875132891081)
                    ·
                      rfl

theorem cell22_2636683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 3].length) (baseStart_2636683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636683 prefixEnd_2636683 := by exact prefixLift 2636683
  have htrace : WordTrace (prefixWord ++ tailWord_2636683) baseStart_2636683 baseEnd_2636683 := by
    simpa [prefixWord, tailWord_2636683, baseEnd_2636683] using wordTrace_append hprefix tailTrace_2636683
  have hstable : (prefixWord ++ tailWord_2636683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636683).length < 2 ^ (prefixWord ++ tailWord_2636683).sum := by decide
  have hdescent : baseEnd_2636683 < baseStart_2636683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636790 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_2636790 : Nat := 118140960795 + 2636790 * 2 ^ 59
def prefixEnd_2636790 : Nat := 4983230072969 + 3 ^ 40 * 2636790 * 2
def baseEnd_2636790 : Nat := 902627103312562520465753

theorem tailTrace_2636790 : CollatzResearch.WordTrace tailWord_2636790 prefixEnd_2636790 902627103312562520465753 := by
  unfold tailWord_2636790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6010727007335477045292239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64114421411578421816450549 6010727007335477045292239)
  ·
    refine ⟨9016090511003215567938359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6010727007335477045292239 9016090511003215567938359)
    ·
      refine ⟨13524135766504823351907539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9016090511003215567938359 13524135766504823351907539)
      ·
        refine ⟨20286203649757235027861309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13524135766504823351907539 20286203649757235027861309)
        ·
          refine ⟨7607326368658963135447991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20286203649757235027861309 7607326368658963135447991)
          ·
            refine ⟨11410989552988444703171987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7607326368658963135447991 11410989552988444703171987)
            ·
              refine ⟨17116484329482667054757981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11410989552988444703171987 17116484329482667054757981)
              ·
                refine ⟨6418681623556000145534243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17116484329482667054757981 6418681623556000145534243)
                ·
                  refine ⟨9628022435334000218301365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6418681623556000145534243 9628022435334000218301365)
                  ·
                    refine ⟨902627103312562520465753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9628022435334000218301365 902627103312562520465753)
                    ·
                      rfl

theorem cell22_2636790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_2636790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636790 prefixEnd_2636790 := by exact prefixLift 2636790
  have htrace : WordTrace (prefixWord ++ tailWord_2636790) baseStart_2636790 baseEnd_2636790 := by
    simpa [prefixWord, tailWord_2636790, baseEnd_2636790] using wordTrace_append hprefix tailTrace_2636790
  have hstable : (prefixWord ++ tailWord_2636790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636790).length < 2 ^ (prefixWord ++ tailWord_2636790).sum := by decide
  have hdescent : baseEnd_2636790 < baseStart_2636790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636835 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 3, 3]
def baseStart_2636835 : Nat := 118140960795 + 2636835 * 2 ^ 59
def prefixEnd_2636835 : Nat := 4983230072969 + 3 ^ 40 * 2636835 * 2
def baseEnd_2636835 : Nat := 902642507732197403090615

theorem tailTrace_2636835 : CollatzResearch.WordTrace tailWord_2636835 prefixEnd_2636835 902642507732197403090615 := by
  unfold tailWord_2636835
  simp only [CollatzResearch.WordTrace]
  refine ⟨96173273402204605410063959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64115515601469736940042639 96173273402204605410063959)
  ·
    refine ⟨144259910103306908115095939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96173273402204605410063959 144259910103306908115095939)
    ·
      refine ⟨216389865154960362172643909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144259910103306908115095939 216389865154960362172643909)
      ·
        refine ⟨40573099716555067907370733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216389865154960362172643909 40573099716555067907370733)
        ·
          refine ⟨15214912393708150465264025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40573099716555067907370733 15214912393708150465264025)
          ·
            refine ⟨11411184295281112848948019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15214912393708150465264025 11411184295281112848948019)
            ·
              refine ⟨17116776442921669273422029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11411184295281112848948019 17116776442921669273422029)
              ·
                refine ⟨6418791166095625977533261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17116776442921669273422029 6418791166095625977533261)
                ·
                  refine ⟨2407046687285859741574973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6418791166095625977533261 2407046687285859741574973)
                  ·
                    refine ⟨902642507732197403090615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2407046687285859741574973 902642507732197403090615)
                    ·
                      rfl

theorem cell22_2636835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 3].length) (baseStart_2636835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636835 prefixEnd_2636835 := by exact prefixLift 2636835
  have htrace : WordTrace (prefixWord ++ tailWord_2636835) baseStart_2636835 baseEnd_2636835 := by
    simpa [prefixWord, tailWord_2636835, baseEnd_2636835] using wordTrace_append hprefix tailTrace_2636835
  have hstable : (prefixWord ++ tailWord_2636835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636835).length < 2 ^ (prefixWord ++ tailWord_2636835).sum := by decide
  have hdescent : baseEnd_2636835 < baseStart_2636835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636923 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 1, 6]
def baseStart_2636923 : Nat := 118140960795 + 2636923 * 2 ^ 59
def prefixEnd_2636923 : Nat := 4983230072969 + 3 ^ 40 * 2636923 * 2
def baseEnd_2636923 : Nat := 902672631930594506890345

theorem tailTrace_2636923 : CollatzResearch.WordTrace tailWord_2636923 prefixEnd_2636923 902672631930594506890345 := by
  unfold tailWord_2636923
  simp only [CollatzResearch.WordTrace]
  refine ⟨96176483025885796439267423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64117655350590530959511615 96176483025885796439267423)
  ·
    refine ⟨144264724538828694658901135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96176483025885796439267423 144264724538828694658901135)
    ·
      refine ⟨216397086808243041988351703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144264724538828694658901135 216397086808243041988351703)
      ·
        refine ⟨324595630212364562982527555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216397086808243041988351703 324595630212364562982527555)
        ·
          refine ⟨486893445318546844473791333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324595630212364562982527555 486893445318546844473791333)
          ·
            refine ⟨91292520997227533338835875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 486893445318546844473791333 91292520997227533338835875)
            ·
              refine ⟨136938781495841300008253813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91292520997227533338835875 136938781495841300008253813)
              ·
                refine ⟨12838010765235121875773795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136938781495841300008253813 12838010765235121875773795)
                ·
                  refine ⟨19257016147852682813660693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12838010765235121875773795 19257016147852682813660693)
                  ·
                    refine ⟨902672631930594506890345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19257016147852682813660693 902672631930594506890345)
                    ·
                      rfl

theorem cell22_2636923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 6].length) (baseStart_2636923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636923 prefixEnd_2636923 := by exact prefixLift 2636923
  have htrace : WordTrace (prefixWord ++ tailWord_2636923) baseStart_2636923 baseEnd_2636923 := by
    simpa [prefixWord, tailWord_2636923, baseEnd_2636923] using wordTrace_append hprefix tailTrace_2636923
  have hstable : (prefixWord ++ tailWord_2636923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636923).length < 2 ^ (prefixWord ++ tailWord_2636923).sum := by decide
  have hdescent : baseEnd_2636923 < baseStart_2636923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636925 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_2636925 : Nat := 118140960795 + 2636925 * 2 ^ 59
def prefixEnd_2636925 : Nat := 4983230072969 + 3 ^ 40 * 2636925 * 2
def baseEnd_2636925 : Nat := 902673316571467168340339

theorem tailTrace_2636925 : CollatzResearch.WordTrace tailWord_2636925 prefixEnd_2636925 902673316571467168340339 := by
  unfold tailWord_2636925
  simp only [CollatzResearch.WordTrace]
  refine ⟨96176555971878550780840229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64117703981252367187226819 96176555971878550780840229)
  ·
    refine ⟨18033104244727228271407543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96176555971878550780840229 18033104244727228271407543)
    ·
      refine ⟨27049656367090842407111315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18033104244727228271407543 27049656367090842407111315)
      ·
        refine ⟨40574484550636263610666973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27049656367090842407111315 40574484550636263610666973)
        ·
          refine ⟨15215431706488598854000115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40574484550636263610666973 15215431706488598854000115)
          ·
            refine ⟨22823147559732898281000173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15215431706488598854000115 22823147559732898281000173)
            ·
              refine ⟨8558680334899836855375065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22823147559732898281000173 8558680334899836855375065)
              ·
                refine ⟨6419010251174877641531299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8558680334899836855375065 6419010251174877641531299)
                ·
                  refine ⟨9628515376762316462296949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6419010251174877641531299 9628515376762316462296949)
                  ·
                    refine ⟨902673316571467168340339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9628515376762316462296949 902673316571467168340339)
                    ·
                      rfl

theorem cell22_2636925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_2636925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636925 prefixEnd_2636925 := by exact prefixLift 2636925
  have htrace : WordTrace (prefixWord ++ tailWord_2636925) baseStart_2636925 baseEnd_2636925 := by
    simpa [prefixWord, tailWord_2636925, baseEnd_2636925] using wordTrace_append hprefix tailTrace_2636925
  have hstable : (prefixWord ++ tailWord_2636925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636925).length < 2 ^ (prefixWord ++ tailWord_2636925).sum := by decide
  have hdescent : baseEnd_2636925 < baseStart_2636925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636929 : List Nat := [1, 2, 4, 2, 2, 2, 3, 1, 1, 4]
def baseStart_2636929 : Nat := 118140960795 + 2636929 * 2 ^ 59
def prefixEnd_2636929 : Nat := 4983230072969 + 3 ^ 40 * 2636929 * 2
def baseEnd_2636929 : Nat := 902674685853212491240327

theorem tailTrace_2636929 : CollatzResearch.WordTrace tailWord_2636929 prefixEnd_2636929 902674685853212491240327 := by
  unfold tailWord_2636929
  simp only [CollatzResearch.WordTrace]
  refine ⟨96176701863864059463985841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64117801242576039642657227 96176701863864059463985841)
  ·
    refine ⟨72132526397898044597989381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96176701863864059463985841 72132526397898044597989381)
    ·
      refine ⟨13524848699605883362123009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72132526397898044597989381 13524848699605883362123009)
      ·
        refine ⟨10143636524704412521592257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13524848699605883362123009 10143636524704412521592257)
        ·
          refine ⟨7607727393528309391194193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10143636524704412521592257 7607727393528309391194193)
          ·
            refine ⟨5705795545146232043395645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7607727393528309391194193 5705795545146232043395645)
            ·
              refine ⟨2139673329429837016273367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5705795545146232043395645 2139673329429837016273367)
              ·
                refine ⟨3209509994144755524410051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2139673329429837016273367 3209509994144755524410051)
                ·
                  refine ⟨4814264991217133286615077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3209509994144755524410051 4814264991217133286615077)
                  ·
                    refine ⟨902674685853212491240327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4814264991217133286615077 902674685853212491240327)
                    ·
                      rfl

theorem cell22_2636929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_2636929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636929 prefixEnd_2636929 := by exact prefixLift 2636929
  have htrace : WordTrace (prefixWord ++ tailWord_2636929) baseStart_2636929 baseEnd_2636929 := by
    simpa [prefixWord, tailWord_2636929, baseEnd_2636929] using wordTrace_append hprefix tailTrace_2636929
  have hstable : (prefixWord ++ tailWord_2636929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636929).length < 2 ^ (prefixWord ++ tailWord_2636929).sum := by decide
  have hdescent : baseEnd_2636929 < baseStart_2636929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636953 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 4, 7]
def baseStart_2636953 : Nat := 118140960795 + 2636953 * 2 ^ 59
def prefixEnd_2636953 : Nat := 4983230072969 + 3 ^ 40 * 2636953 * 2
def baseEnd_2636953 : Nat := 902682901543684428640253

theorem tailTrace_2636953 : CollatzResearch.WordTrace tailWord_2636953 prefixEnd_2636953 902682901543684428640253 := by
  unfold tailWord_2636953
  simp only [CollatzResearch.WordTrace]
  refine ⟨96177577215777111562859513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64118384810518074375239675 96177577215777111562859513)
  ·
    refine ⟨72133182911832833672144635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96177577215777111562859513 72133182911832833672144635)
    ·
      refine ⟨108199774367749250508216953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72133182911832833672144635 108199774367749250508216953)
      ·
        refine ⟨81149830775811937881162715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108199774367749250508216953 81149830775811937881162715)
        ·
          refine ⟨121724746163717906821744073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81149830775811937881162715 121724746163717906821744073)
          ·
            refine ⟨91293559622788430116308055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121724746163717906821744073 91293559622788430116308055)
            ·
              refine ⟨136940339434182645174462083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91293559622788430116308055 136940339434182645174462083)
              ·
                refine ⟨205410509151273967761693125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136940339434182645174462083 205410509151273967761693125)
                ·
                  refine ⟨38514470465863868955317461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205410509151273967761693125 38514470465863868955317461)
                  ·
                    refine ⟨902682901543684428640253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38514470465863868955317461 902682901543684428640253)
                    ·
                      rfl

theorem cell22_2636953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_2636953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2636953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2636953 prefixEnd_2636953 := by exact prefixLift 2636953
  have htrace : WordTrace (prefixWord ++ tailWord_2636953) baseStart_2636953 baseEnd_2636953 := by
    simpa [prefixWord, tailWord_2636953, baseEnd_2636953] using wordTrace_append hprefix tailTrace_2636953
  have hstable : (prefixWord ++ tailWord_2636953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636953).length < 2 ^ (prefixWord ++ tailWord_2636953).sum := by decide
  have hdescent : baseEnd_2636953 < baseStart_2636953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637015 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 2, 5]
def baseStart_2637015 : Nat := 118140960795 + 2637015 * 2 ^ 59
def prefixEnd_2637015 : Nat := 4983230072969 + 3 ^ 40 * 2637015 * 2
def baseEnd_2637015 : Nat := 902704125410736933590063

theorem tailTrace_2637015 : CollatzResearch.WordTrace tailWord_2637015 prefixEnd_2637015 902704125410736933590063 := by
  unfold tailWord_2637015
  simp only [CollatzResearch.WordTrace]
  refine ⟨96179838541552496151616499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64119892361034997434410999 96179838541552496151616499)
  ·
    refine ⟨144269757812328744227424749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96179838541552496151616499 144269757812328744227424749)
    ·
      refine ⟨54101159179623279085284281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144269757812328744227424749 54101159179623279085284281)
      ·
        refine ⟨40575869384717459313963211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54101159179623279085284281 40575869384717459313963211)
        ·
          refine ⟨60863804077076188970944817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40575869384717459313963211 60863804077076188970944817)
          ·
            refine ⟨45647853057807141728208613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60863804077076188970944817 45647853057807141728208613)
            ·
              refine ⟨8558972448338839074039115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45647853057807141728208613 8558972448338839074039115)
              ·
                refine ⟨12838458672508258611058673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8558972448338839074039115 12838458672508258611058673)
                ·
                  refine ⟨9628844004381193958294005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12838458672508258611058673 9628844004381193958294005)
                  ·
                    refine ⟨902704125410736933590063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9628844004381193958294005 902704125410736933590063)
                    ·
                      rfl

theorem cell22_2637015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_2637015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637015 prefixEnd_2637015 := by exact prefixLift 2637015
  have htrace : WordTrace (prefixWord ++ tailWord_2637015) baseStart_2637015 baseEnd_2637015 := by
    simpa [prefixWord, tailWord_2637015, baseEnd_2637015] using wordTrace_append hprefix tailTrace_2637015
  have hstable : (prefixWord ++ tailWord_2637015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637015).length < 2 ^ (prefixWord ++ tailWord_2637015).sum := by decide
  have hdescent : baseEnd_2637015 < baseStart_2637015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637113 : List Nat := [1, 2, 1, 6, 2, 2, 2, 2, 4]
def baseStart_2637113 : Nat := 118140960795 + 2637113 * 2 ^ 59
def prefixEnd_2637113 : Nat := 4983230072969 + 3 ^ 40 * 2637113 * 2
def baseEnd_2637113 : Nat := 300912557604499114879921

theorem tailTrace_2637113 : CollatzResearch.WordTrace tailWord_2637113 prefixEnd_2637113 300912557604499114879921 := by
  unfold tailWord_2637113
  simp only [CollatzResearch.WordTrace]
  refine ⟨96183412895197458888683993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64122275263464972592455995 96183412895197458888683993)
  ·
    refine ⟨72137559671398094166512995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96183412895197458888683993 72137559671398094166512995)
    ·
      refine ⟨108206339507097141249769493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72137559671398094166512995 108206339507097141249769493)
      ·
        refine ⟨5072172164395178496082945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108206339507097141249769493 5072172164395178496082945)
        ·
          refine ⟨3804129123296383872062209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5072172164395178496082945 3804129123296383872062209)
          ·
            refine ⟨2853096842472287904046657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3804129123296383872062209 2853096842472287904046657)
            ·
              refine ⟨2139822631854215928034993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2853096842472287904046657 2139822631854215928034993)
              ·
                refine ⟨1604866973890661946026245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2139822631854215928034993 1604866973890661946026245)
                ·
                  refine ⟨300912557604499114879921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1604866973890661946026245 300912557604499114879921)
                  ·
                    rfl

theorem cell22_2637113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 4].length) (baseStart_2637113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637113 prefixEnd_2637113 := by exact prefixLift 2637113
  have htrace : WordTrace (prefixWord ++ tailWord_2637113) baseStart_2637113 baseEnd_2637113 := by
    simpa [prefixWord, tailWord_2637113, baseEnd_2637113] using wordTrace_append hprefix tailTrace_2637113
  have hstable : (prefixWord ++ tailWord_2637113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637113).length < 2 ^ (prefixWord ++ tailWord_2637113).sum := by decide
  have hdescent : baseEnd_2637113 < baseStart_2637113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637120 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 1, 8]
def baseStart_2637120 : Nat := 118140960795 + 2637120 * 2 ^ 59
def prefixEnd_2637120 : Nat := 4983230072969 + 3 ^ 40 * 2637120 * 2
def baseEnd_2637120 : Nat := 902740069056551659714741

theorem tailTrace_2637120 : CollatzResearch.WordTrace tailWord_2637120 prefixEnd_2637120 902740069056551659714741 := by
  unfold tailWord_2637120
  simp only [CollatzResearch.WordTrace]
  refine ⟨48091834103086049542094407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64122445470781399389459209 48091834103086049542094407)
  ·
    refine ⟨72137751154629074313141611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48091834103086049542094407 72137751154629074313141611)
    ·
      refine ⟨108206626731943611469712417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72137751154629074313141611 108206626731943611469712417)
      ·
        refine ⟨81154970048957708602284313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108206626731943611469712417 81154970048957708602284313)
        ·
          refine ⟨60866227536718281451713235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81154970048957708602284313 60866227536718281451713235)
          ·
            refine ⟨91299341305077422177569853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60866227536718281451713235 91299341305077422177569853)
            ·
              refine ⟨34237252989404033316588695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91299341305077422177569853 34237252989404033316588695)
              ·
                refine ⟨51355879484106049974883043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34237252989404033316588695 51355879484106049974883043)
                ·
                  refine ⟨77033819226159074962324565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51355879484106049974883043 77033819226159074962324565)
                  ·
                    refine ⟨902740069056551659714741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77033819226159074962324565 902740069056551659714741)
                    ·
                      rfl

theorem cell22_2637120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_2637120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637120 prefixEnd_2637120 := by exact prefixLift 2637120
  have htrace : WordTrace (prefixWord ++ tailWord_2637120) baseStart_2637120 baseEnd_2637120 := by
    simpa [prefixWord, tailWord_2637120, baseEnd_2637120] using wordTrace_append hprefix tailTrace_2637120
  have hstable : (prefixWord ++ tailWord_2637120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637120).length < 2 ^ (prefixWord ++ tailWord_2637120).sum := by decide
  have hdescent : baseEnd_2637120 < baseStart_2637120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637124 : List Nat := [2, 3, 4, 1, 1, 1, 3, 7]
def baseStart_2637124 : Nat := 118140960795 + 2637124 * 2 ^ 59
def prefixEnd_2637124 : Nat := 4983230072969 + 3 ^ 40 * 2637124 * 2
def baseEnd_2637124 : Nat := 100304604259810775846081

theorem tailTrace_2637124 : CollatzResearch.WordTrace tailWord_2637124 prefixEnd_2637124 100304604259810775846081 := by
  unfold tailWord_2637124
  simp only [CollatzResearch.WordTrace]
  refine ⟨48091907049078803883667213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64122542732105071844889617 48091907049078803883667213)
  ·
    refine ⟨18034465143404551456375205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48091907049078803883667213 18034465143404551456375205)
    ·
      refine ⟨3381462214388353398070351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18034465143404551456375205 3381462214388353398070351)
      ·
        refine ⟨5072193321582530097105527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3381462214388353398070351 5072193321582530097105527)
        ·
          refine ⟨7608289982373795145658291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5072193321582530097105527 7608289982373795145658291)
          ·
            refine ⟨11412434973560692718487437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7608289982373795145658291 11412434973560692718487437)
            ·
              refine ⟨4279663115085259769432789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11412434973560692718487437 4279663115085259769432789)
              ·
                refine ⟨100304604259810775846081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4279663115085259769432789 100304604259810775846081)
                ·
                  rfl

theorem cell22_2637124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 7].length) (baseStart_2637124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637124 prefixEnd_2637124 := by exact prefixLift 2637124
  have htrace : WordTrace (prefixWord ++ tailWord_2637124) baseStart_2637124 baseEnd_2637124 := by
    simpa [prefixWord, tailWord_2637124, baseEnd_2637124] using wordTrace_append hprefix tailTrace_2637124
  have hstable : (prefixWord ++ tailWord_2637124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637124).length < 2 ^ (prefixWord ++ tailWord_2637124).sum := by decide
  have hdescent : baseEnd_2637124 < baseStart_2637124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637156 : List Nat := [2, 3, 1, 1, 3, 2, 1, 5, 1, 3]
def baseStart_2637156 : Nat := 118140960795 + 2637156 * 2 ^ 59
def prefixEnd_2637156 : Nat := 4983230072969 + 3 ^ 40 * 2637156 * 2
def baseEnd_2637156 : Nat := 902752392592259565814631

theorem tailTrace_2637156 : CollatzResearch.WordTrace tailWord_2637156 prefixEnd_2637156 902752392592259565814631 := by
  unfold tailWord_2637156
  simp only [CollatzResearch.WordTrace]
  refine ⟨48092490617020838616249661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64123320822694451488332881 48092490617020838616249661)
  ·
    refine ⟨18034683981382814481093623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48092490617020838616249661 18034683981382814481093623)
    ·
      refine ⟨27052025972074221721640435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18034683981382814481093623 27052025972074221721640435)
      ·
        refine ⟨40578038958111332582460653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27052025972074221721640435 40578038958111332582460653)
        ·
          refine ⟨15216764609291749718422745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40578038958111332582460653 15216764609291749718422745)
          ·
            refine ⟨11412573456968812288817059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15216764609291749718422745 11412573456968812288817059)
            ·
              refine ⟨17118860185453218433225589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11412573456968812288817059 17118860185453218433225589)
              ·
                refine ⟨1604893142386239228114899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17118860185453218433225589 1604893142386239228114899)
                ·
                  refine ⟨2407339713579358842172349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1604893142386239228114899 2407339713579358842172349)
                  ·
                    refine ⟨902752392592259565814631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2407339713579358842172349 902752392592259565814631)
                    ·
                      rfl

theorem cell22_2637156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_2637156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637156 prefixEnd_2637156 := by exact prefixLift 2637156
  have htrace : WordTrace (prefixWord ++ tailWord_2637156) baseStart_2637156 baseEnd_2637156 := by
    simpa [prefixWord, tailWord_2637156, baseEnd_2637156] using wordTrace_append hprefix tailTrace_2637156
  have hstable : (prefixWord ++ tailWord_2637156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637156).length < 2 ^ (prefixWord ++ tailWord_2637156).sum := by decide
  have hdescent : baseEnd_2637156 < baseStart_2637156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637293 : List Nat := [1, 5, 1, 3, 3, 1, 1, 7]
def baseStart_2637293 : Nat := 118140960795 + 2637293 * 2 ^ 59
def prefixEnd_2637293 : Nat := 4983230072969 + 3 ^ 40 * 2637293 * 2
def baseEnd_2637293 : Nat := 100311032276892986126579

theorem tailTrace_2637293 : CollatzResearch.WordTrace tailWord_2637293 prefixEnd_2637293 100311032276892986126579 := by
  unfold tailWord_2637293
  simp only [CollatzResearch.WordTrace]
  refine ⟨96189978034545349630236533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64126652023030233086824355 96189978034545349630236533)
  ·
    refine ⟨9017810440738626527834675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96189978034545349630236533 9017810440738626527834675)
    ·
      refine ⟨13526715661107939791752013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9017810440738626527834675 13526715661107939791752013)
      ·
        refine ⟨5072518372915477421907005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13526715661107939791752013 5072518372915477421907005)
        ·
          refine ⟨1902194389843304033215127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5072518372915477421907005 1902194389843304033215127)
          ·
            refine ⟨2853291584764956049822691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902194389843304033215127 2853291584764956049822691)
            ·
              refine ⟨4279937377147434074734037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2853291584764956049822691 4279937377147434074734037)
              ·
                refine ⟨100311032276892986126579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4279937377147434074734037 100311032276892986126579)
                ·
                  rfl

theorem cell22_2637293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 7].length) (baseStart_2637293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637293 prefixEnd_2637293 := by exact prefixLift 2637293
  have htrace : WordTrace (prefixWord ++ tailWord_2637293) baseStart_2637293 baseEnd_2637293 := by
    simpa [prefixWord, tailWord_2637293, baseEnd_2637293] using wordTrace_append hprefix tailTrace_2637293
  have hstable : (prefixWord ++ tailWord_2637293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637293).length < 2 ^ (prefixWord ++ tailWord_2637293).sum := by decide
  have hdescent : baseEnd_2637293 < baseStart_2637293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637304 : List Nat := [2, 1, 2, 1, 1, 5, 2, 3, 5]
def baseStart_2637304 : Nat := 118140960795 + 2637304 * 2 ^ 59
def prefixEnd_2637304 : Nat := 4983230072969 + 3 ^ 40 * 2637304 * 2
def baseEnd_2637304 : Nat := 300934352005612171038059

theorem tailTrace_2637304 : CollatzResearch.WordTrace tailWord_2637304 prefixEnd_2637304 300934352005612171038059 := by
  unfold tailWord_2637304
  simp only [CollatzResearch.WordTrace]
  refine ⟨48095189618752749254443483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64126919491670332339257977 48095189618752749254443483)
  ·
    refine ⟨72142784428129123881665225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48095189618752749254443483 72142784428129123881665225)
    ·
      refine ⟨54107088321096842911248919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72142784428129123881665225 54107088321096842911248919)
      ·
        refine ⟨81160632481645264366873379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54107088321096842911248919 81160632481645264366873379)
        ·
          refine ⟨121740948722467896550310069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81160632481645264366873379 121740948722467896550310069)
          ·
            refine ⟨11413213942731365301591569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121740948722467896550310069 11413213942731365301591569)
            ·
              refine ⟨8559910457048523976193677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11413213942731365301591569 8559910457048523976193677)
              ·
                refine ⟨3209966421393196491072629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8559910457048523976193677 3209966421393196491072629)
                ·
                  refine ⟨300934352005612171038059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3209966421393196491072629 300934352005612171038059)
                  ·
                    rfl

theorem cell22_2637304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 5].length) (baseStart_2637304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637304 prefixEnd_2637304 := by exact prefixLift 2637304
  have htrace : WordTrace (prefixWord ++ tailWord_2637304) baseStart_2637304 baseEnd_2637304 := by
    simpa [prefixWord, tailWord_2637304, baseEnd_2637304] using wordTrace_append hprefix tailTrace_2637304
  have hstable : (prefixWord ++ tailWord_2637304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637304).length < 2 ^ (prefixWord ++ tailWord_2637304).sum := by decide
  have hdescent : baseEnd_2637304 < baseStart_2637304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637394 : List Nat := [3, 2, 2, 1, 2, 2, 10]
def baseStart_2637394 : Nat := 118140960795 + 2637394 * 2 ^ 59
def prefixEnd_2637394 : Nat := 4983230072969 + 3 ^ 40 * 2637394 * 2
def baseEnd_2637394 : Nat := 33438291290966899198663

theorem tailTrace_2637394 : CollatzResearch.WordTrace tailWord_2637394 prefixEnd_2637394 33438291290966899198663 := by
  unfold tailWord_2637394
  simp only [CollatzResearch.WordTrace]
  refine ⟨24048415451794860969915809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64129107871452962586442157 24048415451794860969915809)
  ·
    refine ⟨18036311588846145727436857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24048415451794860969915809 18036311588846145727436857)
    ·
      refine ⟨13527233691634609295577643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18036311588846145727436857 13527233691634609295577643)
      ·
        refine ⟨20290850537451913943366465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13527233691634609295577643 20290850537451913943366465)
        ·
          refine ⟨15218137903088935457524849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20290850537451913943366465 15218137903088935457524849)
          ·
            refine ⟨11413603427316701593143637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15218137903088935457524849 11413603427316701593143637)
            ·
              refine ⟨33438291290966899198663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11413603427316701593143637 33438291290966899198663)
              ·
                rfl

theorem cell22_2637394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 10].length) (baseStart_2637394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637394 prefixEnd_2637394 := by exact prefixLift 2637394
  have htrace : WordTrace (prefixWord ++ tailWord_2637394) baseStart_2637394 baseEnd_2637394 := by
    simpa [prefixWord, tailWord_2637394, baseEnd_2637394] using wordTrace_append hprefix tailTrace_2637394
  have hstable : (prefixWord ++ tailWord_2637394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637394).length < 2 ^ (prefixWord ++ tailWord_2637394).sum := by decide
  have hdescent : baseEnd_2637394 < baseStart_2637394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637396 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_2637396 : Nat := 118140960795 + 2637396 * 2 ^ 59
def prefixEnd_2637396 : Nat := 4983230072969 + 3 ^ 40 * 2637396 * 2
def baseEnd_2637396 : Nat := 902834549496978939813895

theorem tailTrace_2637396 : CollatzResearch.WordTrace tailWord_2637396 prefixEnd_2637396 902834549496978939813895 := by
  unfold tailWord_2637396
  simp only [CollatzResearch.WordTrace]
  refine ⟨48096867376586099110618021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64129156502114798814157361 48096867376586099110618021)
  ·
    refine ⟨9018162633109893583240879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48096867376586099110618021 9018162633109893583240879)
    ·
      refine ⟨13527243949664840374861319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9018162633109893583240879 13527243949664840374861319)
      ·
        refine ⟨20290865924497260562291979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13527243949664840374861319 20290865924497260562291979)
        ·
          refine ⟨30436298886745890843437969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20290865924497260562291979 30436298886745890843437969)
          ·
            refine ⟨22827224165059418132578477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30436298886745890843437969 22827224165059418132578477)
            ·
              refine ⟨8560209061897281799716929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22827224165059418132578477 8560209061897281799716929)
              ·
                refine ⟨6420156796422961349787697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8560209061897281799716929 6420156796422961349787697)
                ·
                  refine ⟨4815117597317221012340773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6420156796422961349787697 4815117597317221012340773)
                  ·
                    refine ⟨902834549496978939813895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4815117597317221012340773 902834549496978939813895)
                    ·
                      rfl

theorem cell22_2637396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_2637396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637396 prefixEnd_2637396 := by exact prefixLift 2637396
  have htrace : WordTrace (prefixWord ++ tailWord_2637396) baseStart_2637396 baseEnd_2637396 := by
    simpa [prefixWord, tailWord_2637396, baseEnd_2637396] using wordTrace_append hprefix tailTrace_2637396
  have hstable : (prefixWord ++ tailWord_2637396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637396).length < 2 ^ (prefixWord ++ tailWord_2637396).sum := by decide
  have hdescent : baseEnd_2637396 < baseStart_2637396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637443 : List Nat := [1, 1, 1, 3, 3, 1, 1, 7, 1, 3]
def baseStart_2637443 : Nat := 118140960795 + 2637443 * 2 ^ 59
def prefixEnd_2637443 : Nat := 4983230072969 + 3 ^ 40 * 2637443 * 2
def baseEnd_2637443 : Nat := 902850638557486483888751

theorem tailTrace_2637443 : CollatzResearch.WordTrace tailWord_2637443 prefixEnd_2637443 902850638557486483888751 := by
  unfold tailWord_2637443
  simp only [CollatzResearch.WordTrace]
  refine ⟨96195448984001925248196983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64130299322667950165464655 96195448984001925248196983)
  ·
    refine ⟨144293173476002887872295475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96195448984001925248196983 144293173476002887872295475)
    ·
      refine ⟨216439760214004331808443213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144293173476002887872295475 216439760214004331808443213)
      ·
        refine ⟨81164910080251624428166205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216439760214004331808443213 81164910080251624428166205)
        ·
          refine ⟨30436841280094359160562327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81164910080251624428166205 30436841280094359160562327)
          ·
            refine ⟨45655261920141538740843491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30436841280094359160562327 45655261920141538740843491)
            ·
              refine ⟨68482892880212308111265237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45655261920141538740843491 68482892880212308111265237)
              ·
                refine ⟨1605067801879975971357779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68482892880212308111265237 1605067801879975971357779)
                ·
                  refine ⟨2407601702819963957036669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605067801879975971357779 2407601702819963957036669)
                  ·
                    refine ⟨902850638557486483888751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2407601702819963957036669 902850638557486483888751)
                    ·
                      rfl

theorem cell22_2637443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 1, 3].length) (baseStart_2637443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637443 prefixEnd_2637443 := by exact prefixLift 2637443
  have htrace : WordTrace (prefixWord ++ tailWord_2637443) baseStart_2637443 baseEnd_2637443 := by
    simpa [prefixWord, tailWord_2637443, baseEnd_2637443] using wordTrace_append hprefix tailTrace_2637443
  have hstable : (prefixWord ++ tailWord_2637443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637443).length < 2 ^ (prefixWord ++ tailWord_2637443).sum := by decide
  have hdescent : baseEnd_2637443 < baseStart_2637443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637494 : List Nat := [5, 1, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2637494 : Nat := 118140960795 + 2637494 * 2 ^ 59
def prefixEnd_2637494 : Nat := 4983230072969 + 3 ^ 40 * 2637494 * 2
def baseEnd_2637494 : Nat := 902868096899739350863595

theorem tailTrace_2637494 : CollatzResearch.WordTrace tailWord_2637494 prefixEnd_2637494 902868096899739350863595 := by
  unfold tailWord_2637494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6012331819176072559893971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64131539404544773972202357 6012331819176072559893971)
  ·
    refine ⟨9018497728764108839840957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6012331819176072559893971 9018497728764108839840957)
    ·
      refine ⟨3381936648286540814940359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9018497728764108839840957 3381936648286540814940359)
      ·
        refine ⟨5072904972429811222410539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3381936648286540814940359 5072904972429811222410539)
        ·
          refine ⟨7609357458644716833615809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5072904972429811222410539 7609357458644716833615809)
          ·
            refine ⟨5707018093983537625211857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7609357458644716833615809 5707018093983537625211857)
            ·
              refine ⟨4280263570487653218908893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5707018093983537625211857 4280263570487653218908893)
              ·
                refine ⟨1605098838932869957090835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4280263570487653218908893 1605098838932869957090835)
                ·
                  refine ⟨2407648258399304935636253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605098838932869957090835 2407648258399304935636253)
                  ·
                    refine ⟨902868096899739350863595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2407648258399304935636253 902868096899739350863595)
                    ·
                      rfl

theorem cell22_2637494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2637494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637494 prefixEnd_2637494 := by exact prefixLift 2637494
  have htrace : WordTrace (prefixWord ++ tailWord_2637494) baseStart_2637494 baseEnd_2637494 := by
    simpa [prefixWord, tailWord_2637494, baseEnd_2637494] using wordTrace_append hprefix tailTrace_2637494
  have hstable : (prefixWord ++ tailWord_2637494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637494).length < 2 ^ (prefixWord ++ tailWord_2637494).sum := by decide
  have hdescent : baseEnd_2637494 < baseStart_2637494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637518 : List Nat := [4, 1, 1, 1, 3, 1, 1, 6, 4]
def baseStart_2637518 : Nat := 118140960795 + 2637518 * 2 ^ 59
def prefixEnd_2637518 : Nat := 4983230072969 + 3 ^ 40 * 2637518 * 2
def baseEnd_2637518 : Nat := 300958770863403762754507

theorem tailTrace_2637518 : CollatzResearch.WordTrace tailWord_2637518 prefixEnd_2637518 300958770863403762754507 := by
  unfold tailWord_2637518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12024773057341276632147151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64132122972486808704784805 12024773057341276632147151)
  ·
    refine ⟨18037159586011914948220727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12024773057341276632147151 18037159586011914948220727)
    ·
      refine ⟨27055739379017872422331091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18037159586011914948220727 27055739379017872422331091)
      ·
        refine ⟨40583609068526808633496637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27055739379017872422331091 40583609068526808633496637)
        ·
          refine ⟨15218853400697553237561239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40583609068526808633496637 15218853400697553237561239)
          ·
            refine ⟨22828280101046329856341859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15218853400697553237561239 22828280101046329856341859)
            ·
              refine ⟨34242420151569494784512789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22828280101046329856341859 34242420151569494784512789)
              ·
                refine ⟨1605113444604820068024037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34242420151569494784512789 1605113444604820068024037)
                ·
                  refine ⟨300958770863403762754507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1605113444604820068024037 300958770863403762754507)
                  ·
                    rfl

theorem cell22_2637518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_2637518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637518 prefixEnd_2637518 := by exact prefixLift 2637518
  have htrace : WordTrace (prefixWord ++ tailWord_2637518) baseStart_2637518 baseEnd_2637518 := by
    simpa [prefixWord, tailWord_2637518, baseEnd_2637518] using wordTrace_append hprefix tailTrace_2637518
  have hstable : (prefixWord ++ tailWord_2637518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637518).length < 2 ^ (prefixWord ++ tailWord_2637518).sum := by decide
  have hdescent : baseEnd_2637518 < baseStart_2637518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637576 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 2, 6]
def baseStart_2637576 : Nat := 118140960795 + 2637576 * 2 ^ 59
def prefixEnd_2637576 : Nat := 4983230072969 + 3 ^ 40 * 2637576 * 2
def baseEnd_2637576 : Nat := 902896167175518470313343

theorem tailTrace_2637576 : CollatzResearch.WordTrace tailWord_2637576 prefixEnd_2637576 902896167175518470313343 := by
  unfold tailWord_2637576
  simp only [CollatzResearch.WordTrace]
  refine ⟨48100149946260044481394291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64133533261680059308525721 48100149946260044481394291)
  ·
    refine ⟨72150224919390066722091437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48100149946260044481394291 72150224919390066722091437)
    ·
      refine ⟨27056334344771275020784289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72150224919390066722091437 27056334344771275020784289)
      ·
        refine ⟨20292250758578456265588217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27056334344771275020784289 20292250758578456265588217)
        ·
          refine ⟨15219188068933842199191163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20292250758578456265588217 15219188068933842199191163)
          ·
            refine ⟨22828782103400763298786745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15219188068933842199191163 22828782103400763298786745)
            ·
              refine ⟨17121586577550572474090059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22828782103400763298786745 17121586577550572474090059)
              ·
                refine ⟨25682379866325858711135089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17121586577550572474090059 25682379866325858711135089)
                ·
                  refine ⟨19261784899744394033351317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25682379866325858711135089 19261784899744394033351317)
                  ·
                    refine ⟨902896167175518470313343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19261784899744394033351317 902896167175518470313343)
                    ·
                      rfl

theorem cell22_2637576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_2637576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637576 prefixEnd_2637576 := by exact prefixLift 2637576
  have htrace : WordTrace (prefixWord ++ tailWord_2637576) baseStart_2637576 baseEnd_2637576 := by
    simpa [prefixWord, tailWord_2637576, baseEnd_2637576] using wordTrace_append hprefix tailTrace_2637576
  have hstable : (prefixWord ++ tailWord_2637576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637576).length < 2 ^ (prefixWord ++ tailWord_2637576).sum := by decide
  have hdescent : baseEnd_2637576 < baseStart_2637576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637629 : List Nat := [1, 4, 1, 4, 1, 1, 4, 2, 1, 3]
def baseStart_2637629 : Nat := 118140960795 + 2637629 * 2 ^ 59
def prefixEnd_2637629 : Nat := 4983230072969 + 3 ^ 40 * 2637629 * 2
def baseEnd_2637629 : Nat := 902914310158643998738181

theorem tailTrace_2637629 : CollatzResearch.WordTrace tailWord_2637629 prefixEnd_2637629 902914310158643998738181 := by
  unfold tailWord_2637629
  simp only [CollatzResearch.WordTrace]
  refine ⟨96202232961328079014467941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64134821974218719342978627 96202232961328079014467941)
  ·
    refine ⟨18037918680249014815212739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96202232961328079014467941 18037918680249014815212739)
    ·
      refine ⟨27056878020373522222819109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18037918680249014815212739 27056878020373522222819109)
      ·
        refine ⟨5073164628820035416778583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27056878020373522222819109 5073164628820035416778583)
        ·
          refine ⟨7609746943230053125167875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5073164628820035416778583 7609746943230053125167875)
          ·
            refine ⟨11414620414845079687751813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7609746943230053125167875 11414620414845079687751813)
            ·
              refine ⟨2140241327783452441453465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11414620414845079687751813 2140241327783452441453465)
              ·
                refine ⟨1605180995837589331090099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2140241327783452441453465 1605180995837589331090099)
                ·
                  refine ⟨2407771493756383996635149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605180995837589331090099 2407771493756383996635149)
                  ·
                    refine ⟨902914310158643998738181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2407771493756383996635149 902914310158643998738181)
                    ·
                      rfl

theorem cell22_2637629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_2637629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637629 prefixEnd_2637629 := by exact prefixLift 2637629
  have htrace : WordTrace (prefixWord ++ tailWord_2637629) baseStart_2637629 baseEnd_2637629 := by
    simpa [prefixWord, tailWord_2637629, baseEnd_2637629] using wordTrace_append hprefix tailTrace_2637629
  have hstable : (prefixWord ++ tailWord_2637629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637629).length < 2 ^ (prefixWord ++ tailWord_2637629).sum := by decide
  have hdescent : baseEnd_2637629 < baseStart_2637629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637653 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 6]
def baseStart_2637653 : Nat := 118140960795 + 2637653 * 2 ^ 59
def prefixEnd_2637653 : Nat := 4983230072969 + 3 ^ 40 * 2637653 * 2
def baseEnd_2637653 : Nat := 300974175283038645379369

theorem tailTrace_2637653 : CollatzResearch.WordTrace tailWord_2637653 prefixEnd_2637653 300974175283038645379369 := by
  unfold tailWord_2637653
  simp only [CollatzResearch.WordTrace]
  refine ⟨96203108313241131113341613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64135405542160754075561075 96203108313241131113341613)
  ·
    refine ⟨36076165617465424167503105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96203108313241131113341613 36076165617465424167503105)
    ·
      refine ⟨27057124213099068125627329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36076165617465424167503105 27057124213099068125627329)
      ·
        refine ⟨20292843159824301094220497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27057124213099068125627329 20292843159824301094220497)
        ·
          refine ⟨15219632369868225820665373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20292843159824301094220497 15219632369868225820665373)
          ·
            refine ⟨5707362138700584682749515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15219632369868225820665373 5707362138700584682749515)
            ·
              refine ⟨8561043208050877024124273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5707362138700584682749515 8561043208050877024124273)
              ·
                refine ⟨6420782406038157768093205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8561043208050877024124273 6420782406038157768093205)
                ·
                  refine ⟨300974175283038645379369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6420782406038157768093205 300974175283038645379369)
                  ·
                    rfl

theorem cell22_2637653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_2637653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637653 prefixEnd_2637653 := by exact prefixLift 2637653
  have htrace : WordTrace (prefixWord ++ tailWord_2637653) baseStart_2637653 baseEnd_2637653 := by
    simpa [prefixWord, tailWord_2637653, baseEnd_2637653] using wordTrace_append hprefix tailTrace_2637653
  have hstable : (prefixWord ++ tailWord_2637653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637653).length < 2 ^ (prefixWord ++ tailWord_2637653).sum := by decide
  have hdescent : baseEnd_2637653 < baseStart_2637653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637681 : List Nat := [1, 2, 2, 2, 1, 3, 11]
def baseStart_2637681 : Nat := 118140960795 + 2637681 * 2 ^ 59
def prefixEnd_2637681 : Nat := 4983230072969 + 3 ^ 40 * 2637681 * 2
def baseEnd_2637681 : Nat := 33441930030419748016223

theorem tailTrace_2637681 : CollatzResearch.WordTrace tailWord_2637681 prefixEnd_2637681 33441930030419748016223 := by
  unfold tailWord_2637681
  simp only [CollatzResearch.WordTrace]
  refine ⟨96204129557139691895360897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64136086371426461263573931 96204129557139691895360897)
  ·
    refine ⟨72153097167854768921520673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96204129557139691895360897 72153097167854768921520673)
    ·
      refine ⟨54114822875891076691140505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72153097167854768921520673 54114822875891076691140505)
      ·
        refine ⟨40586117156918307518355379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54114822875891076691140505 40586117156918307518355379)
        ·
          refine ⟨60879175735377461277533069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40586117156918307518355379 60879175735377461277533069)
          ·
            refine ⟨22829690900766547979074901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60879175735377461277533069 22829690900766547979074901)
            ·
              refine ⟨33441930030419748016223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22829690900766547979074901 33441930030419748016223)
              ·
                rfl

theorem cell22_2637681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 11].length) (baseStart_2637681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637681 prefixEnd_2637681 := by exact prefixLift 2637681
  have htrace : WordTrace (prefixWord ++ tailWord_2637681) baseStart_2637681 baseEnd_2637681 := by
    simpa [prefixWord, tailWord_2637681, baseEnd_2637681] using wordTrace_append hprefix tailTrace_2637681
  have hstable : (prefixWord ++ tailWord_2637681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637681).length < 2 ^ (prefixWord ++ tailWord_2637681).sum := by decide
  have hdescent : baseEnd_2637681 < baseStart_2637681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637685 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 4, 3]
def baseStart_2637685 : Nat := 118140960795 + 2637685 * 2 ^ 59
def prefixEnd_2637685 : Nat := 4983230072969 + 3 ^ 40 * 2637685 * 2
def baseEnd_2637685 : Nat := 902933480103078519338009

theorem tailTrace_2637685 : CollatzResearch.WordTrace tailWord_2637685 prefixEnd_2637685 902933480103078519338009 := by
  unfold tailWord_2637685
  simp only [CollatzResearch.WordTrace]
  refine ⟨96204275449125200578506509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64136183632750133719004339 96204275449125200578506509)
  ·
    refine ⟨36076603293421950216939941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96204275449125200578506509 36076603293421950216939941)
    ·
      refine ⟨6764363117516615665676239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36076603293421950216939941 6764363117516615665676239)
      ·
        refine ⟨10146544676274923498514359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6764363117516615665676239 10146544676274923498514359)
        ·
          refine ⟨15219817014412385247771539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10146544676274923498514359 15219817014412385247771539)
          ·
            refine ⟨22829725521618577871657309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15219817014412385247771539 22829725521618577871657309)
            ·
              refine ⟨8561147070606966701871491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22829725521618577871657309 8561147070606966701871491)
              ·
                refine ⟨12841720605910450052807237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8561147070606966701871491 12841720605910450052807237)
                ·
                  refine ⟨2407822613608209384901357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12841720605910450052807237 2407822613608209384901357)
                  ·
                    refine ⟨902933480103078519338009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2407822613608209384901357 902933480103078519338009)
                    ·
                      rfl

theorem cell22_2637685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_2637685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637685 prefixEnd_2637685 := by exact prefixLift 2637685
  have htrace : WordTrace (prefixWord ++ tailWord_2637685) baseStart_2637685 baseEnd_2637685 := by
    simpa [prefixWord, tailWord_2637685, baseEnd_2637685] using wordTrace_append hprefix tailTrace_2637685
  have hstable : (prefixWord ++ tailWord_2637685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637685).length < 2 ^ (prefixWord ++ tailWord_2637685).sum := by decide
  have hdescent : baseEnd_2637685 < baseStart_2637685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637711 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 5, 8]
def baseStart_2637711 : Nat := 118140960795 + 2637711 * 2 ^ 59
def prefixEnd_2637711 : Nat := 4983230072969 + 3 ^ 40 * 2637711 * 2
def baseEnd_2637711 : Nat := 902942380434423118187929

theorem tailTrace_2637711 : CollatzResearch.WordTrace tailWord_2637711 prefixEnd_2637711 902942380434423118187929 := by
  unfold tailWord_2637711
  simp only [CollatzResearch.WordTrace]
  refine ⟨96205223747031007018952987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64136815831354004679301991 96205223747031007018952987)
  ·
    refine ⟨144307835620546510528429481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96205223747031007018952987 144307835620546510528429481)
    ·
      refine ⟨108230876715409882896322111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144307835620546510528429481 108230876715409882896322111)
      ·
        refine ⟨162346315073114824344483167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108230876715409882896322111 162346315073114824344483167)
        ·
          refine ⟨243519472609672236516724751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162346315073114824344483167 243519472609672236516724751)
          ·
            refine ⟨365279208914508354775087127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243519472609672236516724751 365279208914508354775087127)
            ·
              refine ⟨547918813371762532162630691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365279208914508354775087127 547918813371762532162630691)
              ·
                refine ⟨821878220057643798243946037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547918813371762532162630691 821878220057643798243946037)
                ·
                  refine ⟨77051083130404106085369941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 821878220057643798243946037 77051083130404106085369941)
                  ·
                    refine ⟨902942380434423118187929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77051083130404106085369941 902942380434423118187929)
                    ·
                      rfl

theorem cell22_2637711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_2637711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637711 prefixEnd_2637711 := by exact prefixLift 2637711
  have htrace : WordTrace (prefixWord ++ tailWord_2637711) baseStart_2637711 baseEnd_2637711 := by
    simpa [prefixWord, tailWord_2637711, baseEnd_2637711] using wordTrace_append hprefix tailTrace_2637711
  have hstable : (prefixWord ++ tailWord_2637711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637711).length < 2 ^ (prefixWord ++ tailWord_2637711).sum := by decide
  have hdescent : baseEnd_2637711 < baseStart_2637711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637743 : List Nat := [1, 1, 2, 1, 2, 2, 4, 4, 5]
def baseStart_2637743 : Nat := 118140960795 + 2637743 * 2 ^ 59
def prefixEnd_2637743 : Nat := 4983230072969 + 3 ^ 40 * 2637743 * 2
def baseEnd_2637743 : Nat := 300984444896128567129277

theorem tailTrace_2637743 : CollatzResearch.WordTrace tailWord_2637743 prefixEnd_2637743 300984444896128567129277 := by
  unfold tailWord_2637743
  simp only [CollatzResearch.WordTrace]
  refine ⟨96206390882915076484117883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64137593921943384322745255 96206390882915076484117883)
  ·
    refine ⟨144309586324372614726176825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96206390882915076484117883 144309586324372614726176825)
    ·
      refine ⟨108232189743279461044632619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144309586324372614726176825 108232189743279461044632619)
      ·
        refine ⟨162348284614919191566948929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108232189743279461044632619 162348284614919191566948929)
        ·
          refine ⟨121761213461189393675211697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162348284614919191566948929 121761213461189393675211697)
          ·
            refine ⟨91320910095892045256408773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121761213461189393675211697 91320910095892045256408773)
            ·
              refine ⟨17122670642979758485576645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91320910095892045256408773 17122670642979758485576645)
              ·
                refine ⟨3210500745558704716045621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17122670642979758485576645 3210500745558704716045621)
                ·
                  refine ⟨300984444896128567129277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3210500745558704716045621 300984444896128567129277)
                  ·
                    rfl

theorem cell22_2637743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 5].length) (baseStart_2637743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637743 prefixEnd_2637743 := by exact prefixLift 2637743
  have htrace : WordTrace (prefixWord ++ tailWord_2637743) baseStart_2637743 baseEnd_2637743 := by
    simpa [prefixWord, tailWord_2637743, baseEnd_2637743] using wordTrace_append hprefix tailTrace_2637743
  have hstable : (prefixWord ++ tailWord_2637743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637743).length < 2 ^ (prefixWord ++ tailWord_2637743).sum := by decide
  have hdescent : baseEnd_2637743 < baseStart_2637743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637794 : List Nat := [3, 3, 3, 1, 2, 1, 2, 2, 5]
def baseStart_2637794 : Nat := 118140960795 + 2637794 * 2 ^ 59
def prefixEnd_2637794 : Nat := 4983230072969 + 3 ^ 40 * 2637794 * 2
def baseEnd_2637794 : Nat := 300990264343546189454225

theorem tailTrace_2637794 : CollatzResearch.WordTrace tailWord_2637794 prefixEnd_2637794 300990264343546189454225 := by
  unfold tailWord_2637794
  simp only [CollatzResearch.WordTrace]
  refine ⟨24052062751432578048556109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64138834003820208129482957 24052062751432578048556109)
  ·
    refine ⟨9019523531787216768208541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24052062751432578048556109 9019523531787216768208541)
    ·
      refine ⟨3382321324420206288078203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9019523531787216768208541 3382321324420206288078203)
      ·
        refine ⟨5073481986630309432117305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3382321324420206288078203 5073481986630309432117305)
        ·
          refine ⟨3805111489972732074087979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5073481986630309432117305 3805111489972732074087979)
          ·
            refine ⟨5707667234959098111131969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3805111489972732074087979 5707667234959098111131969)
            ·
              refine ⟨4280750426219323583348977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5707667234959098111131969 4280750426219323583348977)
              ·
                refine ⟨3210562819664492687511733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4280750426219323583348977 3210562819664492687511733)
                ·
                  refine ⟨300990264343546189454225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3210562819664492687511733 300990264343546189454225)
                  ·
                    rfl

theorem cell22_2637794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_2637794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637794 prefixEnd_2637794 := by exact prefixLift 2637794
  have htrace : WordTrace (prefixWord ++ tailWord_2637794) baseStart_2637794 baseEnd_2637794 := by
    simpa [prefixWord, tailWord_2637794, baseEnd_2637794] using wordTrace_append hprefix tailTrace_2637794
  have hstable : (prefixWord ++ tailWord_2637794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637794).length < 2 ^ (prefixWord ++ tailWord_2637794).sum := by decide
  have hdescent : baseEnd_2637794 < baseStart_2637794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637820 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 1, 5]
def baseStart_2637820 : Nat := 118140960795 + 2637820 * 2 ^ 59
def prefixEnd_2637820 : Nat := 4983230072969 + 3 ^ 40 * 2637820 * 2
def baseEnd_2637820 : Nat := 902979693361983167212595

theorem tailTrace_2637820 : CollatzResearch.WordTrace tailWord_2637820 prefixEnd_2637820 902979693361983167212595 := by
  unfold tailWord_2637820
  simp only [CollatzResearch.WordTrace]
  refine ⟨48104599651818059317335457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64139466202424079089780609 48104599651818059317335457)
  ·
    refine ⟨36078449738863544488001593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48104599651818059317335457 36078449738863544488001593)
    ·
      refine ⟨27058837304147658366001195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36078449738863544488001593 27058837304147658366001195)
      ·
        refine ⟨40588255956221487549001793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27058837304147658366001195 40588255956221487549001793)
        ·
          refine ⟨30441191967166115661751345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40588255956221487549001793 30441191967166115661751345)
          ·
            refine ⟨22830893975374586746313509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30441191967166115661751345 22830893975374586746313509)
            ·
              refine ⟨4280792620382735014933783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22830893975374586746313509 4280792620382735014933783)
              ·
                refine ⟨6421188930574102522400675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4280792620382735014933783 6421188930574102522400675)
                ·
                  refine ⟨9631783395861153783601013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6421188930574102522400675 9631783395861153783601013)
                  ·
                    refine ⟨902979693361983167212595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9631783395861153783601013 902979693361983167212595)
                    ·
                      rfl

theorem cell22_2637820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_2637820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637820 prefixEnd_2637820 := by exact prefixLift 2637820
  have htrace : WordTrace (prefixWord ++ tailWord_2637820) baseStart_2637820 baseEnd_2637820 := by
    simpa [prefixWord, tailWord_2637820, baseEnd_2637820] using wordTrace_append hprefix tailTrace_2637820
  have hstable : (prefixWord ++ tailWord_2637820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637820).length < 2 ^ (prefixWord ++ tailWord_2637820).sum := by decide
  have hdescent : baseEnd_2637820 < baseStart_2637820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637822 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_2637822 : Nat := 118140960795 + 2637822 * 2 ^ 59
def prefixEnd_2637822 : Nat := 4983230072969 + 3 ^ 40 * 2637822 * 2
def baseEnd_2637822 : Nat := 300993459334285276220863

theorem tailTrace_2637822 : CollatzResearch.WordTrace tailWord_2637822 prefixEnd_2637822 300993459334285276220863 := by
  unfold tailWord_2637822
  simp only [CollatzResearch.WordTrace]
  refine ⟨12026159031203609122030465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64139514833085915317495813 12026159031203609122030465)
  ·
    refine ⟨9019619273402706841522849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12026159031203609122030465 9019619273402706841522849)
    ·
      refine ⟨6764714455052030131142137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9019619273402706841522849 6764714455052030131142137)
      ·
        refine ⟨5073535841289022598356603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6764714455052030131142137 5073535841289022598356603)
        ·
          refine ⟨7610303761933533897534905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5073535841289022598356603 7610303761933533897534905)
          ·
            refine ⟨5707727821450150423151179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7610303761933533897534905 5707727821450150423151179)
            ·
              refine ⟨8561591732175225634726769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5707727821450150423151179 8561591732175225634726769)
              ·
                refine ⟨6421193799131419226045077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8561591732175225634726769 6421193799131419226045077)
                ·
                  refine ⟨300993459334285276220863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6421193799131419226045077 300993459334285276220863)
                  ·
                    rfl

theorem cell22_2637822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_2637822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637822 prefixEnd_2637822 := by exact prefixLift 2637822
  have htrace : WordTrace (prefixWord ++ tailWord_2637822) baseStart_2637822 baseEnd_2637822 := by
    simpa [prefixWord, tailWord_2637822, baseEnd_2637822] using wordTrace_append hprefix tailTrace_2637822
  have hstable : (prefixWord ++ tailWord_2637822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637822).length < 2 ^ (prefixWord ++ tailWord_2637822).sum := by decide
  have hdescent : baseEnd_2637822 < baseStart_2637822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637955 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 3, 5]
def baseStart_2637955 : Nat := 118140960795 + 2637955 * 2 ^ 59
def prefixEnd_2637955 : Nat := 4983230072969 + 3 ^ 40 * 2637955 * 2
def baseEnd_2637955 : Nat := 903025906620887815087181

theorem tailTrace_2637955 : CollatzResearch.WordTrace tailWord_2637955 prefixEnd_2637955 903025906620887815087181 := by
  unfold tailWord_2637955
  simp only [CollatzResearch.WordTrace]
  refine ⟨96214123158147036690835319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64142748772098024460556879 96214123158147036690835319)
  ·
    refine ⟨144321184737220555036252979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96214123158147036690835319 144321184737220555036252979)
    ·
      refine ⟨216481777105830832554379469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144321184737220555036252979 216481777105830832554379469)
      ·
        refine ⟨81180666414686562207892301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216481777105830832554379469 81180666414686562207892301)
        ·
          refine ⟨30442749905507460827959613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81180666414686562207892301 30442749905507460827959613)
          ·
            refine ⟨11416031214565297810484855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30442749905507460827959613 11416031214565297810484855)
            ·
              refine ⟨17124046821847946715727283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11416031214565297810484855 17124046821847946715727283)
              ·
                refine ⟨25686070232771920073590925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17124046821847946715727283 25686070232771920073590925)
                ·
                  refine ⟨9632276337289470027596597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25686070232771920073590925 9632276337289470027596597)
                  ·
                    refine ⟨903025906620887815087181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9632276337289470027596597 903025906620887815087181)
                    ·
                      rfl

theorem cell22_2637955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 5].length) (baseStart_2637955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637955 prefixEnd_2637955 := by exact prefixLift 2637955
  have htrace : WordTrace (prefixWord ++ tailWord_2637955) baseStart_2637955 baseEnd_2637955 := by
    simpa [prefixWord, tailWord_2637955, baseEnd_2637955] using wordTrace_append hprefix tailTrace_2637955
  have hstable : (prefixWord ++ tailWord_2637955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637955).length < 2 ^ (prefixWord ++ tailWord_2637955).sum := by decide
  have hdescent : baseEnd_2637955 < baseStart_2637955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638002 : List Nat := [3, 2, 1, 1, 1, 3, 5, 6]
def baseStart_2638002 : Nat := 118140960795 + 2638002 * 2 ^ 59
def prefixEnd_2638002 : Nat := 4983230072969 + 3 ^ 40 * 2638002 * 2
def baseEnd_2638002 : Nat := 100337999520155039906893

theorem tailTrace_2638002 : CollatzResearch.WordTrace tailWord_2638002 prefixEnd_2638002 100337999520155039906893 := by
  unfold tailWord_2638002
  simp only [CollatzResearch.WordTrace]
  refine ⟨24053959347244190929449065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64143891592651175811864173 24053959347244190929449065)
  ·
    refine ⟨18040469510433143197086799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24053959347244190929449065 18040469510433143197086799)
    ·
      refine ⟨27060704265649714795630199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18040469510433143197086799 27060704265649714795630199)
      ·
        refine ⟨40591056398474572193445299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27060704265649714795630199 40591056398474572193445299)
        ·
          refine ⟨60886584597711858290167949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40591056398474572193445299 60886584597711858290167949)
          ·
            refine ⟨22832469224141946858812981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60886584597711858290167949 22832469224141946858812981)
            ·
              refine ⟨2140543989763307518013717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22832469224141946858812981 2140543989763307518013717)
              ·
                refine ⟨100337999520155039906893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2140543989763307518013717 100337999520155039906893)
                ·
                  rfl

theorem cell22_2638002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 6].length) (baseStart_2638002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638002 prefixEnd_2638002 := by exact prefixLift 2638002
  have htrace : WordTrace (prefixWord ++ tailWord_2638002) baseStart_2638002 baseEnd_2638002 := by
    simpa [prefixWord, tailWord_2638002, baseEnd_2638002] using wordTrace_append hprefix tailTrace_2638002
  have hstable : (prefixWord ++ tailWord_2638002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638002).length < 2 ^ (prefixWord ++ tailWord_2638002).sum := by decide
  have hdescent : baseEnd_2638002 < baseStart_2638002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638034 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 3, 3]
def baseStart_2638034 : Nat := 118140960795 + 2638034 * 2 ^ 59
def prefixEnd_2638034 : Nat := 4983230072969 + 3 ^ 40 * 2638034 * 2
def baseEnd_2638034 : Nat := 903052949935357942361939

theorem tailTrace_2638034 : CollatzResearch.WordTrace tailWord_2638034 prefixEnd_2638034 903052949935357942361939 := by
  unfold tailWord_2638034
  simp only [CollatzResearch.WordTrace]
  refine ⟨24054251131215208295740289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64144669683240555455307437 24054251131215208295740289)
  ·
    refine ⟨18040688348411406221805217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24054251131215208295740289 18040688348411406221805217)
    ·
      refine ⟨13530516261308554666353913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18040688348411406221805217 13530516261308554666353913)
      ·
        refine ⟨10147887195981415999765435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13530516261308554666353913 10147887195981415999765435)
        ·
          refine ⟨15221830793972123999648153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10147887195981415999765435 15221830793972123999648153)
          ·
            refine ⟨11416373095479092999736115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15221830793972123999648153 11416373095479092999736115)
            ·
              refine ⟨17124559643218639499604173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11416373095479092999736115 17124559643218639499604173)
              ·
                refine ⟨6421709866206989812351565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17124559643218639499604173 6421709866206989812351565)
                ·
                  refine ⟨2408141199827621179631837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6421709866206989812351565 2408141199827621179631837)
                  ·
                    refine ⟨903052949935357942361939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2408141199827621179631837 903052949935357942361939)
                    ·
                      rfl

theorem cell22_2638034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_2638034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638034 prefixEnd_2638034 := by exact prefixLift 2638034
  have htrace : WordTrace (prefixWord ++ tailWord_2638034) baseStart_2638034 baseEnd_2638034 := by
    simpa [prefixWord, tailWord_2638034, baseEnd_2638034] using wordTrace_append hprefix tailTrace_2638034
  have hstable : (prefixWord ++ tailWord_2638034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638034).length < 2 ^ (prefixWord ++ tailWord_2638034).sum := by decide
  have hdescent : baseEnd_2638034 < baseStart_2638034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638111 : List Nat := [1, 1, 2, 4, 3, 3, 1, 2, 1, 4]
def baseStart_2638111 : Nat := 118140960795 + 2638111 * 2 ^ 59
def prefixEnd_2638111 : Nat := 4983230072969 + 3 ^ 40 * 2638111 * 2
def baseEnd_2638111 : Nat := 903079308608955408186703

theorem tailTrace_2638111 : CollatzResearch.WordTrace tailWord_2638111 prefixEnd_2638111 903079308608955408186703 := by
  unfold tailWord_2638111
  simp only [CollatzResearch.WordTrace]
  refine ⟨96219812945581875333514187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64146541963721250222342791 96219812945581875333514187)
  ·
    refine ⟨144329719418372813000271281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96219812945581875333514187 144329719418372813000271281)
    ·
      refine ⟨108247289563779609750203461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144329719418372813000271281 108247289563779609750203461)
      ·
        refine ⟨20296366793208676828163149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108247289563779609750203461 20296366793208676828163149)
        ·
          refine ⟨7611137547453253810561181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20296366793208676828163149 7611137547453253810561181)
          ·
            refine ⟨2854176580294970178960443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7611137547453253810561181 2854176580294970178960443)
            ·
              refine ⟨4281264870442455268440665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2854176580294970178960443 4281264870442455268440665)
              ·
                refine ⟨3210948652831841451330499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4281264870442455268440665 3210948652831841451330499)
                ·
                  refine ⟨4816422979247762176995749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3210948652831841451330499 4816422979247762176995749)
                  ·
                    refine ⟨903079308608955408186703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4816422979247762176995749 903079308608955408186703)
                    ·
                      rfl

theorem cell22_2638111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 4].length) (baseStart_2638111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638111 prefixEnd_2638111 := by exact prefixLift 2638111
  have htrace : WordTrace (prefixWord ++ tailWord_2638111) baseStart_2638111 baseEnd_2638111 := by
    simpa [prefixWord, tailWord_2638111, baseEnd_2638111] using wordTrace_append hprefix tailTrace_2638111
  have hstable : (prefixWord ++ tailWord_2638111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638111).length < 2 ^ (prefixWord ++ tailWord_2638111).sum := by decide
  have hdescent : baseEnd_2638111 < baseStart_2638111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638137 : List Nat := [1, 2, 1, 6, 1, 11]
def baseStart_2638137 : Nat := 118140960795 + 2638137 * 2 ^ 59
def prefixEnd_2638137 : Nat := 4983230072969 + 3 ^ 40 * 2638137 * 2
def baseEnd_2638137 : Nat := 11149237147411111197983

theorem tailTrace_2638137 : CollatzResearch.WordTrace tailWord_2638137 prefixEnd_2638137 11149237147411111197983 := by
  unfold tailWord_2638137
  simp only [CollatzResearch.WordTrace]
  refine ⟨96220761243487681773960665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64147174162325121182640443 96220761243487681773960665)
  ·
    refine ⟨72165570932615761330470499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96220761243487681773960665 72165570932615761330470499)
    ·
      refine ⟨108248356398923641995705749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72165570932615761330470499 108248356398923641995705749)
      ·
        refine ⟨5074141706199545718548707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108248356398923641995705749 5074141706199545718548707)
        ·
          refine ⟨7611212559299318577823061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5074141706199545718548707 7611212559299318577823061)
          ·
            refine ⟨11149237147411111197983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7611212559299318577823061 11149237147411111197983)
            ·
              rfl

theorem cell22_2638137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 11].length) (baseStart_2638137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638137 prefixEnd_2638137 := by exact prefixLift 2638137
  have htrace : WordTrace (prefixWord ++ tailWord_2638137) baseStart_2638137 baseEnd_2638137 := by
    simpa [prefixWord, tailWord_2638137, baseEnd_2638137] using wordTrace_append hprefix tailTrace_2638137
  have hstable : (prefixWord ++ tailWord_2638137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638137).length < 2 ^ (prefixWord ++ tailWord_2638137).sum := by decide
  have hdescent : baseEnd_2638137 < baseStart_2638137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638167 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 2, 6]
def baseStart_2638167 : Nat := 118140960795 + 2638167 * 2 ^ 59
def prefixEnd_2638167 : Nat := 4983230072969 + 3 ^ 40 * 2638167 * 2
def baseEnd_2638167 : Nat := 903098478553389928786531

theorem tailTrace_2638167 : CollatzResearch.WordTrace tailWord_2638167 prefixEnd_2638167 903098478553389928786531 := by
  unfold tailWord_2638167
  simp only [CollatzResearch.WordTrace]
  refine ⟨96221855433378996897552755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64147903622252664598368503 96221855433378996897552755)
  ·
    refine ⟨144332783150068495346329133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96221855433378996897552755 144332783150068495346329133)
    ·
      refine ⟨54124793681275685754873425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144332783150068495346329133 54124793681275685754873425)
      ·
        refine ⟨40593595260956764316155069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54124793681275685754873425 40593595260956764316155069)
        ·
          refine ⟨15222598222858786618558151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40593595260956764316155069 15222598222858786618558151)
          ·
            refine ⟨22833897334288179927837227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15222598222858786618558151 22833897334288179927837227)
            ·
              refine ⟨34250846001432269891755841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22833897334288179927837227 34250846001432269891755841)
              ·
                refine ⟨25688134501074202418816881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34250846001432269891755841 25688134501074202418816881)
                ·
                  refine ⟨19266100875805651814112661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25688134501074202418816881 19266100875805651814112661)
                  ·
                    refine ⟨903098478553389928786531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19266100875805651814112661 903098478553389928786531)
                    ·
                      rfl

theorem cell22_2638167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_2638167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638167 prefixEnd_2638167 := by exact prefixLift 2638167
  have htrace : WordTrace (prefixWord ++ tailWord_2638167) baseStart_2638167 baseEnd_2638167 := by
    simpa [prefixWord, tailWord_2638167, baseEnd_2638167] using wordTrace_append hprefix tailTrace_2638167
  have hstable : (prefixWord ++ tailWord_2638167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638167).length < 2 ^ (prefixWord ++ tailWord_2638167).sum := by decide
  have hdescent : baseEnd_2638167 < baseStart_2638167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638216 : List Nat := [2, 1, 3, 3, 1, 1, 5, 1, 5]
def baseStart_2638216 : Nat := 118140960795 + 2638216 * 2 ^ 59
def prefixEnd_2638216 : Nat := 4983230072969 + 3 ^ 40 * 2638216 * 2
def baseEnd_2638216 : Nat := 301038417418256711437127

theorem tailTrace_2638216 : CollatzResearch.WordTrace tailWord_2638216 prefixEnd_2638216 301038417418256711437127 := by
  unfold tailWord_2638216
  simp only [CollatzResearch.WordTrace]
  refine ⟨48111821305100739133043251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64149095073467652177391001 48111821305100739133043251)
  ·
    refine ⟨72167731957651108699564877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48111821305100739133043251 72167731957651108699564877)
    ·
      refine ⟨27062899484119165762336829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72167731957651108699564877 27062899484119165762336829)
      ·
        refine ⟨10148587306544687160876311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27062899484119165762336829 10148587306544687160876311)
        ·
          refine ⟨15222880959817030741314467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10148587306544687160876311 15222880959817030741314467)
          ·
            refine ⟨22834321439725546111971701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15222880959817030741314467 22834321439725546111971701)
            ·
              refine ⟨2140717634974269947997347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22834321439725546111971701 2140717634974269947997347)
              ·
                refine ⟨3211076452461404921996021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2140717634974269947997347 3211076452461404921996021)
                ·
                  refine ⟨301038417418256711437127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3211076452461404921996021 301038417418256711437127)
                  ·
                    rfl

theorem cell22_2638216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 5].length) (baseStart_2638216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638216 prefixEnd_2638216 := by exact prefixLift 2638216
  have htrace : WordTrace (prefixWord ++ tailWord_2638216) baseStart_2638216 baseEnd_2638216 := by
    simpa [prefixWord, tailWord_2638216, baseEnd_2638216] using wordTrace_append hprefix tailTrace_2638216
  have hstable : (prefixWord ++ tailWord_2638216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638216).length < 2 ^ (prefixWord ++ tailWord_2638216).sum := by decide
  have hdescent : baseEnd_2638216 < baseStart_2638216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638237 : List Nat := [1, 4, 2, 1, 5, 1, 1, 3, 1, 3]
def baseStart_2638237 : Nat := 118140960795 + 2638237 * 2 ^ 59
def prefixEnd_2638237 : Nat := 4983230072969 + 3 ^ 40 * 2638237 * 2
def baseEnd_2638237 : Nat := 903122440983933079536317

theorem tailTrace_2638237 : CollatzResearch.WordTrace tailWord_2638237 prefixEnd_2638237 903122440983933079536317 := by
  unfold tailWord_2638237
  simp only [CollatzResearch.WordTrace]
  refine ⟨96224408543125398852600965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64149605695416932568400643 96224408543125398852600965)
  ·
    refine ⟨18042076601836012284862681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96224408543125398852600965 18042076601836012284862681)
    ·
      refine ⟨13531557451377009213647011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18042076601836012284862681 13531557451377009213647011)
      ·
        refine ⟨20297336177065513820470517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13531557451377009213647011 20297336177065513820470517)
        ·
          refine ⟨1902875266599891920669111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20297336177065513820470517 1902875266599891920669111)
          ·
            refine ⟨2854312899899837881003667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902875266599891920669111 2854312899899837881003667)
            ·
              refine ⟨4281469349849756821505501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2854312899899837881003667 4281469349849756821505501)
              ·
                refine ⟨1605551006193658808064563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4281469349849756821505501 1605551006193658808064563)
                ·
                  refine ⟨2408326509290488212096845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605551006193658808064563 2408326509290488212096845)
                  ·
                    refine ⟨903122440983933079536317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2408326509290488212096845 903122440983933079536317)
                    ·
                      rfl

theorem cell22_2638237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_2638237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638237 prefixEnd_2638237 := by exact prefixLift 2638237
  have htrace : WordTrace (prefixWord ++ tailWord_2638237) baseStart_2638237 baseEnd_2638237 := by
    simpa [prefixWord, tailWord_2638237, baseEnd_2638237] using wordTrace_append hprefix tailTrace_2638237
  have hstable : (prefixWord ++ tailWord_2638237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638237).length < 2 ^ (prefixWord ++ tailWord_2638237).sum := by decide
  have hdescent : baseEnd_2638237 < baseStart_2638237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638306 : List Nat := [3, 3, 3, 2, 11]
def baseStart_2638306 : Nat := 118140960795 + 2638306 * 2 ^ 59
def prefixEnd_2638306 : Nat := 4983230072969 + 3 ^ 40 * 2638306 * 2
def baseEnd_2638306 : Nat := 3716650457177118928235

theorem tailTrace_2638306 : CollatzResearch.WordTrace tailWord_2638306 prefixEnd_2638306 3716650457177118928235 := by
  unfold tailWord_2638306
  simp only [CollatzResearch.WordTrace]
  refine ⟨24056731294968855909215693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64151283453250282424575181 24056731294968855909215693)
  ·
    refine ⟨9021274235613320965955885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24056731294968855909215693 9021274235613320965955885)
    ·
      refine ⟨3382977838354995362233457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9021274235613320965955885 3382977838354995362233457)
      ·
        refine ⟨2537233378766246521675093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3382977838354995362233457 2537233378766246521675093)
        ·
          refine ⟨3716650457177118928235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2537233378766246521675093 3716650457177118928235)
          ·
            rfl

theorem cell22_2638306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 11].length) (baseStart_2638306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638306 prefixEnd_2638306 := by exact prefixLift 2638306
  have htrace : WordTrace (prefixWord ++ tailWord_2638306) baseStart_2638306 baseEnd_2638306 := by
    simpa [prefixWord, tailWord_2638306, baseEnd_2638306] using wordTrace_append hprefix tailTrace_2638306
  have hstable : (prefixWord ++ tailWord_2638306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638306).length < 2 ^ (prefixWord ++ tailWord_2638306).sum := by decide
  have hdescent : baseEnd_2638306 < baseStart_2638306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638321 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 3, 3]
def baseStart_2638321 : Nat := 118140960795 + 2638321 * 2 ^ 59
def prefixEnd_2638321 : Nat := 4983230072969 + 3 ^ 40 * 2638321 * 2
def baseEnd_2638321 : Nat := 903151195900584860436059

theorem tailTrace_2638321 : CollatzResearch.WordTrace tailWord_2638321 prefixEnd_2638321 903151195900584860436059 := by
  unfold tailWord_2638321
  simp only [CollatzResearch.WordTrace]
  refine ⟨96227472274821081198658817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64151648183214054132439211 96227472274821081198658817)
  ·
    refine ⟨72170604206115810898994113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96227472274821081198658817 72170604206115810898994113)
    ·
      refine ⟨54127953154586858174245585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72170604206115810898994113 54127953154586858174245585)
      ·
        refine ⟨40595964865940143630684189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54127953154586858174245585 40595964865940143630684189)
        ·
          refine ⟨15223486824727553861506571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40595964865940143630684189 15223486824727553861506571)
          ·
            refine ⟨22835230237091330792259857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15223486824727553861506571 22835230237091330792259857)
            ·
              refine ⟨17126422677818498094194893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22835230237091330792259857 17126422677818498094194893)
              ·
                refine ⟨6422408504181936785323085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17126422677818498094194893 6422408504181936785323085)
                ·
                  refine ⟨2408403189068226294496157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6422408504181936785323085 2408403189068226294496157)
                  ·
                    refine ⟨903151195900584860436059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2408403189068226294496157 903151195900584860436059)
                    ·
                      rfl

theorem cell22_2638321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_2638321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638321 prefixEnd_2638321 := by exact prefixLift 2638321
  have htrace : WordTrace (prefixWord ++ tailWord_2638321) baseStart_2638321 baseEnd_2638321 := by
    simpa [prefixWord, tailWord_2638321, baseEnd_2638321] using wordTrace_append hprefix tailTrace_2638321
  have hstable : (prefixWord ++ tailWord_2638321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638321).length < 2 ^ (prefixWord ++ tailWord_2638321).sum := by decide
  have hdescent : baseEnd_2638321 < baseStart_2638321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638342 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2638342 : Nat := 118140960795 + 2638342 * 2 ^ 59
def prefixEnd_2638342 : Nat := 4983230072969 + 3 ^ 40 * 2638342 * 2
def baseEnd_2638342 : Nat := 903158384629747805660995

theorem tailTrace_2638342 : CollatzResearch.WordTrace tailWord_2638342 prefixEnd_2638342 903158384629747805660995 := by
  unfold tailWord_2638342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3007132443992031305786665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64152158805163334523448853 3007132443992031305786665)
  ·
    refine ⟨2255349332994023479339999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3007132443992031305786665 2255349332994023479339999)
    ·
      refine ⟨3383023999491035219009999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2255349332994023479339999 3383023999491035219009999)
      ·
        refine ⟨5074535999236552828514999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3383023999491035219009999 5074535999236552828514999)
        ·
          refine ⟨7611803998854829242772499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5074535999236552828514999 7611803998854829242772499)
          ·
            refine ⟨11417705998282243864158749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7611803998854829242772499 11417705998282243864158749)
            ·
              refine ⟨4281639749355841449059531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11417705998282243864158749 4281639749355841449059531)
              ·
                refine ⟨6422459624033762173589297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4281639749355841449059531 6422459624033762173589297)
                ·
                  refine ⟨4816844718025321630191973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6422459624033762173589297 4816844718025321630191973)
                  ·
                    refine ⟨903158384629747805660995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4816844718025321630191973 903158384629747805660995)
                    ·
                      rfl

theorem cell22_2638342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2638342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638342 prefixEnd_2638342 := by exact prefixLift 2638342
  have htrace : WordTrace (prefixWord ++ tailWord_2638342) baseStart_2638342 baseEnd_2638342 := by
    simpa [prefixWord, tailWord_2638342, baseEnd_2638342] using wordTrace_append hprefix tailTrace_2638342
  have hstable : (prefixWord ++ tailWord_2638342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638342).length < 2 ^ (prefixWord ++ tailWord_2638342).sum := by decide
  have hdescent : baseEnd_2638342 < baseStart_2638342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638396 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 6]
def baseStart_2638396 : Nat := 118140960795 + 2638396 * 2 ^ 59
def prefixEnd_2638396 : Nat := 4983230072969 + 3 ^ 40 * 2638396 * 2
def baseEnd_2638396 : Nat := 301058956644436554936943

theorem tailTrace_2638396 : CollatzResearch.WordTrace tailWord_2638396 prefixEnd_2638396 301058956644436554936943 := by
  unfold tailWord_2638396
  simp only [CollatzResearch.WordTrace]
  refine ⟨48115103874774684503819521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64153471833032912671759361 48115103874774684503819521)
  ·
    refine ⟨36086327906081013377864641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48115103874774684503819521 36086327906081013377864641)
    ·
      refine ⟨27064745929560760033398481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36086327906081013377864641 27064745929560760033398481)
      ·
        refine ⟨20298559447170570025048861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27064745929560760033398481 20298559447170570025048861)
        ·
          refine ⟨7611959792688963759393323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20298559447170570025048861 7611959792688963759393323)
          ·
            refine ⟨11417939689033445639089985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7611959792688963759393323 11417939689033445639089985)
            ·
              refine ⟨8563454766775084229317489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11417939689033445639089985 8563454766775084229317489)
              ·
                refine ⟨6422591075081313171988117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8563454766775084229317489 6422591075081313171988117)
                ·
                  refine ⟨301058956644436554936943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6422591075081313171988117 301058956644436554936943)
                  ·
                    rfl

theorem cell22_2638396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_2638396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638396 prefixEnd_2638396 := by exact prefixLift 2638396
  have htrace : WordTrace (prefixWord ++ tailWord_2638396) baseStart_2638396 baseEnd_2638396 := by
    simpa [prefixWord, tailWord_2638396, baseEnd_2638396] using wordTrace_append hprefix tailTrace_2638396
  have hstable : (prefixWord ++ tailWord_2638396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638396).length < 2 ^ (prefixWord ++ tailWord_2638396).sum := by decide
  have hdescent : baseEnd_2638396 < baseStart_2638396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638411 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 4, 3]
def baseStart_2638411 : Nat := 118140960795 + 2638411 * 2 ^ 59
def prefixEnd_2638411 : Nat := 4983230072969 + 3 ^ 40 * 2638411 * 2
def baseEnd_2638411 : Nat := 903182004739854625685783

theorem tailTrace_2638411 : CollatzResearch.WordTrace tailWord_2638411 prefixEnd_2638411 903182004739854625685783 := by
  unfold tailWord_2638411
  simp only [CollatzResearch.WordTrace]
  refine ⟨96230754844495026569435087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64153836562996684379623391 96230754844495026569435087)
  ·
    refine ⟨144346132266742539854152631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96230754844495026569435087 144346132266742539854152631)
    ·
      refine ⟨216519198400113809781228947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144346132266742539854152631 216519198400113809781228947)
      ·
        refine ⟨324778797600170714671843421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216519198400113809781228947 324778797600170714671843421)
        ·
          refine ⟨121792049100064018001941283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 324778797600170714671843421 121792049100064018001941283)
          ·
            refine ⟨182688073650096027002911925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121792049100064018001941283 182688073650096027002911925)
            ·
              refine ⟨17127006904696502531522993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 182688073650096027002911925 17127006904696502531522993)
              ·
                refine ⟨12845255178522376898642245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17127006904696502531522993 12845255178522376898642245)
                ·
                  refine ⟨2408485345972945668495421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12845255178522376898642245 2408485345972945668495421)
                  ·
                    refine ⟨903182004739854625685783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2408485345972945668495421 903182004739854625685783)
                    ·
                      rfl

theorem cell22_2638411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 3].length) (baseStart_2638411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638411 prefixEnd_2638411 := by exact prefixLift 2638411
  have htrace : WordTrace (prefixWord ++ tailWord_2638411) baseStart_2638411 baseEnd_2638411 := by
    simpa [prefixWord, tailWord_2638411, baseEnd_2638411] using wordTrace_append hprefix tailTrace_2638411
  have hstable : (prefixWord ++ tailWord_2638411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638411).length < 2 ^ (prefixWord ++ tailWord_2638411).sum := by decide
  have hdescent : baseEnd_2638411 < baseStart_2638411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638424 : List Nat := [2, 1, 2, 2, 1, 2, 12]
def baseStart_2638424 : Nat := 118140960795 + 2638424 * 2 ^ 59
def prefixEnd_2638424 : Nat := 4983230072969 + 3 ^ 40 * 2638424 * 2
def baseEnd_2638424 : Nat := 33451350181686182411509

theorem tailTrace_2638424 : CollatzResearch.WordTrace tailWord_2638424 prefixEnd_2638424 33451350181686182411509 := by
  unfold tailWord_2638424
  simp only [CollatzResearch.WordTrace]
  refine ⟨48115614496723964894829163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64154152662298619859772217 48115614496723964894829163)
  ·
    refine ⟨72173421745085947342243745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48115614496723964894829163 72173421745085947342243745)
    ·
      refine ⟨54130066308814460506682809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72173421745085947342243745 54130066308814460506682809)
      ·
        refine ⟨40597549731610845380012107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54130066308814460506682809 40597549731610845380012107)
        ·
          refine ⟨60896324597416268070018161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40597549731610845380012107 60896324597416268070018161)
          ·
            refine ⟨45672243448062201052513621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60896324597416268070018161 45672243448062201052513621)
            ·
              refine ⟨33451350181686182411509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 45672243448062201052513621 33451350181686182411509)
              ·
                rfl

theorem cell22_2638424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 12].length) (baseStart_2638424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638424 prefixEnd_2638424 := by exact prefixLift 2638424
  have htrace : WordTrace (prefixWord ++ tailWord_2638424) baseStart_2638424 baseEnd_2638424 := by
    simpa [prefixWord, tailWord_2638424, baseEnd_2638424] using wordTrace_append hprefix tailTrace_2638424
  have hstable : (prefixWord ++ tailWord_2638424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638424).length < 2 ^ (prefixWord ++ tailWord_2638424).sum := by decide
  have hdescent : baseEnd_2638424 < baseStart_2638424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638445 : List Nat := [1, 5, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_2638445 : Nat := 118140960795 + 2638445 * 2 ^ 59
def prefixEnd_2638445 : Nat := 4983230072969 + 3 ^ 40 * 2638445 * 2
def baseEnd_2638445 : Nat := 903193643634689870335679

theorem tailTrace_2638445 : CollatzResearch.WordTrace tailWord_2638445 prefixEnd_2638445 903193643634689870335679 := by
  unfold tailWord_2638445
  simp only [CollatzResearch.WordTrace]
  refine ⟨96231994926371850376172789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64154663284247900250781859 96231994926371850376172789)
  ·
    refine ⟨9021749524347360972766199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96231994926371850376172789 9021749524347360972766199)
    ·
      refine ⟨13532624286521041459149299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9021749524347360972766199 13532624286521041459149299)
      ·
        refine ⟨20298936429781562188723949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13532624286521041459149299 20298936429781562188723949)
        ·
          refine ⟨7612101161168085820771481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20298936429781562188723949 7612101161168085820771481)
          ·
            refine ⟨5709075870876064365578611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7612101161168085820771481 5709075870876064365578611)
            ·
              refine ⟨8563613806314096548367917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5709075870876064365578611 8563613806314096548367917)
              ·
                refine ⟨3211355177367786205637969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8563613806314096548367917 3211355177367786205637969)
                ·
                  refine ⟨2408516383025839654228477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3211355177367786205637969 2408516383025839654228477)
                  ·
                    refine ⟨903193643634689870335679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2408516383025839654228477 903193643634689870335679)
                    ·
                      rfl

theorem cell22_2638445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_2638445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638445 prefixEnd_2638445 := by exact prefixLift 2638445
  have htrace : WordTrace (prefixWord ++ tailWord_2638445) baseStart_2638445 baseEnd_2638445 := by
    simpa [prefixWord, tailWord_2638445, baseEnd_2638445] using wordTrace_append hprefix tailTrace_2638445
  have hstable : (prefixWord ++ tailWord_2638445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638445).length < 2 ^ (prefixWord ++ tailWord_2638445).sum := by decide
  have hdescent : baseEnd_2638445 < baseStart_2638445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638466 : List Nat := [3, 4, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2638466 : Nat := 118140960795 + 2638466 * 2 ^ 59
def prefixEnd_2638466 : Nat := 4983230072969 + 3 ^ 40 * 2638466 * 2
def baseEnd_2638466 : Nat := 903200832363852815560615

theorem tailTrace_2638466 : CollatzResearch.WordTrace tailWord_2638466 prefixEnd_2638466 903200832363852815560615 := by
  unfold tailWord_2638466
  simp only [CollatzResearch.WordTrace]
  refine ⟨24058190214823942740671813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64155173906197180641791501 24058190214823942740671813)
  ·
    refine ⟨4510910665279489263875965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24058190214823942740671813 4510910665279489263875965)
    ·
      refine ⟨1691591499479808473953487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4510910665279489263875965 1691591499479808473953487)
      ·
        refine ⟨2537387249219712710930231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1691591499479808473953487 2537387249219712710930231)
        ·
          refine ⟨3806080873829569066395347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2537387249219712710930231 3806080873829569066395347)
          ·
            refine ⟨5709121310744353599593021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3806080873829569066395347 5709121310744353599593021)
            ·
              refine ⟨2140920491529132599847383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5709121310744353599593021 2140920491529132599847383)
              ·
                refine ⟨3211380737293698899771075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2140920491529132599847383 3211380737293698899771075)
                ·
                  refine ⟨4817071105940548349656613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3211380737293698899771075 4817071105940548349656613)
                  ·
                    refine ⟨903200832363852815560615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4817071105940548349656613 903200832363852815560615)
                    ·
                      rfl

theorem cell22_2638466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2638466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638466 prefixEnd_2638466 := by exact prefixLift 2638466
  have htrace : WordTrace (prefixWord ++ tailWord_2638466) baseStart_2638466 baseEnd_2638466 := by
    simpa [prefixWord, tailWord_2638466, baseEnd_2638466] using wordTrace_append hprefix tailTrace_2638466
  have hstable : (prefixWord ++ tailWord_2638466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638466).length < 2 ^ (prefixWord ++ tailWord_2638466).sum := by decide
  have hdescent : baseEnd_2638466 < baseStart_2638466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638576 : List Nat := [2, 1, 1, 1, 3, 1, 5, 8]
def baseStart_2638576 : Nat := 118140960795 + 2638576 * 2 ^ 59
def prefixEnd_2638576 : Nat := 4983230072969 + 3 ^ 40 * 2638576 * 2
def baseEnd_2638576 : Nat := 100359831956872132812253

theorem tailTrace_2638576 : CollatzResearch.WordTrace tailWord_2638576 prefixEnd_2638576 100359831956872132812253 := by
  unfold tailWord_2638576
  simp only [CollatzResearch.WordTrace]
  refine ⟨48118386444448629874595791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64157848592598173166127721 48118386444448629874595791)
  ·
    refine ⟨72177579666672944811893687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48118386444448629874595791 72177579666672944811893687)
    ·
      refine ⟨108266369500009417217840531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72177579666672944811893687 108266369500009417217840531)
      ·
        refine ⟨162399554250014125826760797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108266369500009417217840531 162399554250014125826760797)
        ·
          refine ⟨60899832843755297185035299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162399554250014125826760797 60899832843755297185035299)
          ·
            refine ⟨91349749265632945777552949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60899832843755297185035299 91349749265632945777552949)
            ·
              refine ⟨8564038993653088666645589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91349749265632945777552949 8564038993653088666645589)
              ·
                refine ⟨100359831956872132812253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8564038993653088666645589 100359831956872132812253)
                ·
                  rfl

theorem cell22_2638576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 8].length) (baseStart_2638576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638576 prefixEnd_2638576 := by exact prefixLift 2638576
  have htrace : WordTrace (prefixWord ++ tailWord_2638576) baseStart_2638576 baseEnd_2638576 := by
    simpa [prefixWord, tailWord_2638576, baseEnd_2638576] using wordTrace_append hprefix tailTrace_2638576
  have hstable : (prefixWord ++ tailWord_2638576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638576).length < 2 ^ (prefixWord ++ tailWord_2638576).sum := by decide
  have hdescent : baseEnd_2638576 < baseStart_2638576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638578 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_2638578 : Nat := 118140960795 + 2638578 * 2 ^ 59
def prefixEnd_2638578 : Nat := 4983230072969 + 3 ^ 40 * 2638578 * 2
def baseEnd_2638578 : Nat := 903239172252721856760271

theorem tailTrace_2638578 : CollatzResearch.WordTrace tailWord_2638578 prefixEnd_2638578 903239172252721856760271 := by
  unfold tailWord_2638578
  simp only [CollatzResearch.WordTrace]
  refine ⟨24059211458722503522691097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64157897223260009393842925 24059211458722503522691097)
  ·
    refine ⟨18044408594041877642018323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24059211458722503522691097 18044408594041877642018323)
    ·
      refine ⟨27066612891062816463027485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18044408594041877642018323 27066612891062816463027485)
      ·
        refine ⟨10149979834148556173635307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27066612891062816463027485 10149979834148556173635307)
        ·
          refine ⟨15224969751222834260452961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10149979834148556173635307 15224969751222834260452961)
          ·
            refine ⟨11418727313417125695339721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15224969751222834260452961 11418727313417125695339721)
            ·
              refine ⟨8564045485062844271504791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11418727313417125695339721 8564045485062844271504791)
              ·
                refine ⟨12846068227594266407257187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8564045485062844271504791 12846068227594266407257187)
                ·
                  refine ⟨19269102341391399610885781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12846068227594266407257187 19269102341391399610885781)
                  ·
                    refine ⟨903239172252721856760271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19269102341391399610885781 903239172252721856760271)
                    ·
                      rfl

theorem cell22_2638578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_2638578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638578 prefixEnd_2638578 := by exact prefixLift 2638578
  have htrace : WordTrace (prefixWord ++ tailWord_2638578) baseStart_2638578 baseEnd_2638578 := by
    simpa [prefixWord, tailWord_2638578, baseEnd_2638578] using wordTrace_append hprefix tailTrace_2638578
  have hstable : (prefixWord ++ tailWord_2638578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638578).length < 2 ^ (prefixWord ++ tailWord_2638578).sum := by decide
  have hdescent : baseEnd_2638578 < baseStart_2638578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638642 : List Nat := [3, 2, 1, 1, 3, 1, 2, 5, 1, 3]
def baseStart_2638642 : Nat := 118140960795 + 2638642 * 2 ^ 59
def prefixEnd_2638642 : Nat := 4983230072969 + 3 ^ 40 * 2638642 * 2
def baseEnd_2638642 : Nat := 903261080760647023160075

theorem tailTrace_2638642 : CollatzResearch.WordTrace tailWord_2638642 prefixEnd_2638642 903261080760647023160075 := by
  unfold tailWord_2638642
  simp only [CollatzResearch.WordTrace]
  refine ⟨24059795026664538255273545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64159453404438768680729453 24059795026664538255273545)
  ·
    refine ⟨18044846269998403691455159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24059795026664538255273545 18044846269998403691455159)
    ·
      refine ⟨27067269404997605537182739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18044846269998403691455159 27067269404997605537182739)
      ·
        refine ⟨40600904107496408305774109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27067269404997605537182739 40600904107496408305774109)
        ·
          refine ⟨15225339040311153114665291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40600904107496408305774109 15225339040311153114665291)
          ·
            refine ⟨22838008560466729671997937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15225339040311153114665291 22838008560466729671997937)
            ·
              refine ⟨17128506420350047253998453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22838008560466729671997937 17128506420350047253998453)
              ·
                refine ⟨1605797476907816930062355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17128506420350047253998453 1605797476907816930062355)
                ·
                  refine ⟨2408696215361725395093533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605797476907816930062355 2408696215361725395093533)
                  ·
                    refine ⟨903261080760647023160075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2408696215361725395093533 903261080760647023160075)
                    ·
                      rfl

theorem cell22_2638642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_2638642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638642 prefixEnd_2638642 := by exact prefixLift 2638642
  have htrace : WordTrace (prefixWord ++ tailWord_2638642) baseStart_2638642 baseEnd_2638642 := by
    simpa [prefixWord, tailWord_2638642, baseEnd_2638642] using wordTrace_append hprefix tailTrace_2638642
  have hstable : (prefixWord ++ tailWord_2638642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638642).length < 2 ^ (prefixWord ++ tailWord_2638642).sum := by decide
  have hdescent : baseEnd_2638642 < baseStart_2638642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638655 : List Nat := [1, 1, 2, 2, 5, 2, 2, 2, 5]
def baseStart_2638655 : Nat := 118140960795 + 2638655 * 2 ^ 59
def prefixEnd_2638655 : Nat := 4983230072969 + 3 ^ 40 * 2638655 * 2
def baseEnd_2638655 : Nat := 301088510308773107528345

theorem tailTrace_2638655 : CollatzResearch.WordTrace tailWord_2638655 prefixEnd_2638655 301088510308773107528345 := by
  unfold tailWord_2638655
  simp only [CollatzResearch.WordTrace]
  refine ⟨96239654255611056241317419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64159769503740704160878279 96239654255611056241317419)
  ·
    refine ⟨144359481383416584361976129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96239654255611056241317419 144359481383416584361976129)
    ·
      refine ⟨108269611037562438271482097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144359481383416584361976129 108269611037562438271482097)
      ·
        refine ⟨81202208278171828703611573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108269611037562438271482097 81202208278171828703611573)
        ·
          refine ⟨7612707026078608940963585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81202208278171828703611573 7612707026078608940963585)
          ·
            refine ⟨5709530269558956705722689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7612707026078608940963585 5709530269558956705722689)
            ·
              refine ⟨4282147702169217529292017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5709530269558956705722689 4282147702169217529292017)
              ·
                refine ⟨3211610776626913146969013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4282147702169217529292017 3211610776626913146969013)
                ·
                  refine ⟨301088510308773107528345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3211610776626913146969013 301088510308773107528345)
                  ·
                    rfl

theorem cell22_2638655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 5].length) (baseStart_2638655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638655 prefixEnd_2638655 := by exact prefixLift 2638655
  have htrace : WordTrace (prefixWord ++ tailWord_2638655) baseStart_2638655 baseEnd_2638655 := by
    simpa [prefixWord, tailWord_2638655, baseEnd_2638655] using wordTrace_append hprefix tailTrace_2638655
  have hstable : (prefixWord ++ tailWord_2638655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638655).length < 2 ^ (prefixWord ++ tailWord_2638655).sum := by decide
  have hdescent : baseEnd_2638655 < baseStart_2638655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638730 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 1, 6]
def baseStart_2638730 : Nat := 118140960795 + 2638730 * 2 ^ 59
def prefixEnd_2638730 : Nat := 4983230072969 + 3 ^ 40 * 2638730 * 2
def baseEnd_2638730 : Nat := 903291204959044126959805

theorem tailTrace_2638730 : CollatzResearch.WordTrace tailWord_2638730 prefixEnd_2638730 903291204959044126959805 := by
  unfold tailWord_2638730
  simp only [CollatzResearch.WordTrace]
  refine ⟨24060597432584836012574411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64161593153559562700198429 24060597432584836012574411)
  ·
    refine ⟨36090896148877254018861617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24060597432584836012574411 36090896148877254018861617)
    ·
      refine ⟨27068172111657940514146213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36090896148877254018861617 27068172111657940514146213)
      ·
        refine ⟨5075282270935863846402415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27068172111657940514146213 5075282270935863846402415)
        ·
          refine ⟨7612923406403795769603623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5075282270935863846402415 7612923406403795769603623)
          ·
            refine ⟨11419385109605693654405435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7612923406403795769603623 11419385109605693654405435)
            ·
              refine ⟨17129077664408540481608153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11419385109605693654405435 17129077664408540481608153)
              ·
                refine ⟨12846808248306405361206115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17129077664408540481608153 12846808248306405361206115)
                ·
                  refine ⟨19270212372459608041809173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12846808248306405361206115 19270212372459608041809173)
                  ·
                    refine ⟨903291204959044126959805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19270212372459608041809173 903291204959044126959805)
                    ·
                      rfl

theorem cell22_2638730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_2638730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638730 prefixEnd_2638730 := by exact prefixLift 2638730
  have htrace : WordTrace (prefixWord ++ tailWord_2638730) baseStart_2638730 baseEnd_2638730 := by
    simpa [prefixWord, tailWord_2638730, baseEnd_2638730] using wordTrace_append hprefix tailTrace_2638730
  have hstable : (prefixWord ++ tailWord_2638730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638730).length < 2 ^ (prefixWord ++ tailWord_2638730).sum := by decide
  have hdescent : baseEnd_2638730 < baseStart_2638730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638743 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 2, 7]
def baseStart_2638743 : Nat := 118140960795 + 2638743 * 2 ^ 59
def prefixEnd_2638743 : Nat := 4983230072969 + 3 ^ 40 * 2638743 * 2
def baseEnd_2638743 : Nat := 903295655124716426384765

theorem tailTrace_2638743 : CollatzResearch.WordTrace tailWord_2638743 prefixEnd_2638743 903295655124716426384765 := by
  unfold tailWord_2638743
  simp only [CollatzResearch.WordTrace]
  refine ⟨96242863879292247270520883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64161909252861498180347255 96242863879292247270520883)
  ·
    refine ⟨144364295818938370905781325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96242863879292247270520883 144364295818938370905781325)
    ·
      refine ⟨54136610932101889089667997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144364295818938370905781325 54136610932101889089667997)
      ·
        refine ⟨20301229099538208408625499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54136610932101889089667997 20301229099538208408625499)
        ·
          refine ⟨30451843649307312612938249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20301229099538208408625499 30451843649307312612938249)
          ·
            refine ⟨22838882736980484459703687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30451843649307312612938249 22838882736980484459703687)
            ·
              refine ⟨34258324105470726689555531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22838882736980484459703687 34258324105470726689555531)
              ·
                refine ⟨51387486158206090034333297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34258324105470726689555531 51387486158206090034333297)
                ·
                  refine ⟨38540614618654567525749973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51387486158206090034333297 38540614618654567525749973)
                  ·
                    refine ⟨903295655124716426384765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38540614618654567525749973 903295655124716426384765)
                    ·
                      rfl

theorem cell22_2638743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_2638743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638743 prefixEnd_2638743 := by exact prefixLift 2638743
  have htrace : WordTrace (prefixWord ++ tailWord_2638743) baseStart_2638743 baseEnd_2638743 := by
    simpa [prefixWord, tailWord_2638743, baseEnd_2638743] using wordTrace_append hprefix tailTrace_2638743
  have hstable : (prefixWord ++ tailWord_2638743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638743).length < 2 ^ (prefixWord ++ tailWord_2638743).sum := by decide
  have hdescent : baseEnd_2638743 < baseStart_2638743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638777 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 3, 3]
def baseStart_2638777 : Nat := 118140960795 + 2638777 * 2 ^ 59
def prefixEnd_2638777 : Nat := 4983230072969 + 3 ^ 40 * 2638777 * 2
def baseEnd_2638777 : Nat := 903307294019551671034661

theorem tailTrace_2638777 : CollatzResearch.WordTrace tailWord_2638777 prefixEnd_2638777 903307294019551671034661 := by
  unfold tailWord_2638777
  simp only [CollatzResearch.WordTrace]
  refine ⟨96244103961169071077258585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64162735974112714051505723 96244103961169071077258585)
  ·
    refine ⟨72183077970876803307943939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96244103961169071077258585 72183077970876803307943939)
    ·
      refine ⟨108274616956315204961915909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72183077970876803307943939 108274616956315204961915909)
      ·
        refine ⟨20301490679309100930359233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108274616956315204961915909 20301490679309100930359233)
        ·
          refine ⟨15226118009481825697769425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20301490679309100930359233 15226118009481825697769425)
          ·
            refine ⟨11419588507111369273327069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15226118009481825697769425 11419588507111369273327069)
            ·
              refine ⟨4282345690166763477497651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11419588507111369273327069 4282345690166763477497651)
              ·
                refine ⟨6423518535250145216246477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4282345690166763477497651 6423518535250145216246477)
                ·
                  refine ⟨2408819450718804456092429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6423518535250145216246477 2408819450718804456092429)
                  ·
                    refine ⟨903307294019551671034661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2408819450718804456092429 903307294019551671034661)
                    ·
                      rfl

theorem cell22_2638777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 3].length) (baseStart_2638777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638777 prefixEnd_2638777 := by exact prefixLift 2638777
  have htrace : WordTrace (prefixWord ++ tailWord_2638777) baseStart_2638777 baseEnd_2638777 := by
    simpa [prefixWord, tailWord_2638777, baseEnd_2638777] using wordTrace_append hprefix tailTrace_2638777
  have hstable : (prefixWord ++ tailWord_2638777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638777).length < 2 ^ (prefixWord ++ tailWord_2638777).sum := by decide
  have hdescent : baseEnd_2638777 < baseStart_2638777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638869 : List Nat := [1, 3, 2, 1, 4, 2, 2, 3, 4]
def baseStart_2638869 : Nat := 118140960795 + 2638869 * 2 ^ 59
def prefixEnd_2638869 : Nat := 4983230072969 + 3 ^ 40 * 2638869 * 2
def baseEnd_2638869 : Nat := 301112929166564699244793

theorem tailTrace_2638869 : CollatzResearch.WordTrace tailWord_2638869 prefixEnd_2638869 301112929166564699244793 := by
  unfold tailWord_2638869
  simp only [CollatzResearch.WordTrace]
  refine ⟨96247459476835770789607661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64164972984557180526405107 96247459476835770789607661)
  ·
    refine ⟨36092797303813414046102873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96247459476835770789607661 36092797303813414046102873)
    ·
      refine ⟨27069597977860060534577155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36092797303813414046102873 27069597977860060534577155)
      ·
        refine ⟨40604396966790090801865733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27069597977860060534577155 40604396966790090801865733)
        ·
          refine ⟨7613324431273142025349825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40604396966790090801865733 7613324431273142025349825)
          ·
            refine ⟨5709993323454856519012369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7613324431273142025349825 5709993323454856519012369)
            ·
              refine ⟨4282494992591142389259277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5709993323454856519012369 4282494992591142389259277)
              ·
                refine ⟨1605935622221678395972229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4282494992591142389259277 1605935622221678395972229)
                ·
                  refine ⟨301112929166564699244793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1605935622221678395972229 301112929166564699244793)
                  ·
                    rfl

theorem cell22_2638869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_2638869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638869 prefixEnd_2638869 := by exact prefixLift 2638869
  have htrace : WordTrace (prefixWord ++ tailWord_2638869) baseStart_2638869 baseEnd_2638869 := by
    simpa [prefixWord, tailWord_2638869, baseEnd_2638869] using wordTrace_append hprefix tailTrace_2638869
  have hstable : (prefixWord ++ tailWord_2638869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638869).length < 2 ^ (prefixWord ++ tailWord_2638869).sum := by decide
  have hdescent : baseEnd_2638869 < baseStart_2638869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638871 : List Nat := [1, 1, 3, 5, 1, 3, 2, 1, 1, 4]
def baseStart_2638871 : Nat := 118140960795 + 2638871 * 2 ^ 59
def prefixEnd_2638871 : Nat := 4983230072969 + 3 ^ 40 * 2638871 * 2
def baseEnd_2638871 : Nat := 903339472140566759184373

theorem tailTrace_2638871 : CollatzResearch.WordTrace tailWord_2638871 prefixEnd_2638871 903339472140566759184373 := by
  unfold tailWord_2638871
  simp only [CollatzResearch.WordTrace]
  refine ⟨96247532422828525131180467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64165021615219016754120311 96247532422828525131180467)
  ·
    refine ⟨144371298634242787696770701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96247532422828525131180467 144371298634242787696770701)
    ·
      refine ⟨54139236987841045386289013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144371298634242787696770701 54139236987841045386289013)
      ·
        refine ⟨5075553467610098004964595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54139236987841045386289013 5075553467610098004964595)
        ·
          refine ⟨7613330201415147007446893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5075553467610098004964595 7613330201415147007446893)
          ·
            refine ⟨2854998825530680127792585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7613330201415147007446893 2854998825530680127792585)
            ·
              refine ⟨2141249119148010095844439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2854998825530680127792585 2141249119148010095844439)
              ·
                refine ⟨3211873678722015143766659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2141249119148010095844439 3211873678722015143766659)
                ·
                  refine ⟨4817810518083022715649989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3211873678722015143766659 4817810518083022715649989)
                  ·
                    refine ⟨903339472140566759184373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4817810518083022715649989 903339472140566759184373)
                    ·
                      rfl

theorem cell22_2638871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_2638871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638871 prefixEnd_2638871 := by exact prefixLift 2638871
  have htrace : WordTrace (prefixWord ++ tailWord_2638871) baseStart_2638871 baseEnd_2638871 := by
    simpa [prefixWord, tailWord_2638871, baseEnd_2638871] using wordTrace_append hprefix tailTrace_2638871
  have hstable : (prefixWord ++ tailWord_2638871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638871).length < 2 ^ (prefixWord ++ tailWord_2638871).sum := by decide
  have hdescent : baseEnd_2638871 < baseStart_2638871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638884 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 4, 3]
def baseStart_2638884 : Nat := 118140960795 + 2638884 * 2 ^ 59
def prefixEnd_2638884 : Nat := 4983230072969 + 3 ^ 40 * 2638884 * 2
def baseEnd_2638884 : Nat := 903343922306239058609333

theorem tailTrace_2638884 : CollatzResearch.WordTrace tailWord_2638884 prefixEnd_2638884 903343922306239058609333 := by
  unfold tailWord_2638884
  simp only [CollatzResearch.WordTrace]
  refine ⟨48124003285890714175701853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64165337714520952234269137 48124003285890714175701853)
  ·
    refine ⟨18046501232209017815888195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48124003285890714175701853 18046501232209017815888195)
    ·
      refine ⟨27069751848313526723832293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18046501232209017815888195 27069751848313526723832293)
      ·
        refine ⟨5075578471558786260718555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27069751848313526723832293 5075578471558786260718555)
        ·
          refine ⟨7613367707338179391077833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5075578471558786260718555 7613367707338179391077833)
          ·
            refine ⟨5710025780503634543308375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7613367707338179391077833 5710025780503634543308375)
            ·
              refine ⟨8565038670755451814962563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5710025780503634543308375 8565038670755451814962563)
              ·
                refine ⟨12847558006133177722443845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8565038670755451814962563 12847558006133177722443845)
                ·
                  refine ⟨2408917126149970822958221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12847558006133177722443845 2408917126149970822958221)
                  ·
                    refine ⟨903343922306239058609333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2408917126149970822958221 903343922306239058609333)
                    ·
                      rfl

theorem cell22_2638884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_2638884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638884 prefixEnd_2638884 := by exact prefixLift 2638884
  have htrace : WordTrace (prefixWord ++ tailWord_2638884) baseStart_2638884 baseEnd_2638884 := by
    simpa [prefixWord, tailWord_2638884, baseEnd_2638884] using wordTrace_append hprefix tailTrace_2638884
  have hstable : (prefixWord ++ tailWord_2638884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638884).length < 2 ^ (prefixWord ++ tailWord_2638884).sum := by decide
  have hdescent : baseEnd_2638884 < baseStart_2638884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638912 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 3, 3]
def baseStart_2638912 : Nat := 118140960795 + 2638912 * 2 ^ 59
def prefixEnd_2638912 : Nat := 4983230072969 + 3 ^ 40 * 2638912 * 2
def baseEnd_2638912 : Nat := 903353507278456318909247

theorem tailTrace_2638912 : CollatzResearch.WordTrace tailWord_2638912 prefixEnd_2638912 903353507278456318909247 := by
  unfold tailWord_2638912
  simp only [CollatzResearch.WordTrace]
  refine ⟨48124513907839994566711495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64166018543786659422281993 48124513907839994566711495)
  ·
    refine ⟨72186770861759991850067243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48124513907839994566711495 72186770861759991850067243)
    ·
      refine ⟨108280156292639987775100865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72186770861759991850067243 108280156292639987775100865)
      ·
        refine ⟨81210117219479990831325649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108280156292639987775100865 81210117219479990831325649)
        ·
          refine ⟨60907587914609993123494237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81210117219479990831325649 60907587914609993123494237)
          ·
            refine ⟨22840345467978747421310339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60907587914609993123494237 22840345467978747421310339)
            ·
              refine ⟨34260518201968121131965509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22840345467978747421310339 34260518201968121131965509)
              ·
                refine ⟨6423847162869022712243533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34260518201968121131965509 6423847162869022712243533)
                ·
                  refine ⟨2408942686075883517091325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6423847162869022712243533 2408942686075883517091325)
                  ·
                    refine ⟨903353507278456318909247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2408942686075883517091325 903353507278456318909247)
                    ·
                      rfl

theorem cell22_2638912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 3, 3].length) (baseStart_2638912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638912 prefixEnd_2638912 := by exact prefixLift 2638912
  have htrace : WordTrace (prefixWord ++ tailWord_2638912) baseStart_2638912 baseEnd_2638912 := by
    simpa [prefixWord, tailWord_2638912, baseEnd_2638912] using wordTrace_append hprefix tailTrace_2638912
  have hstable : (prefixWord ++ tailWord_2638912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638912).length < 2 ^ (prefixWord ++ tailWord_2638912).sum := by decide
  have hdescent : baseEnd_2638912 < baseStart_2638912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638946 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_2638946 : Nat := 118140960795 + 2638946 * 2 ^ 59
def prefixEnd_2638946 : Nat := 4983230072969 + 3 ^ 40 * 2638946 * 2
def baseEnd_2638946 : Nat := 903365146173291563559143

theorem tailTrace_2638946 : CollatzResearch.WordTrace tailWord_2638946 prefixEnd_2638946 903365146173291563559143 := by
  unfold tailWord_2638946
  simp only [CollatzResearch.WordTrace]
  refine ⟨24062566974389203235040173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64166845265037875293440461 24062566974389203235040173)
  ·
    refine ⟨9023462615395951213140065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24062566974389203235040173 9023462615395951213140065)
    ·
      refine ⟨6767596961546963409855049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9023462615395951213140065 6767596961546963409855049)
      ·
        refine ⟨5075697721160222557391287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6767596961546963409855049 5075697721160222557391287)
        ·
          refine ⟨7613546581740333836086931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5075697721160222557391287 7613546581740333836086931)
          ·
            refine ⟨11420319872610500754130397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7613546581740333836086931 11420319872610500754130397)
            ·
              refine ⟨4282619952228937782798899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11420319872610500754130397 4282619952228937782798899)
              ·
                refine ⟨6423929928343406674198349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4282619952228937782798899 6423929928343406674198349)
                ·
                  refine ⟨2408973723128777502824381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6423929928343406674198349 2408973723128777502824381)
                  ·
                    refine ⟨903365146173291563559143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2408973723128777502824381 903365146173291563559143)
                    ·
                      rfl

theorem cell22_2638946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_2638946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638946 prefixEnd_2638946 := by exact prefixLift 2638946
  have htrace : WordTrace (prefixWord ++ tailWord_2638946) baseStart_2638946 baseEnd_2638946 := by
    simpa [prefixWord, tailWord_2638946, baseEnd_2638946] using wordTrace_append hprefix tailTrace_2638946
  have hstable : (prefixWord ++ tailWord_2638946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638946).length < 2 ^ (prefixWord ++ tailWord_2638946).sum := by decide
  have hdescent : baseEnd_2638946 < baseStart_2638946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638972 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 3, 4]
def baseStart_2638972 : Nat := 118140960795 + 2638972 * 2 ^ 59
def prefixEnd_2638972 : Nat := 4983230072969 + 3 ^ 40 * 2638972 * 2
def baseEnd_2638972 : Nat := 903374046504636162409063

theorem tailTrace_2638972 : CollatzResearch.WordTrace tailWord_2638972 prefixEnd_2638972 903374046504636162409063 := by
  unfold tailWord_2638972
  simp only [CollatzResearch.WordTrace]
  refine ⟨48125608097731309690303585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64167477463641746253738113 48125608097731309690303585)
  ·
    refine ⟨36094206073298482267727689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48125608097731309690303585 36094206073298482267727689)
    ·
      refine ⟨27070654554973861700795767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36094206073298482267727689 27070654554973861700795767)
      ·
        refine ⟨40605981832460792551193651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27070654554973861700795767 40605981832460792551193651)
        ·
          refine ⟨60908972748691188826790477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40605981832460792551193651 60908972748691188826790477)
          ·
            refine ⟨22840864780759195810046429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60908972748691188826790477 22840864780759195810046429)
            ·
              refine ⟨8565324292784698428767411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22840864780759195810046429 8565324292784698428767411)
              ·
                refine ⟨12847986439177047643151117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8565324292784698428767411 12847986439177047643151117)
                ·
                  refine ⟨4817994914691392866181669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12847986439177047643151117 4817994914691392866181669)
                  ·
                    refine ⟨903374046504636162409063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4817994914691392866181669 903374046504636162409063)
                    ·
                      rfl

theorem cell22_2638972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_2638972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2638972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2638972 prefixEnd_2638972 := by exact prefixLift 2638972
  have htrace : WordTrace (prefixWord ++ tailWord_2638972) baseStart_2638972 baseEnd_2638972 := by
    simpa [prefixWord, tailWord_2638972, baseEnd_2638972] using wordTrace_append hprefix tailTrace_2638972
  have hstable : (prefixWord ++ tailWord_2638972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638972).length < 2 ^ (prefixWord ++ tailWord_2638972).sum := by decide
  have hdescent : baseEnd_2638972 < baseStart_2638972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639141 : List Nat := [1, 3, 1, 2, 4, 1, 3, 2, 1, 4]
def baseStart_2639141 : Nat := 118140960795 + 2639141 * 2 ^ 59
def prefixEnd_2639141 : Nat := 4983230072969 + 3 ^ 40 * 2639141 * 2
def baseEnd_2639141 : Nat := 903431898658376054933545

theorem tailTrace_2639141 : CollatzResearch.WordTrace tailWord_2639141 prefixEnd_2639141 903431898658376054933545 := by
  unfold tailWord_2639141
  simp only [CollatzResearch.WordTrace]
  refine ⟨96257380131850361243509277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64171586754566907495672851 96257380131850361243509277)
  ·
    refine ⟨36096517549443885466315979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96257380131850361243509277 36096517549443885466315979)
    ·
      refine ⟨54144776324165828199473969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36096517549443885466315979 54144776324165828199473969)
      ·
        refine ⟨40608582243124371149605477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54144776324165828199473969 40608582243124371149605477)
        ·
          refine ⟨7614109170585819590551027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40608582243124371149605477 7614109170585819590551027)
          ·
            refine ⟨11421163755878729385826541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7614109170585819590551027 11421163755878729385826541)
            ·
              refine ⟨4282936408454523519684953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11421163755878729385826541 4282936408454523519684953)
              ·
                refine ⟨3212202306340892639763715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4282936408454523519684953 3212202306340892639763715)
                ·
                  refine ⟨4818303459511338959645573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212202306340892639763715 4818303459511338959645573)
                  ·
                    refine ⟨903431898658376054933545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4818303459511338959645573 903431898658376054933545)
                    ·
                      rfl

theorem cell22_2639141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_2639141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639141 prefixEnd_2639141 := by exact prefixLift 2639141
  have htrace : WordTrace (prefixWord ++ tailWord_2639141) baseStart_2639141 baseEnd_2639141 := by
    simpa [prefixWord, tailWord_2639141, baseEnd_2639141] using wordTrace_append hprefix tailTrace_2639141
  have hstable : (prefixWord ++ tailWord_2639141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639141).length < 2 ^ (prefixWord ++ tailWord_2639141).sum := by decide
  have hdescent : baseEnd_2639141 < baseStart_2639141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639154 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_2639154 : Nat := 118140960795 + 2639154 * 2 ^ 59
def prefixEnd_2639154 : Nat := 4983230072969 + 3 ^ 40 * 2639154 * 2
def baseEnd_2639154 : Nat := 903436348824048354358505

theorem tailTrace_2639154 : CollatzResearch.WordTrace tailWord_2639154 prefixEnd_2639154 903436348824048354358505 := by
  unfold tailWord_2639154
  simp only [CollatzResearch.WordTrace]
  refine ⟨24064463570200816115933129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64171902853868842975821677 24064463570200816115933129)
  ·
    refine ⟨18048347677650612086949847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24064463570200816115933129 18048347677650612086949847)
    ·
      refine ⟨27072521516475918130424771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18048347677650612086949847 27072521516475918130424771)
      ·
        refine ⟨40608782274713877195637157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27072521516475918130424771 40608782274713877195637157)
        ·
          refine ⟨7614146676508851974181967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40608782274713877195637157 7614146676508851974181967)
          ·
            refine ⟨11421220014763277961272951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7614146676508851974181967 11421220014763277961272951)
            ·
              refine ⟨17131830022144916941909427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11421220014763277961272951 17131830022144916941909427)
              ·
                refine ⟨25697745033217375412864141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17131830022144916941909427 25697745033217375412864141)
                ·
                  refine ⟨9636654387456515779824053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25697745033217375412864141 9636654387456515779824053)
                  ·
                    refine ⟨903436348824048354358505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9636654387456515779824053 903436348824048354358505)
                    ·
                      rfl

theorem cell22_2639154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_2639154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639154 prefixEnd_2639154 := by exact prefixLift 2639154
  have htrace : WordTrace (prefixWord ++ tailWord_2639154) baseStart_2639154 baseEnd_2639154 := by
    simpa [prefixWord, tailWord_2639154, baseEnd_2639154] using wordTrace_append hprefix tailTrace_2639154
  have hstable : (prefixWord ++ tailWord_2639154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639154).length < 2 ^ (prefixWord ++ tailWord_2639154).sum := by decide
  have hdescent : baseEnd_2639154 < baseStart_2639154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639167 : List Nat := [1, 1, 2, 2, 4, 12]
def baseStart_2639167 : Nat := 118140960795 + 2639167 * 2 ^ 59
def prefixEnd_2639167 : Nat := 4983230072969 + 3 ^ 40 * 2639167 * 2
def baseEnd_2639167 : Nat := 11153590110984205602265

theorem tailTrace_2639167 : CollatzResearch.WordTrace tailWord_2639167 prefixEnd_2639167 11153590110984205602265 := by
  unfold tailWord_2639167
  simp only [CollatzResearch.WordTrace]
  refine ⟨96258328429756167683955755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64172218953170778455970503 96258328429756167683955755)
  ·
    refine ⟨144387492644634251525933633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96258328429756167683955755 144387492644634251525933633)
    ·
      refine ⟨108290619483475688644450225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144387492644634251525933633 108290619483475688644450225)
      ·
        refine ⟨81217964612606766483337669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108290619483475688644450225 81217964612606766483337669)
        ·
          refine ⟨15228368364863768715625813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81217964612606766483337669 15228368364863768715625813)
          ·
            refine ⟨11153590110984205602265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15228368364863768715625813 11153590110984205602265)
            ·
              rfl

theorem cell22_2639167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 12].length) (baseStart_2639167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639167 prefixEnd_2639167 := by exact prefixLift 2639167
  have htrace : WordTrace (prefixWord ++ tailWord_2639167) baseStart_2639167 baseEnd_2639167 := by
    simpa [prefixWord, tailWord_2639167, baseEnd_2639167] using wordTrace_append hprefix tailTrace_2639167
  have hstable : (prefixWord ++ tailWord_2639167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639167).length < 2 ^ (prefixWord ++ tailWord_2639167).sum := by decide
  have hdescent : baseEnd_2639167 < baseStart_2639167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639229 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 7]
def baseStart_2639229 : Nat := 118140960795 + 2639229 * 2 ^ 59
def prefixEnd_2639229 : Nat := 4983230072969 + 3 ^ 40 * 2639229 * 2
def baseEnd_2639229 : Nat := 301154007618924386244425

theorem tailTrace_2639229 : CollatzResearch.WordTrace tailWord_2639229 prefixEnd_2639229 301154007618924386244425 := by
  unfold tailWord_2639229
  simp only [CollatzResearch.WordTrace]
  refine ⟨96260589755531552272712741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64173726503687701515141827 96260589755531552272712741)
  ·
    refine ⟨18048860579162166051133639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96260589755531552272712741 18048860579162166051133639)
    ·
      refine ⟨27073290868743249076700459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18048860579162166051133639 27073290868743249076700459)
      ·
        refine ⟨40609936303114873615050689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27073290868743249076700459 40609936303114873615050689)
        ·
          refine ⟨30457452227336155211288017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40609936303114873615050689 30457452227336155211288017)
          ·
            refine ⟨22843089170502116408466013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30457452227336155211288017 22843089170502116408466013)
            ·
              refine ⟨8566158438938293653174755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22843089170502116408466013 8566158438938293653174755)
              ·
                refine ⟨12849237658407440479762133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8566158438938293653174755 12849237658407440479762133)
                ·
                  refine ⟨301154007618924386244425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12849237658407440479762133 301154007618924386244425)
                  ·
                    rfl

theorem cell22_2639229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_2639229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639229 prefixEnd_2639229 := by exact prefixLift 2639229
  have htrace : WordTrace (prefixWord ++ tailWord_2639229) baseStart_2639229 baseEnd_2639229 := by
    simpa [prefixWord, tailWord_2639229, baseEnd_2639229] using wordTrace_append hprefix tailTrace_2639229
  have hstable : (prefixWord ++ tailWord_2639229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639229).length < 2 ^ (prefixWord ++ tailWord_2639229).sum := by decide
  have hdescent : baseEnd_2639229 < baseStart_2639229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639244 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_2639244 : Nat := 118140960795 + 2639244 * 2 ^ 59
def prefixEnd_2639244 : Nat := 4983230072969 + 3 ^ 40 * 2639244 * 2
def baseEnd_2639244 : Nat := 903467157663318119608229

theorem tailTrace_2639244 : CollatzResearch.WordTrace tailWord_2639244 prefixEnd_2639244 903467157663318119608229 := by
  unfold tailWord_2639244
  simp only [CollatzResearch.WordTrace]
  refine ⟨48130568425238604917254393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64174091233651473223005857 48130568425238604917254393)
  ·
    refine ⟨36097926318928953687940795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48130568425238604917254393 36097926318928953687940795)
    ·
      refine ⟨54146889478393430531911193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36097926318928953687940795 54146889478393430531911193)
      ·
        refine ⟨40610167108795072898933395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54146889478393430531911193 40610167108795072898933395)
        ·
          refine ⟨60915250663192609348400093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40610167108795072898933395 60915250663192609348400093)
          ·
            refine ⟨22843218998697228505650035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60915250663192609348400093 22843218998697228505650035)
            ·
              refine ⟨34264828498045842758475053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22843218998697228505650035 34264828498045842758475053)
              ·
                refine ⟨12849310686767191034428145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34264828498045842758475053 12849310686767191034428145)
                ·
                  refine ⟨9636983015075393275821109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12849310686767191034428145 9636983015075393275821109)
                  ·
                    refine ⟨903467157663318119608229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9636983015075393275821109 903467157663318119608229)
                    ·
                      rfl

theorem cell22_2639244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_2639244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639244 prefixEnd_2639244 := by exact prefixLift 2639244
  have htrace : WordTrace (prefixWord ++ tailWord_2639244) baseStart_2639244 baseEnd_2639244 := by
    simpa [prefixWord, tailWord_2639244, baseEnd_2639244] using wordTrace_append hprefix tailTrace_2639244
  have hstable : (prefixWord ++ tailWord_2639244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639244).length < 2 ^ (prefixWord ++ tailWord_2639244).sum := by decide
  have hdescent : baseEnd_2639244 < baseStart_2639244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639276 : List Nat := [2, 2, 1, 1, 1, 1, 6, 3, 1, 4]
def baseStart_2639276 : Nat := 118140960795 + 2639276 * 2 ^ 59
def prefixEnd_2639276 : Nat := 4983230072969 + 3 ^ 40 * 2639276 * 2
def baseEnd_2639276 : Nat := 903478111917280702808131

theorem tailTrace_2639276 : CollatzResearch.WordTrace tailWord_2639276 prefixEnd_2639276 903478111917280702808131 := by
  unfold tailWord_2639276
  simp only [CollatzResearch.WordTrace]
  refine ⟨48131151993180639649836841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64174869324240852866449121 48131151993180639649836841)
  ·
    refine ⟨36098363994885479737377631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48131151993180639649836841 36098363994885479737377631)
    ·
      refine ⟨54147545992328219606066447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36098363994885479737377631 54147545992328219606066447)
      ·
        refine ⟨81221318988492329409099671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54147545992328219606066447 81221318988492329409099671)
        ·
          refine ⟨121831978482738494113649507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81221318988492329409099671 121831978482738494113649507)
          ·
            refine ⟨182747967724107741170474261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121831978482738494113649507 182747967724107741170474261)
            ·
              refine ⟨8566310987067550367365981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 182747967724107741170474261 8566310987067550367365981)
              ·
                refine ⟨3212366620150331387762243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8566310987067550367365981 3212366620150331387762243)
                ·
                  refine ⟨4818549930225497081643365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212366620150331387762243 4818549930225497081643365)
                  ·
                    refine ⟨903478111917280702808131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4818549930225497081643365 903478111917280702808131)
                    ·
                      rfl

theorem cell22_2639276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_2639276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639276 prefixEnd_2639276 := by exact prefixLift 2639276
  have htrace : WordTrace (prefixWord ++ tailWord_2639276) baseStart_2639276 baseEnd_2639276 := by
    simpa [prefixWord, tailWord_2639276, baseEnd_2639276] using wordTrace_append hprefix tailTrace_2639276
  have hstable : (prefixWord ++ tailWord_2639276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639276).length < 2 ^ (prefixWord ++ tailWord_2639276).sum := by decide
  have hdescent : baseEnd_2639276 < baseStart_2639276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639321 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 2, 4]
def baseStart_2639321 : Nat := 118140960795 + 2639321 * 2 ^ 59
def prefixEnd_2639321 : Nat := 4983230072969 + 3 ^ 40 * 2639321 * 2
def baseEnd_2639321 : Nat := 903493516336915585432993

theorem tailTrace_2639321 : CollatzResearch.WordTrace tailWord_2639321 prefixEnd_2639321 903493516336915585432993 := by
  unfold tailWord_2639321
  simp only [CollatzResearch.WordTrace]
  refine ⟨96263945271198251985061817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64175963514132167990041211 96263945271198251985061817)
  ·
    refine ⟨72197958953398688988796363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96263945271198251985061817 72197958953398688988796363)
    ·
      refine ⟨108296938430098033483194545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72197958953398688988796363 108296938430098033483194545)
      ·
        refine ⟨81222703822573525112395909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108296938430098033483194545 81222703822573525112395909)
        ·
          refine ⟨15229256966732535958574233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81222703822573525112395909 15229256966732535958574233)
          ·
            refine ⟨11421942725049401968930675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15229256966732535958574233 11421942725049401968930675)
            ·
              refine ⟨17132914087574102953396013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11421942725049401968930675 17132914087574102953396013)
              ·
                refine ⟨6424842782840288607523505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17132914087574102953396013 6424842782840288607523505)
                ·
                  refine ⟨4818632087130216455642629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6424842782840288607523505 4818632087130216455642629)
                  ·
                    refine ⟨903493516336915585432993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4818632087130216455642629 903493516336915585432993)
                    ·
                      rfl

theorem cell22_2639321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_2639321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639321 prefixEnd_2639321 := by exact prefixLift 2639321
  have htrace : WordTrace (prefixWord ++ tailWord_2639321) baseStart_2639321 baseEnd_2639321 := by
    simpa [prefixWord, tailWord_2639321, baseEnd_2639321] using wordTrace_append hprefix tailTrace_2639321
  have hstable : (prefixWord ++ tailWord_2639321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639321).length < 2 ^ (prefixWord ++ tailWord_2639321).sum := by decide
  have hdescent : baseEnd_2639321 < baseStart_2639321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639441 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 3, 5]
def baseStart_2639441 : Nat := 118140960795 + 2639441 * 2 ^ 59
def prefixEnd_2639441 : Nat := 4983230072969 + 3 ^ 40 * 2639441 * 2
def baseEnd_2639441 : Nat := 903534594789275272432625

theorem tailTrace_2639441 : CollatzResearch.WordTrace tailWord_2639441 prefixEnd_2639441 903534594789275272432625 := by
  unfold tailWord_2639441
  simp only [CollatzResearch.WordTrace]
  refine ⟨96268322030763512479430177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64178881353842341652953451 96268322030763512479430177)
  ·
    refine ⟨72201241523072634359572633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96268322030763512479430177 72201241523072634359572633)
    ·
      refine ⟨54150931142304475769679475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72201241523072634359572633 54150931142304475769679475)
      ·
        refine ⟨81226396713456713654519213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54150931142304475769679475 81226396713456713654519213)
        ·
          refine ⟨30459898767546267620444705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81226396713456713654519213 30459898767546267620444705)
          ·
            refine ⟨22844924075659700715333529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30459898767546267620444705 22844924075659700715333529)
            ·
              refine ⟨17133693056744775536500147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22844924075659700715333529 17133693056744775536500147)
              ·
                refine ⟨25700539585117163304750221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17133693056744775536500147 25700539585117163304750221)
                ·
                  refine ⟨9637702344418936239281333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25700539585117163304750221 9637702344418936239281333)
                  ·
                    refine ⟨903534594789275272432625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9637702344418936239281333 903534594789275272432625)
                    ·
                      rfl

theorem cell22_2639441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_2639441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639441 prefixEnd_2639441 := by exact prefixLift 2639441
  have htrace : WordTrace (prefixWord ++ tailWord_2639441) baseStart_2639441 baseEnd_2639441 := by
    simpa [prefixWord, tailWord_2639441, baseEnd_2639441] using wordTrace_append hprefix tailTrace_2639441
  have hstable : (prefixWord ++ tailWord_2639441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639441).length < 2 ^ (prefixWord ++ tailWord_2639441).sum := by decide
  have hdescent : baseEnd_2639441 < baseStart_2639441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639522 : List Nat := [3, 3, 1, 4, 1, 2, 1, 7]
def baseStart_2639522 : Nat := 118140960795 + 2639522 * 2 ^ 59
def prefixEnd_2639522 : Nat := 4983230072969 + 3 ^ 40 * 2639522 * 2
def baseEnd_2639522 : Nat := 100395813638290895684153

theorem tailTrace_2639522 : CollatzResearch.WordTrace tailWord_2639522 prefixEnd_2639522 100395813638290895684153 := by
  unfold tailWord_2639522
  simp only [CollatzResearch.WordTrace]
  refine ⟨24067819085867515828282205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64180850895646708875419213 24067819085867515828282205)
  ·
    refine ⟨9025432157200318435605827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24067819085867515828282205 9025432157200318435605827)
    ·
      refine ⟨13538148235800477653408741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9025432157200318435605827 13538148235800477653408741)
      ·
        refine ⟨2538402794212589560014139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13538148235800477653408741 2538402794212589560014139)
        ·
          refine ⟨3807604191318884340021209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2538402794212589560014139 3807604191318884340021209)
          ·
            refine ⟨2855703143489163255015907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3807604191318884340021209 2855703143489163255015907)
            ·
              refine ⟨4283554715233744882523861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2855703143489163255015907 4283554715233744882523861)
              ·
                refine ⟨100395813638290895684153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4283554715233744882523861 100395813638290895684153)
                ·
                  rfl

theorem cell22_2639522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 7].length) (baseStart_2639522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639522 prefixEnd_2639522 := by exact prefixLift 2639522
  have htrace : WordTrace (prefixWord ++ tailWord_2639522) baseStart_2639522 baseEnd_2639522 := by
    simpa [prefixWord, tailWord_2639522, baseEnd_2639522] using wordTrace_append hprefix tailTrace_2639522
  have hstable : (prefixWord ++ tailWord_2639522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639522).length < 2 ^ (prefixWord ++ tailWord_2639522).sum := by decide
  have hdescent : baseEnd_2639522 < baseStart_2639522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639578 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 6]
def baseStart_2639578 : Nat := 118140960795 + 2639578 * 2 ^ 59
def prefixEnd_2639578 : Nat := 4983230072969 + 3 ^ 40 * 2639578 * 2
def baseEnd_2639578 : Nat := 301193830896350860585735

theorem tailTrace_2639578 : CollatzResearch.WordTrace tailWord_2639578 prefixEnd_2639578 301193830896350860585735 := by
  unfold tailWord_2639578
  simp only [CollatzResearch.WordTrace]
  refine ⟨24068329707816796219291847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64182212554178123251444925 24068329707816796219291847)
  ·
    refine ⟨36102494561725194328937771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24068329707816796219291847 36102494561725194328937771)
    ·
      refine ⟨54153741842587791493406657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36102494561725194328937771 54153741842587791493406657)
      ·
        refine ⟨40615306381940843620054993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54153741842587791493406657 40615306381940843620054993)
        ·
          refine ⟨30461479786455632715041245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40615306381940843620054993 30461479786455632715041245)
          ·
            refine ⟨11423054919920862268140467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30461479786455632715041245 11423054919920862268140467)
            ·
              refine ⟨17134582379881293402210701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11423054919920862268140467 17134582379881293402210701)
              ·
                refine ⟨6425468392455485025829013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17134582379881293402210701 6425468392455485025829013)
                ·
                  refine ⟨301193830896350860585735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6425468392455485025829013 301193830896350860585735)
                  ·
                    rfl

theorem cell22_2639578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_2639578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639578 prefixEnd_2639578 := by exact prefixLift 2639578
  have htrace : WordTrace (prefixWord ++ tailWord_2639578) baseStart_2639578 baseEnd_2639578 := by
    simpa [prefixWord, tailWord_2639578, baseEnd_2639578] using wordTrace_append hprefix tailTrace_2639578
  have hstable : (prefixWord ++ tailWord_2639578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639578).length < 2 ^ (prefixWord ++ tailWord_2639578).sum := by decide
  have hdescent : baseEnd_2639578 < baseStart_2639578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639597 : List Nat := [1, 5, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_2639597 : Nat := 118140960795 + 2639597 * 2 ^ 59
def prefixEnd_2639597 : Nat := 4983230072969 + 3 ^ 40 * 2639597 * 2
def baseEnd_2639597 : Nat := 903587996777342865532147

theorem tailTrace_2639597 : CollatzResearch.WordTrace tailWord_2639597 prefixEnd_2639597 903587996777342865532147 := by
  unfold tailWord_2639597
  simp only [CollatzResearch.WordTrace]
  refine ⟨96274011818198351122109045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64182674545465567414739363 96274011818198351122109045)
  ·
    refine ⟨9025688607956095417697723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96274011818198351122109045 9025688607956095417697723)
    ·
      refine ⟨13538532911934143126546585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9025688607956095417697723 13538532911934143126546585)
      ·
        refine ⟨10153899683950607344909939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13538532911934143126546585 10153899683950607344909939)
        ·
          refine ⟨15230849525925911017364909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10153899683950607344909939 15230849525925911017364909)
          ·
            refine ⟨5711568572222216631511841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15230849525925911017364909 5711568572222216631511841)
            ·
              refine ⟨4283676429166662473633881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5711568572222216631511841 4283676429166662473633881)
              ·
                refine ⟨3212757321874996855225411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4283676429166662473633881 3212757321874996855225411)
                ·
                  refine ⟨4819135982812495282838117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212757321874996855225411 4819135982812495282838117)
                  ·
                    refine ⟨903587996777342865532147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4819135982812495282838117 903587996777342865532147)
                    ·
                      rfl

theorem cell22_2639597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_2639597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639597 prefixEnd_2639597 := by exact prefixLift 2639597
  have htrace : WordTrace (prefixWord ++ tailWord_2639597) baseStart_2639597 baseEnd_2639597 := by
    simpa [prefixWord, tailWord_2639597, baseEnd_2639597] using wordTrace_append hprefix tailTrace_2639597
  have hstable : (prefixWord ++ tailWord_2639597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639597).length < 2 ^ (prefixWord ++ tailWord_2639597).sum := by decide
  have hdescent : baseEnd_2639597 < baseStart_2639597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639622 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2639622 : Nat := 118140960795 + 2639622 * 2 ^ 59
def prefixEnd_2639622 : Nat := 4983230072969 + 3 ^ 40 * 2639622 * 2
def baseEnd_2639622 : Nat := 903596554788251133657071

theorem tailTrace_2639622 : CollatzResearch.WordTrace tailWord_2639622 prefixEnd_2639622 903596554788251133657071 := by
  unfold tailWord_2639622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3008591363847118137242785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64183282428738520261179413 3008591363847118137242785)
  ·
    refine ⟨2256443522885338602932089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3008591363847118137242785 2256443522885338602932089)
    ·
      refine ⟨1692332642164003952199067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2256443522885338602932089 1692332642164003952199067)
      ·
        refine ⟨2538498963246005928298601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692332642164003952199067 2538498963246005928298601)
        ·
          refine ⟨1903874222434504446223951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2538498963246005928298601 1903874222434504446223951)
          ·
            refine ⟨2855811333651756669335927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1903874222434504446223951 2855811333651756669335927)
            ·
              refine ⟨4283717000477635004003891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2855811333651756669335927 4283717000477635004003891)
              ·
                refine ⟨6425575500716452506005837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4283717000477635004003891 6425575500716452506005837)
                ·
                  refine ⟨2409590812768669689752189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6425575500716452506005837 2409590812768669689752189)
                  ·
                    refine ⟨903596554788251133657071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2409590812768669689752189 903596554788251133657071)
                    ·
                      rfl

theorem cell22_2639622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2639622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639622 prefixEnd_2639622 := by exact prefixLift 2639622
  have htrace : WordTrace (prefixWord ++ tailWord_2639622) baseStart_2639622 baseEnd_2639622 := by
    simpa [prefixWord, tailWord_2639622, baseEnd_2639622] using wordTrace_append hprefix tailTrace_2639622
  have hstable : (prefixWord ++ tailWord_2639622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639622).length < 2 ^ (prefixWord ++ tailWord_2639622).sum := by decide
  have hdescent : baseEnd_2639622 < baseStart_2639622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639685 : List Nat := [1, 3, 1, 1, 1, 2, 6, 2, 5]
def baseStart_2639685 : Nat := 118140960795 + 2639685 * 2 ^ 59
def prefixEnd_2639685 : Nat := 4983230072969 + 3 ^ 40 * 2639685 * 2
def baseEnd_2639685 : Nat := 301206040325246656443959

theorem tailTrace_2639685 : CollatzResearch.WordTrace tailWord_2639685 prefixEnd_2639685 301206040325246656443959 := by
  unfold tailWord_2639685
  simp only [CollatzResearch.WordTrace]
  refine ⟨96277221441879542151312509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64184814294586361434208339 96277221441879542151312509)
  ·
    refine ⟨36103958040704828306742191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96277221441879542151312509 36103958040704828306742191)
    ·
      refine ⟨54155937061057242460113287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36103958040704828306742191 54155937061057242460113287)
      ·
        refine ⟨81233905591585863690169931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54155937061057242460113287 81233905591585863690169931)
        ·
          refine ⟨121850858387378795535254897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81233905591585863690169931 121850858387378795535254897)
          ·
            refine ⟨91388143790534096651441173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121850858387378795535254897 91388143790534096651441173)
            ·
              refine ⟨4283819240181285780536305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91388143790534096651441173 4283819240181285780536305)
              ·
                refine ⟨3212864430135964335402229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4283819240181285780536305 3212864430135964335402229)
                ·
                  refine ⟨301206040325246656443959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3212864430135964335402229 301206040325246656443959)
                  ·
                    rfl

theorem cell22_2639685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_2639685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639685 prefixEnd_2639685 := by exact prefixLift 2639685
  have htrace : WordTrace (prefixWord ++ tailWord_2639685) baseStart_2639685 baseEnd_2639685 := by
    simpa [prefixWord, tailWord_2639685, baseEnd_2639685] using wordTrace_append hprefix tailTrace_2639685
  have hstable : (prefixWord ++ tailWord_2639685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639685).length < 2 ^ (prefixWord ++ tailWord_2639685).sum := by decide
  have hdescent : baseEnd_2639685 < baseStart_2639685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639700 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_2639700 : Nat := 118140960795 + 2639700 * 2 ^ 59
def prefixEnd_2639700 : Nat := 4983230072969 + 3 ^ 40 * 2639700 * 2
def baseEnd_2639700 : Nat := 903623255782284930206831

theorem tailTrace_2639700 : CollatzResearch.WordTrace tailWord_2639700 prefixEnd_2639700 903623255782284930206831 := by
  unfold tailWord_2639700
  simp only [CollatzResearch.WordTrace]
  refine ⟨48138884268412599856554277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64185179024550133142072369 48138884268412599856554277)
  ·
    refine ⟨9026040800327362473103927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48138884268412599856554277 9026040800327362473103927)
    ·
      refine ⟨13539061200491043709655891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9026040800327362473103927 13539061200491043709655891)
      ·
        refine ⟨20308591800736565564483837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13539061200491043709655891 20308591800736565564483837)
        ·
          refine ⟨7615721925276212086681439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20308591800736565564483837 7615721925276212086681439)
          ·
            refine ⟨11423582887914318130022159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7615721925276212086681439 11423582887914318130022159)
            ·
              refine ⟨17135374331871477195033239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11423582887914318130022159 17135374331871477195033239)
              ·
                refine ⟨25703061497807215792549859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17135374331871477195033239 25703061497807215792549859)
                ·
                  refine ⟨38554592246710823688824789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25703061497807215792549859 38554592246710823688824789)
                  ·
                    refine ⟨903623255782284930206831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38554592246710823688824789 903623255782284930206831)
                    ·
                      rfl

theorem cell22_2639700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_2639700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639700 prefixEnd_2639700 := by exact prefixLift 2639700
  have htrace : WordTrace (prefixWord ++ tailWord_2639700) baseStart_2639700 baseEnd_2639700 := by
    simpa [prefixWord, tailWord_2639700, baseEnd_2639700] using wordTrace_append hprefix tailTrace_2639700
  have hstable : (prefixWord ++ tailWord_2639700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639700).length < 2 ^ (prefixWord ++ tailWord_2639700).sum := by decide
  have hdescent : baseEnd_2639700 < baseStart_2639700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639747 : List Nat := [1, 1, 1, 3, 4, 2, 2, 4, 4]
def baseStart_2639747 : Nat := 118140960795 + 2639747 * 2 ^ 59
def prefixEnd_2639747 : Nat := 4983230072969 + 3 ^ 40 * 2639747 * 2
def baseEnd_2639747 : Nat := 301213114947597491427229

theorem tailTrace_2639747 : CollatzResearch.WordTrace tailWord_2639747 prefixEnd_2639747 301213114947597491427229 := by
  unfold tailWord_2639747
  simp only [CollatzResearch.WordTrace]
  refine ⟨96279482767654926740069495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64186321845103284493379663 96279482767654926740069495)
  ·
    refine ⟨144419224151482390110104243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96279482767654926740069495 144419224151482390110104243)
    ·
      refine ⟨216628836227223585165156365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144419224151482390110104243 216628836227223585165156365)
      ·
        refine ⟨81235813585208844436933637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216628836227223585165156365 81235813585208844436933637)
        ·
          refine ⟨15231715047226658331925057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81235813585208844436933637 15231715047226658331925057)
          ·
            refine ⟨11423786285419993748943793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15231715047226658331925057 11423786285419993748943793)
            ·
              refine ⟨8567839714064995311707845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11423786285419993748943793 8567839714064995311707845)
              ·
                refine ⟨1606469946387186620945221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8567839714064995311707845 1606469946387186620945221)
                ·
                  refine ⟨301213114947597491427229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1606469946387186620945221 301213114947597491427229)
                  ·
                    rfl

theorem cell22_2639747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 4].length) (baseStart_2639747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639747 prefixEnd_2639747 := by exact prefixLift 2639747
  have htrace : WordTrace (prefixWord ++ tailWord_2639747) baseStart_2639747 baseEnd_2639747 := by
    simpa [prefixWord, tailWord_2639747, baseEnd_2639747] using wordTrace_append hprefix tailTrace_2639747
  have hstable : (prefixWord ++ tailWord_2639747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639747).length < 2 ^ (prefixWord ++ tailWord_2639747).sum := by decide
  have hdescent : baseEnd_2639747 < baseStart_2639747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639854 : List Nat := [4, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_2639854 : Nat := 118140960795 + 2639854 * 2 ^ 59
def prefixEnd_2639854 : Nat := 4983230072969 + 3 ^ 40 * 2639854 * 2
def baseEnd_2639854 : Nat := 301225324376493287285453

theorem tailTrace_2639854 : CollatzResearch.WordTrace tailWord_2639854 prefixEnd_2639854 301225324376493287285453 := by
  unfold tailWord_2639854
  simp only [CollatzResearch.WordTrace]
  refine ⟨12035423172283410501776827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64188923585511522676143077 12035423172283410501776827)
  ·
    refine ⟨18053134758425115752665241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12035423172283410501776827 18053134758425115752665241)
    ·
      refine ⟨13539851068818836814498931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18053134758425115752665241 13539851068818836814498931)
      ·
        refine ⟨20309776603228255221748397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13539851068818836814498931 20309776603228255221748397)
        ·
          refine ⟨7616166226210595708155649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20309776603228255221748397 7616166226210595708155649)
          ·
            refine ⟨5712124669657946781116737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7616166226210595708155649 5712124669657946781116737)
            ·
              refine ⟨4284093502243460085837553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5712124669657946781116737 4284093502243460085837553)
              ·
                refine ⟨3213070126682595064378165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4284093502243460085837553 3213070126682595064378165)
                ·
                  refine ⟨301225324376493287285453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3213070126682595064378165 301225324376493287285453)
                  ·
                    rfl

theorem cell22_2639854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_2639854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639854 prefixEnd_2639854 := by exact prefixLift 2639854
  have htrace : WordTrace (prefixWord ++ tailWord_2639854) baseStart_2639854 baseEnd_2639854 := by
    simpa [prefixWord, tailWord_2639854, baseEnd_2639854] using wordTrace_append hprefix tailTrace_2639854
  have hstable : (prefixWord ++ tailWord_2639854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639854).length < 2 ^ (prefixWord ++ tailWord_2639854).sum := by decide
  have hdescent : baseEnd_2639854 < baseStart_2639854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639897 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 4, 3]
def baseStart_2639897 : Nat := 118140960795 + 2639897 * 2 ^ 59
def prefixEnd_2639897 : Nat := 4983230072969 + 3 ^ 40 * 2639897 * 2
def baseEnd_2639897 : Nat := 903690692908242083031227

theorem tailTrace_2639897 : CollatzResearch.WordTrace tailWord_2639897 prefixEnd_2639897 903690692908242083031227 := by
  unfold tailWord_2639897
  simp only [CollatzResearch.WordTrace]
  refine ⟨96284953717111502358029945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64189969144741001572019963 96284953717111502358029945)
  ·
    refine ⟨72213715287833626768522459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96284953717111502358029945 72213715287833626768522459)
    ·
      refine ⟨108320572931750440152783689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72213715287833626768522459 108320572931750440152783689)
      ·
        refine ⟨81240429698812830114587767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108320572931750440152783689 81240429698812830114587767)
        ·
          refine ⟨121860644548219245171881651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81240429698812830114587767 121860644548219245171881651)
          ·
            refine ⟨182790966822328867757822477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121860644548219245171881651 182790966822328867757822477)
            ·
              refine ⟨68546612558373325409183429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182790966822328867757822477 68546612558373325409183429)
              ·
                refine ⟨12852489854694998514221893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68546612558373325409183429 12852489854694998514221893)
                ·
                  refine ⟨2409841847755312221416605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12852489854694998514221893 2409841847755312221416605)
                  ·
                    refine ⟨903690692908242083031227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2409841847755312221416605 903690692908242083031227)
                    ·
                      rfl

theorem cell22_2639897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 3].length) (baseStart_2639897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639897 prefixEnd_2639897 := by exact prefixLift 2639897
  have htrace : WordTrace (prefixWord ++ tailWord_2639897) baseStart_2639897 baseEnd_2639897 := by
    simpa [prefixWord, tailWord_2639897, baseEnd_2639897] using wordTrace_append hprefix tailTrace_2639897
  have hstable : (prefixWord ++ tailWord_2639897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639897).length < 2 ^ (prefixWord ++ tailWord_2639897).sum := by decide
  have hdescent : baseEnd_2639897 < baseStart_2639897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639901 : List Nat := [1, 4, 2, 2, 2, 1, 4, 1, 1, 4]
def baseStart_2639901 : Nat := 118140960795 + 2639901 * 2 ^ 59
def prefixEnd_2639901 : Nat := 4983230072969 + 3 ^ 40 * 2639901 * 2
def baseEnd_2639901 : Nat := 903692062189987405931215

theorem tailTrace_2639901 : CollatzResearch.WordTrace tailWord_2639901 prefixEnd_2639901 903692062189987405931215 := by
  unfold tailWord_2639901
  simp only [CollatzResearch.WordTrace]
  refine ⟨96285099609097011041175557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64190066406064674027450371 96285099609097011041175557)
  ·
    refine ⟨18053456176705689570220417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96285099609097011041175557 18053456176705689570220417)
    ·
      refine ⟨13540092132529267177665313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18053456176705689570220417 13540092132529267177665313)
      ·
        refine ⟨10155069099396950383248985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13540092132529267177665313 10155069099396950383248985)
        ·
          refine ⟨7616301824547712787436739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10155069099396950383248985 7616301824547712787436739)
          ·
            refine ⟨11424452736821569181155109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7616301824547712787436739 11424452736821569181155109)
            ·
              refine ⟨2142084888154044221466583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11424452736821569181155109 2142084888154044221466583)
              ·
                refine ⟨3213127332231066332199875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2142084888154044221466583 3213127332231066332199875)
                ·
                  refine ⟨4819690998346599498299813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213127332231066332199875 4819690998346599498299813)
                  ·
                    refine ⟨903692062189987405931215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4819690998346599498299813 903692062189987405931215)
                    ·
                      rfl

theorem cell22_2639901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_2639901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639901 prefixEnd_2639901 := by exact prefixLift 2639901
  have htrace : WordTrace (prefixWord ++ tailWord_2639901) baseStart_2639901 baseEnd_2639901 := by
    simpa [prefixWord, tailWord_2639901, baseEnd_2639901] using wordTrace_append hprefix tailTrace_2639901
  have hstable : (prefixWord ++ tailWord_2639901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639901).length < 2 ^ (prefixWord ++ tailWord_2639901).sum := by decide
  have hdescent : baseEnd_2639901 < baseStart_2639901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639972 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 7]
def baseStart_2639972 : Nat := 118140960795 + 2639972 * 2 ^ 59
def prefixEnd_2639972 : Nat := 4983230072969 + 3 ^ 40 * 2639972 * 2
def baseEnd_2639972 : Nat := 301238788980322295801999

theorem tailTrace_2639972 : CollatzResearch.WordTrace tailWord_2639972 prefixEnd_2639972 301238788980322295801999 := by
  unfold tailWord_2639972
  simp only [CollatzResearch.WordTrace]
  refine ⟨48143844595919895083505085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64191792794559860111340113 48143844595919895083505085)
  ·
    refine ⟨18053941723469960656314407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48143844595919895083505085 18053941723469960656314407)
    ·
      refine ⟨27080912585204940984471611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18053941723469960656314407 27080912585204940984471611)
      ·
        refine ⟨40621368877807411476707417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27080912585204940984471611 40621368877807411476707417)
        ·
          refine ⟨30466026658355558607530563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40621368877807411476707417 30466026658355558607530563)
          ·
            refine ⟨45699039987533337911295845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30466026658355558607530563 45699039987533337911295845)
            ·
              refine ⟨8568569997662500858367971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45699039987533337911295845 8568569997662500858367971)
              ·
                refine ⟨12852854996493751287551957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8568569997662500858367971 12852854996493751287551957)
                ·
                  refine ⟨301238788980322295801999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12852854996493751287551957 301238788980322295801999)
                  ·
                    rfl

theorem cell22_2639972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_2639972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2639972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2639972 prefixEnd_2639972 := by exact prefixLift 2639972
  have htrace : WordTrace (prefixWord ++ tailWord_2639972) baseStart_2639972 baseEnd_2639972 := by
    simpa [prefixWord, tailWord_2639972, baseEnd_2639972] using wordTrace_append hprefix tailTrace_2639972
  have hstable : (prefixWord ++ tailWord_2639972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639972).length < 2 ^ (prefixWord ++ tailWord_2639972).sum := by decide
  have hdescent : baseEnd_2639972 < baseStart_2639972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640047 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 1, 6]
def baseStart_2640047 : Nat := 118140960795 + 2640047 * 2 ^ 59
def prefixEnd_2640047 : Nat := 4983230072969 + 3 ^ 40 * 2640047 * 2
def baseEnd_2640047 : Nat := 903742040973691691780767

theorem tailTrace_2640047 : CollatzResearch.WordTrace tailWord_2640047 prefixEnd_2640047 903742040973691691780767 := by
  unfold tailWord_2640047
  simp only [CollatzResearch.WordTrace]
  refine ⟨96290424666568077975990395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64193616444378718650660263 96290424666568077975990395)
  ·
    refine ⟨144435636999852116963985593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96290424666568077975990395 144435636999852116963985593)
    ·
      refine ⟨108326727749889087722989195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144435636999852116963985593 108326727749889087722989195)
      ·
        refine ⟨162490091624833631584483793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108326727749889087722989195 162490091624833631584483793)
        ·
          refine ⟨121867568718625223688362845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162490091624833631584483793 121867568718625223688362845)
          ·
            refine ⟨45700338269484458883136067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121867568718625223688362845 45700338269484458883136067)
            ·
              refine ⟨68550507404226688324704101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45700338269484458883136067 68550507404226688324704101)
              ·
                refine ⟨12853220138292504060882019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68550507404226688324704101 12853220138292504060882019)
                ·
                  refine ⟨19279830207438756091323029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12853220138292504060882019 19279830207438756091323029)
                  ·
                    refine ⟨903742040973691691780767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19279830207438756091323029 903742040973691691780767)
                    ·
                      rfl

theorem cell22_2640047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_2640047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640047 prefixEnd_2640047 := by exact prefixLift 2640047
  have htrace : WordTrace (prefixWord ++ tailWord_2640047) baseStart_2640047 baseEnd_2640047 := by
    simpa [prefixWord, tailWord_2640047, baseEnd_2640047] using wordTrace_append hprefix tailTrace_2640047
  have hstable : (prefixWord ++ tailWord_2640047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640047).length < 2 ^ (prefixWord ++ tailWord_2640047).sum := by decide
  have hdescent : baseEnd_2640047 < baseStart_2640047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640064 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 1, 6]
def baseStart_2640064 : Nat := 118140960795 + 2640064 * 2 ^ 59
def prefixEnd_2640064 : Nat := 4983230072969 + 3 ^ 40 * 2640064 * 2
def baseEnd_2640064 : Nat := 903747860421109314105715

theorem tailTrace_2640064 : CollatzResearch.WordTrace tailWord_2640064 prefixEnd_2640064 903747860421109314105715 := by
  unfold tailWord_2640064
  simp only [CollatzResearch.WordTrace]
  refine ⟨48145522353753244939679623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64194029805004326586239497 48145522353753244939679623)
  ·
    refine ⟨72218283530629867409519435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48145522353753244939679623 72218283530629867409519435)
    ·
      refine ⟨108327425295944801114279153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72218283530629867409519435 108327425295944801114279153)
      ·
        refine ⟨81245568971958600835709365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108327425295944801114279153 81245568971958600835709365)
        ·
          refine ⟨7616772091121118828347753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81245568971958600835709365 7616772091121118828347753)
          ·
            refine ⟨5712579068340839121260815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7616772091121118828347753 5712579068340839121260815)
            ·
              refine ⟨8568868602511258681891223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5712579068340839121260815 8568868602511258681891223)
              ·
                refine ⟨12853302903766888022836835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8568868602511258681891223 12853302903766888022836835)
                ·
                  refine ⟨19279954355650332034255253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12853302903766888022836835 19279954355650332034255253)
                  ·
                    refine ⟨903747860421109314105715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19279954355650332034255253 903747860421109314105715)
                    ·
                      rfl

theorem cell22_2640064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_2640064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640064 prefixEnd_2640064 := by exact prefixLift 2640064
  have htrace : WordTrace (prefixWord ++ tailWord_2640064) baseStart_2640064 baseEnd_2640064 := by
    simpa [prefixWord, tailWord_2640064, baseEnd_2640064] using wordTrace_append hprefix tailTrace_2640064
  have hstable : (prefixWord ++ tailWord_2640064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640064).length < 2 ^ (prefixWord ++ tailWord_2640064).sum := by decide
  have hdescent : baseEnd_2640064 < baseStart_2640064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640068 : List Nat := [2, 3, 3, 1, 2, 2, 2, 3, 4]
def baseStart_2640068 : Nat := 118140960795 + 2640068 * 2 ^ 59
def prefixEnd_2640068 : Nat := 4983230072969 + 3 ^ 40 * 2640068 * 2
def baseEnd_2640068 : Nat := 301249743234284879001901

theorem tailTrace_2640068 : CollatzResearch.WordTrace tailWord_2640068 prefixEnd_2640068 301249743234284879001901 := by
  unfold tailWord_2640068
  simp only [CollatzResearch.WordTrace]
  refine ⟨48145595299745999281252429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64194127066327999041669905 48145595299745999281252429)
  ·
    refine ⟨18054598237404749730469661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48145595299745999281252429 18054598237404749730469661)
    ·
      refine ⟨6770474339026781148926123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18054598237404749730469661 6770474339026781148926123)
      ·
        refine ⟨10155711508540171723389185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6770474339026781148926123 10155711508540171723389185)
        ·
          refine ⟨7616783631405128792541889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10155711508540171723389185 7616783631405128792541889)
          ·
            refine ⟨5712587723553846594406417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7616783631405128792541889 5712587723553846594406417)
            ·
              refine ⟨4284440792665384945804813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5712587723553846594406417 4284440792665384945804813)
              ·
                refine ⟨1606665297249519354676805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4284440792665384945804813 1606665297249519354676805)
                ·
                  refine ⟨301249743234284879001901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1606665297249519354676805 301249743234284879001901)
                  ·
                    rfl

theorem cell22_2640068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_2640068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640068 prefixEnd_2640068 := by exact prefixLift 2640068
  have htrace : WordTrace (prefixWord ++ tailWord_2640068) baseStart_2640068 baseEnd_2640068 := by
    simpa [prefixWord, tailWord_2640068, baseEnd_2640068] using wordTrace_append hprefix tailTrace_2640068
  have hstable : (prefixWord ++ tailWord_2640068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640068).length < 2 ^ (prefixWord ++ tailWord_2640068).sum := by decide
  have hdescent : baseEnd_2640068 < baseStart_2640068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640111 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 3, 3]
def baseStart_2640111 : Nat := 118140960795 + 2640111 * 2 ^ 59
def prefixEnd_2640111 : Nat := 4983230072969 + 3 ^ 40 * 2640111 * 2
def baseEnd_2640111 : Nat := 903763949481616858180571

theorem tailTrace_2640111 : CollatzResearch.WordTrace tailWord_2640111 prefixEnd_2640111 903763949481616858180571 := by
  unfold tailWord_2640111
  simp only [CollatzResearch.WordTrace]
  refine ⟨96292758938336216906320187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64195172625557477937546791 96292758938336216906320187)
  ·
    refine ⟨144439138407504325359480281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96292758938336216906320187 144439138407504325359480281)
    ·
      refine ⟨108329353805628244019610211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144439138407504325359480281 108329353805628244019610211)
      ·
        refine ⟨162494030708442366029415317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108329353805628244019610211 162494030708442366029415317)
        ·
          refine ⟨7616907689458235907628843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 162494030708442366029415317 7616907689458235907628843)
          ·
            refine ⟨11425361534187353861443265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7616907689458235907628843 11425361534187353861443265)
            ·
              refine ⟨8569021150640515396082449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11425361534187353861443265 8569021150640515396082449)
              ·
                refine ⟨6426765862980386547061837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8569021150640515396082449 6426765862980386547061837)
                ·
                  refine ⟨2410037198617644955148189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6426765862980386547061837 2410037198617644955148189)
                  ·
                    refine ⟨903763949481616858180571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2410037198617644955148189 903763949481616858180571)
                    ·
                      rfl

theorem cell22_2640111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 3].length) (baseStart_2640111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640111 prefixEnd_2640111 := by exact prefixLift 2640111
  have htrace : WordTrace (prefixWord ++ tailWord_2640111) baseStart_2640111 baseEnd_2640111 := by
    simpa [prefixWord, tailWord_2640111, baseEnd_2640111] using wordTrace_append hprefix tailTrace_2640111
  have hstable : (prefixWord ++ tailWord_2640111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640111).length < 2 ^ (prefixWord ++ tailWord_2640111).sum := by decide
  have hdescent : baseEnd_2640111 < baseStart_2640111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640124 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 7]
def baseStart_2640124 : Nat := 118140960795 + 2640124 * 2 ^ 59
def prefixEnd_2640124 : Nat := 4983230072969 + 3 ^ 40 * 2640124 * 2
def baseEnd_2640124 : Nat := 301256133215763052535177

theorem tailTrace_2640124 : CollatzResearch.WordTrace tailWord_2640124 prefixEnd_2640124 301256133215763052535177 := by
  unfold tailWord_2640124
  simp only [CollatzResearch.WordTrace]
  refine ⟨48146616543644560063271713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64195488724859413417695617 48146616543644560063271713)
  ·
    refine ⟨36109962407733420047453785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48146616543644560063271713 36109962407733420047453785)
    ·
      refine ⟨27082471805800065035590339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36109962407733420047453785 27082471805800065035590339)
      ·
        refine ⟨40623707708700097553385509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27082471805800065035590339 40623707708700097553385509)
        ·
          refine ⟨7616945195381268291259783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40623707708700097553385509 7616945195381268291259783)
          ·
            refine ⟨11425417793071902436889675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7616945195381268291259783 11425417793071902436889675)
            ·
              refine ⟨17138126689607853655334513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11425417793071902436889675 17138126689607853655334513)
              ·
                refine ⟨12853595017205890241500885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17138126689607853655334513 12853595017205890241500885)
                ·
                  refine ⟨301256133215763052535177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12853595017205890241500885 301256133215763052535177)
                  ·
                    rfl

theorem cell22_2640124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_2640124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640124 prefixEnd_2640124 := by exact prefixLift 2640124
  have htrace : WordTrace (prefixWord ++ tailWord_2640124) baseStart_2640124 baseEnd_2640124 := by
    simpa [prefixWord, tailWord_2640124, baseEnd_2640124] using wordTrace_append hprefix tailTrace_2640124
  have hstable : (prefixWord ++ tailWord_2640124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640124).length < 2 ^ (prefixWord ++ tailWord_2640124).sum := by decide
  have hdescent : baseEnd_2640124 < baseStart_2640124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640128 : List Nat := [2, 1, 1, 2, 1, 1, 7, 3, 1, 3]
def baseStart_2640128 : Nat := 118140960795 + 2640128 * 2 ^ 59
def prefixEnd_2640128 : Nat := 4983230072969 + 3 ^ 40 * 2640128 * 2
def baseEnd_2640128 : Nat := 903769768929034480505519

theorem tailTrace_2640128 : CollatzResearch.WordTrace tailWord_2640128 prefixEnd_2640128 903769768929034480505519 := by
  unfold tailWord_2640128
  simp only [CollatzResearch.WordTrace]
  refine ⟨48146689489637314404844519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64195585986183085873126025 48146689489637314404844519)
  ·
    refine ⟨72220034234455971607266779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48146689489637314404844519 72220034234455971607266779)
    ·
      refine ⟨108330051351683957410900169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72220034234455971607266779 108330051351683957410900169)
      ·
        refine ⟨81247538513762968058175127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108330051351683957410900169 81247538513762968058175127)
        ·
          refine ⟨121871307770644452087262691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81247538513762968058175127 121871307770644452087262691)
          ·
            refine ⟨182806961655966678130894037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121871307770644452087262691 182806961655966678130894037)
            ·
              refine ⟨4284538163811719018692829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 182806961655966678130894037 4284538163811719018692829)
              ·
                refine ⟨1606701811429394632009811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4284538163811719018692829 1606701811429394632009811)
                ·
                  refine ⟨2410052717144091948014717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606701811429394632009811 2410052717144091948014717)
                  ·
                    refine ⟨903769768929034480505519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2410052717144091948014717 903769768929034480505519)
                    ·
                      rfl

theorem cell22_2640128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 1, 3].length) (baseStart_2640128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640128 prefixEnd_2640128 := by exact prefixLift 2640128
  have htrace : WordTrace (prefixWord ++ tailWord_2640128) baseStart_2640128 baseEnd_2640128 := by
    simpa [prefixWord, tailWord_2640128, baseEnd_2640128] using wordTrace_append hprefix tailTrace_2640128
  have hstable : (prefixWord ++ tailWord_2640128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640128).length < 2 ^ (prefixWord ++ tailWord_2640128).sum := by decide
  have hdescent : baseEnd_2640128 < baseStart_2640128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640145 : List Nat := [1, 2, 2, 1, 1, 6, 3, 2, 1, 3]
def baseStart_2640145 : Nat := 118140960795 + 2640145 * 2 ^ 59
def prefixEnd_2640145 : Nat := 4983230072969 + 3 ^ 40 * 2640145 * 2
def baseEnd_2640145 : Nat := 903775588376452102830467

theorem tailTrace_2640145 : CollatzResearch.WordTrace tailWord_2640145 prefixEnd_2640145 903775588376452102830467 := by
  unfold tailWord_2640145
  simp only [CollatzResearch.WordTrace]
  refine ⟨96293999020213040713057889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64195999346808693808705259 96293999020213040713057889)
  ·
    refine ⟨72220499265159780534793417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96293999020213040713057889 72220499265159780534793417)
    ·
      refine ⟨54165374448869835401095063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72220499265159780534793417 54165374448869835401095063)
      ·
        refine ⟨81248061673304753101642595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54165374448869835401095063 81248061673304753101642595)
        ·
          refine ⟨121872092509957129652463893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81248061673304753101642595 121872092509957129652463893)
          ·
            refine ⟨5712754336404240452459245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 121872092509957129652463893 5712754336404240452459245)
            ·
              refine ⟨2142282876151590169672217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5712754336404240452459245 2142282876151590169672217)
              ·
                refine ⟨1606712157113692627254163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2142282876151590169672217 1606712157113692627254163)
                ·
                  refine ⟨2410068235670538940881245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606712157113692627254163 2410068235670538940881245)
                  ·
                    refine ⟨903775588376452102830467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2410068235670538940881245 903775588376452102830467)
                    ·
                      rfl

theorem cell22_2640145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_2640145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640145 prefixEnd_2640145 := by exact prefixLift 2640145
  have htrace : WordTrace (prefixWord ++ tailWord_2640145) baseStart_2640145 baseEnd_2640145 := by
    simpa [prefixWord, tailWord_2640145, baseEnd_2640145] using wordTrace_append hprefix tailTrace_2640145
  have hstable : (prefixWord ++ tailWord_2640145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640145).length < 2 ^ (prefixWord ++ tailWord_2640145).sum := by decide
  have hdescent : baseEnd_2640145 < baseStart_2640145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640184 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 3, 5]
def baseStart_2640184 : Nat := 118140960795 + 2640184 * 2 ^ 59
def prefixEnd_2640184 : Nat := 4983230072969 + 3 ^ 40 * 2640184 * 2
def baseEnd_2640184 : Nat := 903788938873469001105347

theorem tailTrace_2640184 : CollatzResearch.WordTrace tailWord_2640184 prefixEnd_2640184 903788938873469001105347 := by
  unfold tailWord_2640184
  simp only [CollatzResearch.WordTrace]
  refine ⟨48147710733535875186863803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64196947644714500249151737 48147710733535875186863803)
  ·
    refine ⟨72221566100303812780295705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48147710733535875186863803 72221566100303812780295705)
    ·
      refine ⟨54166174575227859585221779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72221566100303812780295705 54166174575227859585221779)
      ·
        refine ⟨81249261862841789377832669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54166174575227859585221779 81249261862841789377832669)
        ·
          refine ⟨30468473198565671016687251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81249261862841789377832669 30468473198565671016687251)
          ·
            refine ⟨45702709797848506525030877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30468473198565671016687251 45702709797848506525030877)
            ·
              refine ⟨17138516174193189946886579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45702709797848506525030877 17138516174193189946886579)
              ·
                refine ⟨25707774261289784920329869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17138516174193189946886579 25707774261289784920329869)
                ·
                  refine ⟨9640415347983669345123701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25707774261289784920329869 9640415347983669345123701)
                  ·
                    refine ⟨903788938873469001105347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9640415347983669345123701 903788938873469001105347)
                    ·
                      rfl

theorem cell22_2640184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_2640184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640184 prefixEnd_2640184 := by exact prefixLift 2640184
  have htrace : WordTrace (prefixWord ++ tailWord_2640184) baseStart_2640184 baseEnd_2640184 := by
    simpa [prefixWord, tailWord_2640184, baseEnd_2640184] using wordTrace_append hprefix tailTrace_2640184
  have hstable : (prefixWord ++ tailWord_2640184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640184).length < 2 ^ (prefixWord ++ tailWord_2640184).sum := by decide
  have hdescent : baseEnd_2640184 < baseStart_2640184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640188 : List Nat := [2, 2, 2, 2, 1, 2, 5, 1, 1, 4]
def baseStart_2640188 : Nat := 118140960795 + 2640188 * 2 ^ 59
def prefixEnd_2640188 : Nat := 4983230072969 + 3 ^ 40 * 2640188 * 2
def baseEnd_2640188 : Nat := 903790308155214324005335

theorem tailTrace_2640188 : CollatzResearch.WordTrace tailWord_2640188 prefixEnd_2640188 903790308155214324005335 := by
  unfold tailWord_2640188
  simp only [CollatzResearch.WordTrace]
  refine ⟨48147783679528629528436609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64197044906038172704582145 48147783679528629528436609)
  ·
    refine ⟨36110837759646472146327457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48147783679528629528436609 36110837759646472146327457)
    ·
      refine ⟨27083128319734854109745593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36110837759646472146327457 27083128319734854109745593)
      ·
        refine ⟨20312346239801140582309195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27083128319734854109745593 20312346239801140582309195)
        ·
          refine ⟨30468519359701710873463793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20312346239801140582309195 30468519359701710873463793)
          ·
            refine ⟨22851389519776283155097845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30468519359701710873463793 22851389519776283155097845)
            ·
              refine ⟨2142317767479026545790423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22851389519776283155097845 2142317767479026545790423)
              ·
                refine ⟨3213476651218539818685635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2142317767479026545790423 3213476651218539818685635)
                ·
                  refine ⟨4820214976827809728028453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213476651218539818685635 4820214976827809728028453)
                  ·
                    refine ⟨903790308155214324005335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4820214976827809728028453 903790308155214324005335)
                    ·
                      rfl

theorem cell22_2640188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_2640188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640188 prefixEnd_2640188 := by exact prefixLift 2640188
  have htrace : WordTrace (prefixWord ++ tailWord_2640188) baseStart_2640188 baseEnd_2640188 := by
    simpa [prefixWord, tailWord_2640188, baseEnd_2640188] using wordTrace_append hprefix tailTrace_2640188
  have hstable : (prefixWord ++ tailWord_2640188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640188).length < 2 ^ (prefixWord ++ tailWord_2640188).sum := by decide
  have hdescent : baseEnd_2640188 < baseStart_2640188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640196 : List Nat := [2, 3, 4, 1, 3, 1, 2, 2, 1, 3]
def baseStart_2640196 : Nat := 118140960795 + 2640196 * 2 ^ 59
def prefixEnd_2640196 : Nat := 4983230072969 + 3 ^ 40 * 2640196 * 2
def baseEnd_2640196 : Nat := 903793046718704969805311

theorem tailTrace_2640196 : CollatzResearch.WordTrace tailWord_2640196 prefixEnd_2640196 903793046718704969805311 := by
  unfold tailWord_2640196
  simp only [CollatzResearch.WordTrace]
  refine ⟨48147929571514138211582221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64197239428685517615442961 48147929571514138211582221)
  ·
    refine ⟨18055473589317801829343333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48147929571514138211582221 18055473589317801829343333)
    ·
      refine ⟨3385401297997087843001875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18055473589317801829343333 3385401297997087843001875)
      ·
        refine ⟨5078101946995631764502813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3385401297997087843001875 5078101946995631764502813)
        ·
          refine ⟨1904288230123361911688555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5078101946995631764502813 1904288230123361911688555)
          ·
            refine ⟨2856432345185042867532833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904288230123361911688555 2856432345185042867532833)
            ·
              refine ⟨2142324258888782150649625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2856432345185042867532833 2142324258888782150649625)
              ·
                refine ⟨1606743194166586612987219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2142324258888782150649625 1606743194166586612987219)
                ·
                  refine ⟨2410114791249879919480829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606743194166586612987219 2410114791249879919480829)
                  ·
                    refine ⟨903793046718704969805311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2410114791249879919480829 903793046718704969805311)
                    ·
                      rfl

theorem cell22_2640196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_2640196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640196 prefixEnd_2640196 := by exact prefixLift 2640196
  have htrace : WordTrace (prefixWord ++ tailWord_2640196) baseStart_2640196 baseEnd_2640196 := by
    simpa [prefixWord, tailWord_2640196, baseEnd_2640196] using wordTrace_append hprefix tailTrace_2640196
  have hstable : (prefixWord ++ tailWord_2640196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640196).length < 2 ^ (prefixWord ++ tailWord_2640196).sum := by decide
  have hdescent : baseEnd_2640196 < baseStart_2640196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640263 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 3, 3]
def baseStart_2640263 : Nat := 118140960795 + 2640263 * 2 ^ 59
def prefixEnd_2640263 : Nat := 4983230072969 + 3 ^ 40 * 2640263 * 2
def baseEnd_2640263 : Nat := 903815982187939128380105

theorem tailTrace_2640263 : CollatzResearch.WordTrace tailWord_2640263 prefixEnd_2640263 903815982187939128380105 := by
  unfold tailWord_2640263
  simp only [CollatzResearch.WordTrace]
  refine ⟨96298302833785546865853443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64198868555857031243902295 96298302833785546865853443)
  ·
    refine ⟨144447454250678320298780165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96298302833785546865853443 144447454250678320298780165)
    ·
      refine ⟨27083897672002185056021281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144447454250678320298780165 27083897672002185056021281)
      ·
        refine ⟨20312923254001638792015961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27083897672002185056021281 20312923254001638792015961)
        ·
          refine ⟨15234692440501229094011971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20312923254001638792015961 15234692440501229094011971)
          ·
            refine ⟨22852038660751843641017957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15234692440501229094011971 22852038660751843641017957)
            ·
              refine ⟨4284757248890970682690867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22852038660751843641017957 4284757248890970682690867)
              ·
                refine ⟨6427135873336456024036301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4284757248890970682690867 6427135873336456024036301)
                ·
                  refine ⟨2410175952501171009013613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6427135873336456024036301 2410175952501171009013613)
                  ·
                    refine ⟨903815982187939128380105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2410175952501171009013613 903815982187939128380105)
                    ·
                      rfl

theorem cell22_2640263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_2640263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640263 prefixEnd_2640263 := by exact prefixLift 2640263
  have htrace : WordTrace (prefixWord ++ tailWord_2640263) baseStart_2640263 baseEnd_2640263 := by
    simpa [prefixWord, tailWord_2640263, baseEnd_2640263] using wordTrace_append hprefix tailTrace_2640263
  have hstable : (prefixWord ++ tailWord_2640263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640263).length < 2 ^ (prefixWord ++ tailWord_2640263).sum := by decide
  have hdescent : baseEnd_2640263 < baseStart_2640263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640340 : List Nat := [2, 4, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_2640340 : Nat := 118140960795 + 2640340 * 2 ^ 59
def prefixEnd_2640340 : Nat := 4983230072969 + 3 ^ 40 * 2640340 * 2
def baseEnd_2640340 : Nat := 903842340861536594204869

theorem tailTrace_2640340 : CollatzResearch.WordTrace tailWord_2640340 prefixEnd_2640340 903842340861536594204869 := by
  unfold tailWord_2640340
  simp only [CollatzResearch.WordTrace]
  refine ⟨48150555627253294508203237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64200740836337726010937649 48150555627253294508203237)
  ·
    refine ⟨9028229180109992720288107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48150555627253294508203237 9028229180109992720288107)
    ·
      refine ⟨13542343770164989080432161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9028229180109992720288107 13542343770164989080432161)
      ·
        refine ⟨10156757827623741810324121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13542343770164989080432161 10156757827623741810324121)
        ·
          refine ⟨7617568370717806357743091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10156757827623741810324121 7617568370717806357743091)
          ·
            refine ⟨11426352556076709536614637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7617568370717806357743091 11426352556076709536614637)
            ·
              refine ⟨4284882208528766076230489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11426352556076709536614637 4284882208528766076230489)
              ·
                refine ⟨3213661656396574557172867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4284882208528766076230489 3213661656396574557172867)
                ·
                  refine ⟨4820492484594861835759301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213661656396574557172867 4820492484594861835759301)
                  ·
                    refine ⟨903842340861536594204869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4820492484594861835759301 903842340861536594204869)
                    ·
                      rfl

theorem cell22_2640340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_2640340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640340 prefixEnd_2640340 := by exact prefixLift 2640340
  have htrace : WordTrace (prefixWord ++ tailWord_2640340) baseStart_2640340 baseEnd_2640340 := by
    simpa [prefixWord, tailWord_2640340, baseEnd_2640340] using wordTrace_append hprefix tailTrace_2640340
  have hstable : (prefixWord ++ tailWord_2640340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640340).length < 2 ^ (prefixWord ++ tailWord_2640340).sum := by decide
  have hdescent : baseEnd_2640340 < baseStart_2640340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640357 : List Nat := [1, 3, 1, 5, 2, 1, 3, 1, 1, 4]
def baseStart_2640357 : Nat := 118140960795 + 2640357 * 2 ^ 59
def prefixEnd_2640357 : Nat := 4983230072969 + 3 ^ 40 * 2640357 * 2
def baseEnd_2640357 : Nat := 903848160308954216529817

theorem tailTrace_2640357 : CollatzResearch.WordTrace tailWord_2640357 prefixEnd_2640357 903848160308954216529817 := by
  unfold tailWord_2640357
  simp only [CollatzResearch.WordTrace]
  refine ⟨96301731295445000919775325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64201154196963333946516883 96301731295445000919775325)
  ·
    refine ⟨36113149235791875344915747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96301731295445000919775325 36113149235791875344915747)
    ·
      refine ⟨54169723853687813017373621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36113149235791875344915747 54169723853687813017373621)
      ·
        refine ⟨5078411611283232470378777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54169723853687813017373621 5078411611283232470378777)
        ·
          refine ⟨3808808708462424352784083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5078411611283232470378777 3808808708462424352784083)
          ·
            refine ⟨5713213062693636529176125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3808808708462424352784083 5713213062693636529176125)
            ·
              refine ⟨2142454898510113698441047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5713213062693636529176125 2142454898510113698441047)
              ·
                refine ⟨3213682347765170547661571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2142454898510113698441047 3213682347765170547661571)
                ·
                  refine ⟨4820523521647755821492357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213682347765170547661571 4820523521647755821492357)
                  ·
                    refine ⟨903848160308954216529817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4820523521647755821492357 903848160308954216529817)
                    ·
                      rfl

theorem cell22_2640357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_2640357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640357 prefixEnd_2640357 := by exact prefixLift 2640357
  have htrace : WordTrace (prefixWord ++ tailWord_2640357) baseStart_2640357 baseEnd_2640357 := by
    simpa [prefixWord, tailWord_2640357, baseEnd_2640357] using wordTrace_append hprefix tailTrace_2640357
  have hstable : (prefixWord ++ tailWord_2640357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640357).length < 2 ^ (prefixWord ++ tailWord_2640357).sum := by decide
  have hdescent : baseEnd_2640357 < baseStart_2640357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640366 : List Nat := [4, 1, 2, 1, 2, 12]
def baseStart_2640366 : Nat := 118140960795 + 2640366 * 2 ^ 59
def prefixEnd_2640366 : Nat := 4983230072969 + 3 ^ 40 * 2640366 * 2
def baseEnd_2640366 : Nat := 11158657298677545593269

theorem tailTrace_2640366 : CollatzResearch.WordTrace tailWord_2640366 prefixEnd_2640366 11158657298677545593269 := by
  unfold tailWord_2640366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12037757444051549432106619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64201373034941596971235301 12037757444051549432106619)
  ·
    refine ⟨18056636166077324148159929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12037757444051549432106619 18056636166077324148159929)
    ·
      refine ⟨13542477124557993111119947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18056636166077324148159929 13542477124557993111119947)
      ·
        refine ⟨20313715686836989666679921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13542477124557993111119947 20313715686836989666679921)
        ·
          refine ⟨15235286765127742250009941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20313715686836989666679921 15235286765127742250009941)
          ·
            refine ⟨11158657298677545593269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15235286765127742250009941 11158657298677545593269)
            ·
              rfl

theorem cell22_2640366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 12].length) (baseStart_2640366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640366 prefixEnd_2640366 := by exact prefixLift 2640366
  have htrace : WordTrace (prefixWord ++ tailWord_2640366) baseStart_2640366 baseEnd_2640366 := by
    simpa [prefixWord, tailWord_2640366, baseEnd_2640366] using wordTrace_append hprefix tailTrace_2640366
  have hstable : (prefixWord ++ tailWord_2640366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640366).length < 2 ^ (prefixWord ++ tailWord_2640366).sum := by decide
  have hdescent : baseEnd_2640366 < baseStart_2640366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
