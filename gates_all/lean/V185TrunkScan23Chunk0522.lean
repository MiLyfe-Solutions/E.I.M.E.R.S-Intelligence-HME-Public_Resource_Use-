import V185TrunkScan23Chunk0521

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3086467 : List Nat := [1, 1, 1, 3, 3, 4, 3, 1, 1, 3, 2]
def baseStart_3086467 : Nat := 118140960795 + 3086467 * 2 ^ 59
def prefixEnd_3086467 : Nat := 4983230072969 + 3 ^ 40 * 3086467 * 2
def baseEnd_3086467 : Nat := 1584841095240680917368103

theorem tailTrace_3086467 : CollatzResearch.WordTrace tailWord_3086467 prefixEnd_3086467 1584841095240680917368103 := by
  unfold tailWord_3086467
  simp only [CollatzResearch.WordTrace]
  refine ⟨112572699709264660442017655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75048466472843106961345103 112572699709264660442017655)
  ·
    refine ⟨168859049563896990663026483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112572699709264660442017655 168859049563896990663026483)
    ·
      refine ⟨253288574345845485994539725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168859049563896990663026483 253288574345845485994539725)
      ·
        refine ⟨94983215379692057247952397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253288574345845485994539725 94983215379692057247952397)
        ·
          refine ⟨35618705767384521467982149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94983215379692057247952397 35618705767384521467982149)
          ·
            refine ⟨6678507331384597775246653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35618705767384521467982149 6678507331384597775246653)
            ·
              refine ⟨2504440249269224165717495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6678507331384597775246653 2504440249269224165717495)
              ·
                refine ⟨3756660373903836248576243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504440249269224165717495 3756660373903836248576243)
                ·
                  refine ⟨5634990560855754372864365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3756660373903836248576243 5634990560855754372864365)
                  ·
                    refine ⟨2113121460320907889824137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5634990560855754372864365 2113121460320907889824137)
                    ·
                      refine ⟨1584841095240680917368103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2113121460320907889824137 1584841095240680917368103)
                      ·
                        rfl

theorem cell23_3086467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 1, 3, 2].length) (baseStart_3086467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086467 prefixEnd_3086467 := by exact prefixLift 3086467
  have htrace : WordTrace (prefixWord ++ tailWord_3086467) baseStart_3086467 baseEnd_3086467 := by
    simpa [prefixWord, tailWord_3086467, baseEnd_3086467] using wordTrace_append hprefix tailTrace_3086467
  have hstable : (prefixWord ++ tailWord_3086467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086467).length < 2 ^ (prefixWord ++ tailWord_3086467).sum := by decide
  have hdescent : baseEnd_3086467 < baseStart_3086467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086493 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_3086493 : Nat := 118140960795 + 3086493 * 2 ^ 59
def prefixEnd_3086493 : Nat := 4983230072969 + 3 ^ 40 * 3086493 * 2
def baseEnd_3086493 : Nat := 1584854445737697815642983

theorem tailTrace_3086493 : CollatzResearch.WordTrace tailWord_3086493 prefixEnd_3086493 1584854445737697815642983 := by
  unfold tailWord_3086493
  simp only [CollatzResearch.WordTrace]
  refine ⟨112573648007170466882464133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75049098671446977921642755 112573648007170466882464133)
  ·
    refine ⟨21107559001344462540462025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112573648007170466882464133 21107559001344462540462025)
    ·
      refine ⟨15830669251008346905346519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21107559001344462540462025 15830669251008346905346519)
      ·
        refine ⟨23746003876512520358019779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15830669251008346905346519 23746003876512520358019779)
        ·
          refine ⟨35619005814768780537029669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23746003876512520358019779 35619005814768780537029669)
          ·
            refine ⟨6678563590269146350693063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35619005814768780537029669 6678563590269146350693063)
            ·
              refine ⟨10017845385403719526039595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6678563590269146350693063 10017845385403719526039595)
              ·
                refine ⟨15026768078105579289059393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10017845385403719526039595 15026768078105579289059393)
                ·
                  refine ⟨11270076058579184466794545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15026768078105579289059393 11270076058579184466794545)
                  ·
                    refine ⟨8452557043934388350095909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11270076058579184466794545 8452557043934388350095909)
                    ·
                      refine ⟨1584854445737697815642983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8452557043934388350095909 1584854445737697815642983)
                      ·
                        rfl

theorem cell23_3086493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_3086493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086493 prefixEnd_3086493 := by exact prefixLift 3086493
  have htrace : WordTrace (prefixWord ++ tailWord_3086493) baseStart_3086493 baseEnd_3086493 := by
    simpa [prefixWord, tailWord_3086493, baseEnd_3086493] using wordTrace_append hprefix tailTrace_3086493
  have hstable : (prefixWord ++ tailWord_3086493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086493).length < 2 ^ (prefixWord ++ tailWord_3086493).sum := by decide
  have hdescent : baseEnd_3086493 < baseStart_3086493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086497 : List Nat := [1, 2, 3, 3, 1, 2, 2, 3, 2, 2, 2]
def baseStart_3086497 : Nat := 118140960795 + 3086497 * 2 ^ 59
def prefixEnd_3086497 : Nat := 4983230072969 + 3 ^ 40 * 3086497 * 2
def baseEnd_3086497 : Nat := 1584856499660315799992965

theorem tailTrace_3086497 : CollatzResearch.WordTrace tailWord_3086497 prefixEnd_3086497 1584856499660315799992965 := by
  unfold tailWord_3086497
  simp only [CollatzResearch.WordTrace]
  refine ⟨112573793899155975565609745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75049195932770650377073163 112573793899155975565609745)
  ·
    refine ⟨84430345424366981674207309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112573793899155975565609745 84430345424366981674207309)
    ·
      refine ⟨31661379534137618127827741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84430345424366981674207309 31661379534137618127827741)
      ·
        refine ⟨11873017325301606797935403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31661379534137618127827741 11873017325301606797935403)
        ·
          refine ⟨17809525987952410196903105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11873017325301606797935403 17809525987952410196903105)
          ·
            refine ⟨13357144490964307647677329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17809525987952410196903105 13357144490964307647677329)
            ·
              refine ⟨10017858368223230735757997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13357144490964307647677329 10017858368223230735757997)
              ·
                refine ⟨3756696888083711525909249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10017858368223230735757997 3756696888083711525909249)
                ·
                  refine ⟨2817522666062783644431937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3756696888083711525909249 2817522666062783644431937)
                  ·
                    refine ⟨2113141999547087733323953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2817522666062783644431937 2113141999547087733323953)
                    ·
                      refine ⟨1584856499660315799992965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2113141999547087733323953 1584856499660315799992965)
                      ·
                        rfl

theorem cell23_3086497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_3086497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086497 prefixEnd_3086497 := by exact prefixLift 3086497
  have htrace : WordTrace (prefixWord ++ tailWord_3086497) baseStart_3086497 baseEnd_3086497 := by
    simpa [prefixWord, tailWord_3086497, baseEnd_3086497] using wordTrace_append hprefix tailTrace_3086497
  have hstable : (prefixWord ++ tailWord_3086497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086497).length < 2 ^ (prefixWord ++ tailWord_3086497).sum := by decide
  have hdescent : baseEnd_3086497 < baseStart_3086497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086550 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_3086550 : Nat := 118140960795 + 3086550 * 2 ^ 59
def prefixEnd_3086550 : Nat := 4983230072969 + 3 ^ 40 * 3086550 * 2
def baseEnd_3086550 : Nat := 528294571378334697543407

theorem tailTrace_3086550 : CollatzResearch.WordTrace tailWord_3086550 prefixEnd_3086550 528294571378334697543407 := by
  unfold tailWord_3086550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7035982935497747851080569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75050484645309310411526069 7035982935497747851080569)
  ·
    refine ⟨5276987201623310888310427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7035982935497747851080569 5276987201623310888310427)
    ·
      refine ⟨7915480802434966332465641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5276987201623310888310427 7915480802434966332465641)
      ·
        refine ⟨5936610601826224749349231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7915480802434966332465641 5936610601826224749349231)
        ·
          refine ⟨8904915902739337124023847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5936610601826224749349231 8904915902739337124023847)
          ·
            refine ⟨13357373854109005686035771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8904915902739337124023847 13357373854109005686035771)
            ·
              refine ⟨20036060781163508529053657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13357373854109005686035771 20036060781163508529053657)
              ·
                refine ⟨15027045585872631396790243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20036060781163508529053657 15027045585872631396790243)
                ·
                  refine ⟨22540568378808947095185365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15027045585872631396790243 22540568378808947095185365)
                  ·
                    refine ⟨528294571378334697543407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22540568378808947095185365 528294571378334697543407)
                    ·
                      rfl

theorem cell23_3086550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_3086550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086550 prefixEnd_3086550 := by exact prefixLift 3086550
  have htrace : WordTrace (prefixWord ++ tailWord_3086550) baseStart_3086550 baseEnd_3086550 := by
    simpa [prefixWord, tailWord_3086550, baseEnd_3086550] using wordTrace_append hprefix tailTrace_3086550
  have hstable : (prefixWord ++ tailWord_3086550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086550).length < 2 ^ (prefixWord ++ tailWord_3086550).sum := by decide
  have hdescent : baseEnd_3086550 < baseStart_3086550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086593 : List Nat := [1, 2, 4, 1, 1, 2, 2, 4, 6]
def baseStart_3086593 : Nat := 118140960795 + 3086593 * 2 ^ 59
def prefixEnd_3086593 : Nat := 4983230072969 + 3 ^ 40 * 3086593 * 2
def baseEnd_3086593 : Nat := 176100643755905269376947

theorem tailTrace_3086593 : CollatzResearch.WordTrace tailWord_3086593 prefixEnd_3086593 176100643755905269376947 := by
  unfold tailWord_3086593
  simp only [CollatzResearch.WordTrace]
  refine ⟨112577295306808183961104433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75051530204538789307402955 112577295306808183961104433)
  ·
    refine ⟨84432971480106137970828325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112577295306808183961104433 84432971480106137970828325)
    ·
      refine ⟨15831182152519900869530311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84432971480106137970828325 15831182152519900869530311)
      ·
        refine ⟨23746773228779851304295467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15831182152519900869530311 23746773228779851304295467)
        ·
          refine ⟨35620159843169776956443201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23746773228779851304295467 35620159843169776956443201)
          ·
            refine ⟨26715119882377332717332401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35620159843169776956443201 26715119882377332717332401)
            ·
              refine ⟨20036339911782999537999301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26715119882377332717332401 20036339911782999537999301)
              ·
                refine ⟨3756813733459312413374869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20036339911782999537999301 3756813733459312413374869)
                ·
                  refine ⟨176100643755905269376947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3756813733459312413374869 176100643755905269376947)
                  ·
                    rfl

theorem cell23_3086593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 6].length) (baseStart_3086593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086593 prefixEnd_3086593 := by exact prefixLift 3086593
  have htrace : WordTrace (prefixWord ++ tailWord_3086593) baseStart_3086593 baseEnd_3086593 := by
    simpa [prefixWord, tailWord_3086593, baseEnd_3086593] using wordTrace_append hprefix tailTrace_3086593
  have hstable : (prefixWord ++ tailWord_3086593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086593).length < 2 ^ (prefixWord ++ tailWord_3086593).sum := by decide
  have hdescent : baseEnd_3086593 < baseStart_3086593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086620 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_3086620 : Nat := 118140960795 + 3086620 * 2 ^ 59
def prefixEnd_3086620 : Nat := 4983230072969 + 3 ^ 40 * 3086620 * 2
def baseEnd_3086620 : Nat := 1584919657780818818754899

theorem tailTrace_3086620 : CollatzResearch.WordTrace tailWord_3086620 prefixEnd_3086620 1584919657780818818754899 := by
  unfold tailWord_3086620
  simp only [CollatzResearch.WordTrace]
  refine ⟨56289140038855183786168657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75052186718473578381558209 56289140038855183786168657)
  ·
    refine ⟨42216855029141387839626493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56289140038855183786168657 42216855029141387839626493)
    ·
      refine ⟨15831320635928020439859935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42216855029141387839626493 15831320635928020439859935)
      ·
        refine ⟨23746980953892030659789903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15831320635928020439859935 23746980953892030659789903)
        ·
          refine ⟨35620471430838045989684855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23746980953892030659789903 35620471430838045989684855)
          ·
            refine ⟨53430707146257068984527283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35620471430838045989684855 53430707146257068984527283)
            ·
              refine ⟨80146060719385603476790925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53430707146257068984527283 80146060719385603476790925)
              ·
                refine ⟨30054772769769601303796597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80146060719385603476790925 30054772769769601303796597)
                ·
                  refine ⟨2817634947165900122230931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30054772769769601303796597 2817634947165900122230931)
                  ·
                    refine ⟨4226452420748850183346397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2817634947165900122230931 4226452420748850183346397)
                    ·
                      refine ⟨1584919657780818818754899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4226452420748850183346397 1584919657780818818754899)
                      ·
                        rfl

theorem cell23_3086620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_3086620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086620 prefixEnd_3086620 := by exact prefixLift 3086620
  have htrace : WordTrace (prefixWord ++ tailWord_3086620) baseStart_3086620 baseEnd_3086620 := by
    simpa [prefixWord, tailWord_3086620, baseEnd_3086620] using wordTrace_append hprefix tailTrace_3086620
  have hstable : (prefixWord ++ tailWord_3086620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086620).length < 2 ^ (prefixWord ++ tailWord_3086620).sum := by decide
  have hdescent : baseEnd_3086620 < baseStart_3086620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086663 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_3086663 : Nat := 118140960795 + 3086663 * 2 ^ 59
def prefixEnd_3086663 : Nat := 4983230072969 + 3 ^ 40 * 3086663 * 2
def baseEnd_3086663 : Nat := 1584941737448962150517201

theorem tailTrace_3086663 : CollatzResearch.WordTrace tailWord_3086663 prefixEnd_3086663 1584941737448962150517201 := by
  unfold tailWord_3086663
  simp only [CollatzResearch.WordTrace]
  refine ⟨112579848416554585916152643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75053232277703057277435095 112579848416554585916152643)
  ·
    refine ⟨168869772624831878874228965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112579848416554585916152643 168869772624831878874228965)
    ·
      refine ⟨31663082367155977288917931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168869772624831878874228965 31663082367155977288917931)
      ·
        refine ⟨47494623550733965933376897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31663082367155977288917931 47494623550733965933376897)
        ·
          refine ⟨35620967663050474450032673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47494623550733965933376897 35620967663050474450032673)
          ·
            refine ⟨26715725747287855837524505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35620967663050474450032673 26715725747287855837524505)
            ·
              refine ⟨20036794310465891878143379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26715725747287855837524505 20036794310465891878143379)
              ·
                refine ⟨30055191465698837817215069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20036794310465891878143379 30055191465698837817215069)
                ·
                  refine ⟨11270696799637064181455651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30055191465698837817215069 11270696799637064181455651)
                  ·
                    refine ⟨16906045199455596272183477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11270696799637064181455651 16906045199455596272183477)
                    ·
                      refine ⟨1584941737448962150517201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16906045199455596272183477 1584941737448962150517201)
                      ·
                        rfl

theorem cell23_3086663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_3086663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086663 prefixEnd_3086663 := by exact prefixLift 3086663
  have htrace : WordTrace (prefixWord ++ tailWord_3086663) baseStart_3086663 baseEnd_3086663 := by
    simpa [prefixWord, tailWord_3086663, baseEnd_3086663] using wordTrace_append hprefix tailTrace_3086663
  have hstable : (prefixWord ++ tailWord_3086663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086663).length < 2 ^ (prefixWord ++ tailWord_3086663).sum := by decide
  have hdescent : baseEnd_3086663 < baseStart_3086663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086743 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 1, 8]
def baseStart_3086743 : Nat := 118140960795 + 3086743 * 2 ^ 59
def prefixEnd_3086743 : Nat := 4983230072969 + 3 ^ 40 * 3086743 * 2
def baseEnd_3086743 : Nat := 528327605300440612505611

theorem tailTrace_3086743 : CollatzResearch.WordTrace tailWord_3086743 prefixEnd_3086743 528327605300440612505611 := by
  unfold tailWord_3086743
  simp only [CollatzResearch.WordTrace]
  refine ⟨112582766256264759579064883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75055177504176506386043255 112582766256264759579064883)
  ·
    refine ⟨168874149384397139368597325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112582766256264759579064883 168874149384397139368597325)
    ·
      refine ⟨63327806019148927263223997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168874149384397139368597325 63327806019148927263223997)
      ·
        refine ⟨23747927257180847723708999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63327806019148927263223997 23747927257180847723708999)
        ·
          refine ⟨35621890885771271585563499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23747927257180847723708999 35621890885771271585563499)
          ·
            refine ⟨53432836328656907378345249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35621890885771271585563499 53432836328656907378345249)
            ·
              refine ⟨40074627246492680533758937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53432836328656907378345249 40074627246492680533758937)
              ·
                refine ⟨30055970434869510400319203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40074627246492680533758937 30055970434869510400319203)
                ·
                  refine ⟨45083955652304265600478805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30055970434869510400319203 45083955652304265600478805)
                  ·
                    refine ⟨528327605300440612505611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45083955652304265600478805 528327605300440612505611)
                    ·
                      rfl

theorem cell23_3086743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_3086743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086743 prefixEnd_3086743 := by exact prefixLift 3086743
  have htrace : WordTrace (prefixWord ++ tailWord_3086743) baseStart_3086743 baseEnd_3086743 := by
    simpa [prefixWord, tailWord_3086743, baseEnd_3086743] using wordTrace_append hprefix tailTrace_3086743
  have hstable : (prefixWord ++ tailWord_3086743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086743).length < 2 ^ (prefixWord ++ tailWord_3086743).sum := by decide
  have hdescent : baseEnd_3086743 < baseStart_3086743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086754 : List Nat := [3, 3, 1, 2, 1, 1, 1, 5, 1, 3, 2]
def baseStart_3086754 : Nat := 118140960795 + 3086754 * 2 ^ 59
def prefixEnd_3086754 : Nat := 4983230072969 + 3 ^ 40 * 3086754 * 2
def baseEnd_3086754 : Nat := 1584988464188521294479283

theorem tailTrace_3086754 : CollatzResearch.WordTrace tailWord_3086754 prefixEnd_3086754 1584988464188521294479283 := by
  unfold tailWord_3086754
  simp only [CollatzResearch.WordTrace]
  refine ⟨28145791864806227114428829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75055444972816605638476877 28145791864806227114428829)
  ·
    refine ⟨10554671949302335167910811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28145791864806227114428829 10554671949302335167910811)
    ·
      refine ⟨15832007923953502751866217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10554671949302335167910811 15832007923953502751866217)
      ·
        refine ⟨11874005942965127063899663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15832007923953502751866217 11874005942965127063899663)
        ·
          refine ⟨17811008914447690595849495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11874005942965127063899663 17811008914447690595849495)
          ·
            refine ⟨26716513371671535893774243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17811008914447690595849495 26716513371671535893774243)
            ·
              refine ⟨40074770057507303840661365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26716513371671535893774243 40074770057507303840661365)
              ·
                refine ⟨3757009692891309735062003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40074770057507303840661365 3757009692891309735062003)
                ·
                  refine ⟨5635514539336964602593005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757009692891309735062003 5635514539336964602593005)
                  ·
                    refine ⟨2113317952251361725972377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5635514539336964602593005 2113317952251361725972377)
                    ·
                      refine ⟨1584988464188521294479283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2113317952251361725972377 1584988464188521294479283)
                      ·
                        rfl

theorem cell23_3086754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_3086754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086754 prefixEnd_3086754 := by exact prefixLift 3086754
  have htrace : WordTrace (prefixWord ++ tailWord_3086754) baseStart_3086754 baseEnd_3086754 := by
    simpa [prefixWord, tailWord_3086754, baseEnd_3086754] using wordTrace_append hprefix tailTrace_3086754
  have hstable : (prefixWord ++ tailWord_3086754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086754).length < 2 ^ (prefixWord ++ tailWord_3086754).sum := by decide
  have hdescent : baseEnd_3086754 < baseStart_3086754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086762 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_3086762 : Nat := 118140960795 + 3086762 * 2 ^ 59
def prefixEnd_3086762 : Nat := 4983230072969 + 3 ^ 40 * 3086762 * 2
def baseEnd_3086762 : Nat := 1584992572033757263179247

theorem tailTrace_3086762 : CollatzResearch.WordTrace tailWord_3086762 prefixEnd_3086762 1584992572033757263179247 := by
  unfold tailWord_3086762
  simp only [CollatzResearch.WordTrace]
  refine ⟨28145864810798981456001635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75055639495463950549337693 28145864810798981456001635)
  ·
    refine ⟨42218797216198472184002453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28145864810798981456001635 42218797216198472184002453)
    ·
      refine ⟨1979006119509303383625115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42218797216198472184002453 1979006119509303383625115)
      ·
        refine ⟨2968509179263955075437673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1979006119509303383625115 2968509179263955075437673)
        ·
          refine ⟨2226381884447966306578255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2968509179263955075437673 2226381884447966306578255)
          ·
            refine ⟨3339572826671949459867383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226381884447966306578255 3339572826671949459867383)
            ·
              refine ⟨5009359240007924189801075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339572826671949459867383 5009359240007924189801075)
              ·
                refine ⟨7514038860011886284701613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5009359240007924189801075 7514038860011886284701613)
                ·
                  refine ⟨2817764572504457356763105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7514038860011886284701613 2817764572504457356763105)
                  ·
                    refine ⟨2113323429378343017572329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2817764572504457356763105 2113323429378343017572329)
                    ·
                      refine ⟨1584992572033757263179247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2113323429378343017572329 1584992572033757263179247)
                      ·
                        rfl

theorem cell23_3086762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_3086762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086762 prefixEnd_3086762 := by exact prefixLift 3086762
  have htrace : WordTrace (prefixWord ++ tailWord_3086762) baseStart_3086762 baseEnd_3086762 := by
    simpa [prefixWord, tailWord_3086762, baseEnd_3086762] using wordTrace_append hprefix tailTrace_3086762
  have hstable : (prefixWord ++ tailWord_3086762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086762).length < 2 ^ (prefixWord ++ tailWord_3086762).sum := by decide
  have hdescent : baseEnd_3086762 < baseStart_3086762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086770 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3]
def baseStart_3086770 : Nat := 118140960795 + 3086770 * 2 ^ 59
def prefixEnd_3086770 : Nat := 4983230072969 + 3 ^ 40 * 3086770 * 2
def baseEnd_3086770 : Nat := 1584996679878993231879209

theorem tailTrace_3086770 : CollatzResearch.WordTrace tailWord_3086770 prefixEnd_3086770 1584996679878993231879209 := by
  unfold tailWord_3086770
  simp only [CollatzResearch.WordTrace]
  refine ⟨28145937756791735797574441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75055834018111295460198509 28145937756791735797574441)
  ·
    refine ⟨21109453317593801848180831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28145937756791735797574441 21109453317593801848180831)
    ·
      refine ⟨31664179976390702772271247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21109453317593801848180831 31664179976390702772271247)
      ·
        refine ⟨47496269964586054158406871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31664179976390702772271247 47496269964586054158406871)
        ·
          refine ⟨71244404946879081237610307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47496269964586054158406871 71244404946879081237610307)
          ·
            refine ⟨106866607420318621856415461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71244404946879081237610307 106866607420318621856415461)
            ·
              refine ⟨20037488891309741598077899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106866607420318621856415461 20037488891309741598077899)
              ·
                refine ⟨30056233336964612397116849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20037488891309741598077899 30056233336964612397116849)
                ·
                  refine ⟨22542175002723459297837637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30056233336964612397116849 22542175002723459297837637)
                  ·
                    refine ⟨4226657813010648618344557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22542175002723459297837637 4226657813010648618344557)
                    ·
                      refine ⟨1584996679878993231879209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4226657813010648618344557 1584996679878993231879209)
                      ·
                        rfl

theorem cell23_3086770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_3086770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086770 prefixEnd_3086770 := by exact prefixLift 3086770
  have htrace : WordTrace (prefixWord ++ tailWord_3086770) baseStart_3086770 baseEnd_3086770 := by
    simpa [prefixWord, tailWord_3086770, baseEnd_3086770] using wordTrace_append hprefix tailTrace_3086770
  have hstable : (prefixWord ++ tailWord_3086770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086770).length < 2 ^ (prefixWord ++ tailWord_3086770).sum := by decide
  have hdescent : baseEnd_3086770 < baseStart_3086770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086788 : List Nat := [2, 3, 3, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_3086788 : Nat := 118140960795 + 3086788 * 2 ^ 59
def prefixEnd_3086788 : Nat := 4983230072969 + 3 ^ 40 * 3086788 * 2
def baseEnd_3086788 : Nat := 1585005922530774161454127

theorem tailTrace_3086788 : CollatzResearch.WordTrace tailWord_3086788 prefixEnd_3086788 1585005922530774161454127 := by
  unfold tailWord_3086788
  simp only [CollatzResearch.WordTrace]
  refine ⟨56292203770550866132226509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75056271694067821509635345 56292203770550866132226509)
  ·
    refine ⟨21109576413956574799584941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56292203770550866132226509 21109576413956574799584941)
    ·
      refine ⟨7916091155233715549844353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21109576413956574799584941 7916091155233715549844353)
      ·
        refine ⟨5937068366425286662383265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7916091155233715549844353 5937068366425286662383265)
        ·
          refine ⟨4452801274818964996787449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5937068366425286662383265 4452801274818964996787449)
          ·
            refine ⟨3339600956114223747590587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4452801274818964996787449 3339600956114223747590587)
            ·
              refine ⟨5009401434171335621385881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339600956114223747590587 5009401434171335621385881)
              ·
                refine ⟨3757051075628501716039411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5009401434171335621385881 3757051075628501716039411)
                ·
                  refine ⟨5635576613442752574059117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757051075628501716039411 5635576613442752574059117)
                  ·
                    refine ⟨2113341230041032215272169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5635576613442752574059117 2113341230041032215272169)
                    ·
                      refine ⟨1585005922530774161454127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2113341230041032215272169 1585005922530774161454127)
                      ·
                        rfl

theorem cell23_3086788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_3086788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086788 prefixEnd_3086788 := by exact prefixLift 3086788
  have htrace : WordTrace (prefixWord ++ tailWord_3086788) baseStart_3086788 baseEnd_3086788 := by
    simpa [prefixWord, tailWord_3086788, baseEnd_3086788] using wordTrace_append hprefix tailTrace_3086788
  have hstable : (prefixWord ++ tailWord_3086788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086788).length < 2 ^ (prefixWord ++ tailWord_3086788).sum := by decide
  have hdescent : baseEnd_3086788 < baseStart_3086788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086803 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 7, 7]
def baseStart_3086803 : Nat := 118140960795 + 3086803 * 2 ^ 59
def prefixEnd_3086803 : Nat := 4983230072969 + 3 ^ 40 * 3086803 * 2
def baseEnd_3086803 : Nat := 528337874913530534255519

theorem tailTrace_3086803 : CollatzResearch.WordTrace tailWord_3086803 prefixEnd_3086803 528337874913530534255519 := by
  unfold tailWord_3086803
  simp only [CollatzResearch.WordTrace]
  refine ⟨112584954636047389826249063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75056636424031593217499375 112584954636047389826249063)
  ·
    refine ⟨168877431954071084739373595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112584954636047389826249063 168877431954071084739373595)
    ·
      refine ⟨253316147931106627109060393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168877431954071084739373595 253316147931106627109060393)
      ·
        refine ⟨189987110948329970331795295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253316147931106627109060393 189987110948329970331795295)
        ·
          refine ⟨284980666422494955497692943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189987110948329970331795295 284980666422494955497692943)
          ·
            refine ⟨427470999633742433246539415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284980666422494955497692943 427470999633742433246539415)
            ·
              refine ⟨641206499450613649869809123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427470999633742433246539415 641206499450613649869809123)
              ·
                refine ⟨961809749175920474804713685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641206499450613649869809123 961809749175920474804713685)
                ·
                  refine ⟨22542415996310636128235477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 961809749175920474804713685 22542415996310636128235477)
                  ·
                    refine ⟨528337874913530534255519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22542415996310636128235477 528337874913530534255519)
                    ·
                      rfl

theorem cell23_3086803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 7].length) (baseStart_3086803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086803 prefixEnd_3086803 := by exact prefixLift 3086803
  have htrace : WordTrace (prefixWord ++ tailWord_3086803) baseStart_3086803 baseEnd_3086803 := by
    simpa [prefixWord, tailWord_3086803, baseEnd_3086803] using wordTrace_append hprefix tailTrace_3086803
  have hstable : (prefixWord ++ tailWord_3086803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086803).length < 2 ^ (prefixWord ++ tailWord_3086803).sum := by decide
  have hdescent : baseEnd_3086803 < baseStart_3086803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086824 : List Nat := [2, 1, 4, 1, 1, 3, 4, 2, 5]
def baseStart_3086824 : Nat := 118140960795 + 3086824 * 2 ^ 59
def prefixEnd_3086824 : Nat := 4983230072969 + 3 ^ 40 * 3086824 * 2
def baseEnd_3086824 : Nat := 176113823092704002289329

theorem tailTrace_3086824 : CollatzResearch.WordTrace tailWord_3086824 prefixEnd_3086824 176113823092704002289329 := by
  unfold tailWord_3086824
  simp only [CollatzResearch.WordTrace]
  refine ⟨56292860284485655206381763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75057147045980873608509017 56292860284485655206381763)
  ·
    refine ⟨84439290426728482809572645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56292860284485655206381763 84439290426728482809572645)
    ·
      refine ⟨15832366955011590526794871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84439290426728482809572645 15832366955011590526794871)
      ·
        refine ⟨23748550432517385790192307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15832366955011590526794871 23748550432517385790192307)
        ·
          refine ⟨35622825648776078685288461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23748550432517385790192307 35622825648776078685288461)
          ·
            refine ⟨13358559618291029506983173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35622825648776078685288461 13358559618291029506983173)
            ·
              refine ⟨2504729928429568032559345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13358559618291029506983173 2504729928429568032559345)
              ·
                refine ⟨1878547446322176024419509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2504729928429568032559345 1878547446322176024419509)
                ·
                  refine ⟨176113823092704002289329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1878547446322176024419509 176113823092704002289329)
                  ·
                    rfl

theorem cell23_3086824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 5].length) (baseStart_3086824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086824 prefixEnd_3086824 := by exact prefixLift 3086824
  have htrace : WordTrace (prefixWord ++ tailWord_3086824) baseStart_3086824 baseEnd_3086824 := by
    simpa [prefixWord, tailWord_3086824, baseEnd_3086824] using wordTrace_append hprefix tailTrace_3086824
  have hstable : (prefixWord ++ tailWord_3086824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086824).length < 2 ^ (prefixWord ++ tailWord_3086824).sum := by decide
  have hdescent : baseEnd_3086824 < baseStart_3086824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086834 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3086834 : Nat := 118140960795 + 3086834 * 2 ^ 59
def prefixEnd_3086834 : Nat := 4983230072969 + 3 ^ 40 * 3086834 * 2
def baseEnd_3086834 : Nat := 1585029542640880981478915

theorem tailTrace_3086834 : CollatzResearch.WordTrace tailWord_3086834 prefixEnd_3086834 1585029542640880981478915 := by
  unfold tailWord_3086834
  simp only [CollatzResearch.WordTrace]
  refine ⟨28146521324733770530156889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75057390199290054747085037 28146521324733770530156889)
  ·
    refine ⟨21109890993550327897617667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28146521324733770530156889 21109890993550327897617667)
    ·
      refine ⟨31664836490325491846426501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21109890993550327897617667 31664836490325491846426501)
      ·
        refine ⟨5937156841936029721204969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31664836490325491846426501 5937156841936029721204969)
        ·
          refine ⟨4452867631452022290903727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5937156841936029721204969 4452867631452022290903727)
          ·
            refine ⟨6679301447178033436355591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4452867631452022290903727 6679301447178033436355591)
            ·
              refine ⟨10018952170767050154533387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6679301447178033436355591 10018952170767050154533387)
              ·
                refine ⟨15028428256150575231800081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10018952170767050154533387 15028428256150575231800081)
                ·
                  refine ⟨11271321192112931423850061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15028428256150575231800081 11271321192112931423850061)
                  ·
                    refine ⟨4226745447042349283943773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11271321192112931423850061 4226745447042349283943773)
                    ·
                      refine ⟨1585029542640880981478915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4226745447042349283943773 1585029542640880981478915)
                      ·
                        rfl

theorem cell23_3086834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3086834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086834 prefixEnd_3086834 := by exact prefixLift 3086834
  have htrace : WordTrace (prefixWord ++ tailWord_3086834) baseStart_3086834 baseEnd_3086834 := by
    simpa [prefixWord, tailWord_3086834, baseEnd_3086834] using wordTrace_append hprefix tailTrace_3086834
  have hstable : (prefixWord ++ tailWord_3086834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086834).length < 2 ^ (prefixWord ++ tailWord_3086834).sum := by decide
  have hdescent : baseEnd_3086834 < baseStart_3086834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086840 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 1, 3, 4]
def baseStart_3086840 : Nat := 118140960795 + 3086840 * 2 ^ 59
def prefixEnd_3086840 : Nat := 4983230072969 + 3 ^ 40 * 3086840 * 2
def baseEnd_3086840 : Nat := 1585032623524807958003887

theorem tailTrace_3086840 : CollatzResearch.WordTrace tailWord_3086840 prefixEnd_3086840 1585032623524807958003887 := by
  unfold tailWord_3086840
  simp only [CollatzResearch.WordTrace]
  refine ⟨56293152068456672572672987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75057536091275563430230649 56293152068456672572672987)
  ·
    refine ⟨84439728102685008859009481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56293152068456672572672987 84439728102685008859009481)
    ·
      refine ⟨63329796077013756644257111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84439728102685008859009481 63329796077013756644257111)
      ·
        refine ⟨94994694115520634966385667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63329796077013756644257111 94994694115520634966385667)
        ·
          refine ⟨142492041173280952449578501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94994694115520634966385667 142492041173280952449578501)
          ·
            refine ⟨26717257719990178584295969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142492041173280952449578501 26717257719990178584295969)
            ·
              refine ⟨20037943289992633938221977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26717257719990178584295969 20037943289992633938221977)
              ·
                refine ⟨15028457467494475453666483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20037943289992633938221977 15028457467494475453666483)
                ·
                  refine ⟨22542686201241713180499725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15028457467494475453666483 22542686201241713180499725)
                  ·
                    refine ⟨8453507325465642442687397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22542686201241713180499725 8453507325465642442687397)
                    ·
                      refine ⟨1585032623524807958003887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8453507325465642442687397 1585032623524807958003887)
                      ·
                        rfl

theorem cell23_3086840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_3086840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086840 prefixEnd_3086840 := by exact prefixLift 3086840
  have htrace : WordTrace (prefixWord ++ tailWord_3086840) baseStart_3086840 baseEnd_3086840 := by
    simpa [prefixWord, tailWord_3086840, baseEnd_3086840] using wordTrace_append hprefix tailTrace_3086840
  have hstable : (prefixWord ++ tailWord_3086840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086840).length < 2 ^ (prefixWord ++ tailWord_3086840).sum := by decide
  have hdescent : baseEnd_3086840 < baseStart_3086840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086907 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 9, 1, 3]
def baseStart_3086907 : Nat := 118140960795 + 3086907 * 2 ^ 59
def prefixEnd_3086907 : Nat := 4983230072969 + 3 ^ 40 * 3086907 * 2
def baseEnd_3086907 : Nat := 1585067026728659195866079

theorem tailTrace_3086907 : CollatzResearch.WordTrace tailWord_3086907 prefixEnd_3086907 1585067026728659195866079 := by
  unfold tailWord_3086907
  simp only [CollatzResearch.WordTrace]
  refine ⟨112588747827670615588034975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75059165218447077058689983 112588747827670615588034975)
  ·
    refine ⟨168883121741505923382052463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112588747827670615588034975 168883121741505923382052463)
    ·
      refine ⟨253324682612258885073078695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168883121741505923382052463 253324682612258885073078695)
      ·
        refine ⟨379987023918388327609618043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253324682612258885073078695 379987023918388327609618043)
        ·
          refine ⟨569980535877582491414427065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379987023918388327609618043 569980535877582491414427065)
          ·
            refine ⟨427485401908186868560820299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569980535877582491414427065 427485401908186868560820299)
            ·
              refine ⟨641228102862280302841230449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427485401908186868560820299 641228102862280302841230449)
              ·
                refine ⟨480921077146710227130922837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641228102862280302841230449 480921077146710227130922837)
                ·
                  refine ⟨2817896936406505237095251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 480921077146710227130922837 2817896936406505237095251)
                  ·
                    refine ⟨4226845404609757855642877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2817896936406505237095251 4226845404609757855642877)
                    ·
                      refine ⟨1585067026728659195866079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4226845404609757855642877 1585067026728659195866079)
                      ·
                        rfl

theorem cell23_3086907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 1, 3].length) (baseStart_3086907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086907 prefixEnd_3086907 := by exact prefixLift 3086907
  have htrace : WordTrace (prefixWord ++ tailWord_3086907) baseStart_3086907 baseEnd_3086907 := by
    simpa [prefixWord, tailWord_3086907, baseEnd_3086907] using wordTrace_append hprefix tailTrace_3086907
  have hstable : (prefixWord ++ tailWord_3086907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086907).length < 2 ^ (prefixWord ++ tailWord_3086907).sum := by decide
  have hdescent : baseEnd_3086907 < baseStart_3086907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086927 : List Nat := [1, 1, 2, 1, 1, 2, 6, 3, 1, 5]
def baseStart_3086927 : Nat := 118140960795 + 3086927 * 2 ^ 59
def prefixEnd_3086927 : Nat := 4983230072969 + 3 ^ 40 * 3086927 * 2
def baseEnd_3086927 : Nat := 528359098780583039205329

theorem tailTrace_3086927 : CollatzResearch.WordTrace tailWord_3086927 prefixEnd_3086927 528359098780583039205329 := by
  unfold tailWord_3086927
  simp only [CollatzResearch.WordTrace]
  refine ⟨112589477287598159003763035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75059651525065439335842023 112589477287598159003763035)
  ·
    refine ⟨168884215931397238505644553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112589477287598159003763035 168884215931397238505644553)
    ·
      refine ⟨126663161948547928879233415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168884215931397238505644553 126663161948547928879233415)
      ·
        refine ⟨189994742922821893318850123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126663161948547928879233415 189994742922821893318850123)
        ·
          refine ⟨284992114384232839978275185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189994742922821893318850123 284992114384232839978275185)
          ·
            refine ⟨213744085788174629983706389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284992114384232839978275185 213744085788174629983706389)
            ·
              refine ⟨10019254021320685780486237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 213744085788174629983706389 10019254021320685780486237)
              ·
                refine ⟨3757220257995257167682339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10019254021320685780486237 3757220257995257167682339)
                ·
                  refine ⟨5635830386992885751523509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757220257995257167682339 5635830386992885751523509)
                  ·
                    refine ⟨528359098780583039205329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5635830386992885751523509 528359098780583039205329)
                    ·
                      rfl

theorem cell23_3086927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 5].length) (baseStart_3086927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086927 prefixEnd_3086927 := by exact prefixLift 3086927
  have htrace : WordTrace (prefixWord ++ tailWord_3086927) baseStart_3086927 baseEnd_3086927 := by
    simpa [prefixWord, tailWord_3086927, baseEnd_3086927] using wordTrace_append hprefix tailTrace_3086927
  have hstable : (prefixWord ++ tailWord_3086927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086927).length < 2 ^ (prefixWord ++ tailWord_3086927).sum := by decide
  have hdescent : baseEnd_3086927 < baseStart_3086927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086947 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 4]
def baseStart_3086947 : Nat := 118140960795 + 3086947 * 2 ^ 59
def prefixEnd_3086947 : Nat := 4983230072969 + 3 ^ 40 * 3086947 * 2
def baseEnd_3086947 : Nat := 1585087565954839039365895

theorem tailTrace_3086947 : CollatzResearch.WordTrace tailWord_3086947 prefixEnd_3086947 1585087565954839039365895 := by
  unfold tailWord_3086947
  simp only [CollatzResearch.WordTrace]
  refine ⟨112590206747525702419491095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75060137831683801612994063 112590206747525702419491095)
  ·
    refine ⟨168885310121288553629236643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112590206747525702419491095 168885310121288553629236643)
    ·
      refine ⟨253327965181932830443854965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168885310121288553629236643 253327965181932830443854965)
      ·
        refine ⟨23749496735806202854111403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253327965181932830443854965 23749496735806202854111403)
        ·
          refine ⟨35624245103709304281167105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23749496735806202854111403 35624245103709304281167105)
          ·
            refine ⟨26718183827781978210875329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35624245103709304281167105 26718183827781978210875329)
            ·
              refine ⟨20038637870836483658156497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26718183827781978210875329 20038637870836483658156497)
              ·
                refine ⟨15028978403127362743617373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20038637870836483658156497 15028978403127362743617373)
                ·
                  refine ⟨5635866901172761028856515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15028978403127362743617373 5635866901172761028856515)
                  ·
                    refine ⟨8453800351759141543284773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5635866901172761028856515 8453800351759141543284773)
                    ·
                      refine ⟨1585087565954839039365895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8453800351759141543284773 1585087565954839039365895)
                      ·
                        rfl

theorem cell23_3086947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_3086947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086947 prefixEnd_3086947 := by exact prefixLift 3086947
  have htrace : WordTrace (prefixWord ++ tailWord_3086947) baseStart_3086947 baseEnd_3086947 := by
    simpa [prefixWord, tailWord_3086947, baseEnd_3086947] using wordTrace_append hprefix tailTrace_3086947
  have hstable : (prefixWord ++ tailWord_3086947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086947).length < 2 ^ (prefixWord ++ tailWord_3086947).sum := by decide
  have hdescent : baseEnd_3086947 < baseStart_3086947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086981 : List Nat := [1, 3, 1, 1, 4, 3, 3, 1, 1, 1, 4]
def baseStart_3086981 : Nat := 118140960795 + 3086981 * 2 ^ 59
def prefixEnd_3086981 : Nat := 4983230072969 + 3 ^ 40 * 3086981 * 2
def baseEnd_3086981 : Nat := 1585105024297091906340739

theorem tailTrace_3086981 : CollatzResearch.WordTrace tailWord_3086981 prefixEnd_3086981 1585105024297091906340739 := by
  unfold tailWord_3086981
  simp only [CollatzResearch.WordTrace]
  refine ⟨112591446829402526226228797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75060964552935017484152531 112591446829402526226228797)
  ·
    refine ⟨42221792561025947334835799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112591446829402526226228797 42221792561025947334835799)
    ·
      refine ⟨63332688841538921002253699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42221792561025947334835799 63332688841538921002253699)
      ·
        refine ⟨94999033262308381503380549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63332688841538921002253699 94999033262308381503380549)
        ·
          refine ⟨17812318736682821531883853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94999033262308381503380549 17812318736682821531883853)
          ·
            refine ⟨6679619526256058074456445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17812318736682821531883853 6679619526256058074456445)
            ·
              refine ⟨2504857322346021777921167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6679619526256058074456445 2504857322346021777921167)
              ·
                refine ⟨3757285983519032666881751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504857322346021777921167 3757285983519032666881751)
                ·
                  refine ⟨5635928975278549000322627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757285983519032666881751 5635928975278549000322627)
                  ·
                    refine ⟨8453893462917823500483941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5635928975278549000322627 8453893462917823500483941)
                    ·
                      refine ⟨1585105024297091906340739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8453893462917823500483941 1585105024297091906340739)
                      ·
                        rfl

theorem cell23_3086981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 1, 1, 4].length) (baseStart_3086981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086981 prefixEnd_3086981 := by exact prefixLift 3086981
  have htrace : WordTrace (prefixWord ++ tailWord_3086981) baseStart_3086981 baseEnd_3086981 := by
    simpa [prefixWord, tailWord_3086981, baseEnd_3086981] using wordTrace_append hprefix tailTrace_3086981
  have hstable : (prefixWord ++ tailWord_3086981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086981).length < 2 ^ (prefixWord ++ tailWord_3086981).sum := by decide
  have hdescent : baseEnd_3086981 < baseStart_3086981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087004 : List Nat := [2, 2, 3, 2, 2, 3, 1, 8]
def baseStart_3087004 : Nat := 118140960795 + 3087004 * 2 ^ 59
def prefixEnd_3087004 : Nat := 4983230072969 + 3 ^ 40 * 3087004 * 2
def baseEnd_3087004 : Nat := 58708030901931308013079

theorem tailTrace_3087004 : CollatzResearch.WordTrace tailWord_3087004 prefixEnd_3087004 58708030901931308013079 := by
  unfold tailWord_3087004
  simp only [CollatzResearch.WordTrace]
  refine ⟨56296142854159600577158033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75061523805546134102877377 56296142854159600577158033)
  ·
    refine ⟨42222107140619700432868525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56296142854159600577158033 42222107140619700432868525)
    ·
      refine ⟨15833290177732387662325697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42222107140619700432868525 15833290177732387662325697)
      ·
        refine ⟨11874967633299290746744273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15833290177732387662325697 11874967633299290746744273)
        ·
          refine ⟨8906225724974468060058205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11874967633299290746744273 8906225724974468060058205)
          ·
            refine ⟨3339834646865425522521827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8906225724974468060058205 3339834646865425522521827)
            ·
              refine ⟨5009751970298138283782741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339834646865425522521827 5009751970298138283782741)
              ·
                refine ⟨58708030901931308013079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5009751970298138283782741 58708030901931308013079)
                ·
                  rfl

theorem cell23_3087004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 8].length) (baseStart_3087004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087004 prefixEnd_3087004 := by exact prefixLift 3087004
  have htrace : WordTrace (prefixWord ++ tailWord_3087004) baseStart_3087004 baseEnd_3087004 := by
    simpa [prefixWord, tailWord_3087004, baseEnd_3087004] using wordTrace_append hprefix tailTrace_3087004
  have hstable : (prefixWord ++ tailWord_3087004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087004).length < 2 ^ (prefixWord ++ tailWord_3087004).sum := by decide
  have hdescent : baseEnd_3087004 < baseStart_3087004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087015 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_3087015 : Nat := 118140960795 + 3087015 * 2 ^ 59
def prefixEnd_3087015 : Nat := 4983230072969 + 3 ^ 40 * 3087015 * 2
def baseEnd_3087015 : Nat := 1585122482639344773315583

theorem tailTrace_3087015 : CollatzResearch.WordTrace tailWord_3087015 prefixEnd_3087015 1585122482639344773315583 := by
  unfold tailWord_3087015
  simp only [CollatzResearch.WordTrace]
  refine ⟨112592686911279350032966499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75061791274186233355310999 112592686911279350032966499)
  ·
    refine ⟨168889030366919025049449749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112592686911279350032966499 168889030366919025049449749)
    ·
      refine ⟨7916673298449329299192957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 168889030366919025049449749 7916673298449329299192957)
      ·
        refine ⟨2968752486918498487197359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7916673298449329299192957 2968752486918498487197359)
        ·
          refine ⟨4453128730377747730796039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2968752486918498487197359 4453128730377747730796039)
          ·
            refine ⟨6679693095566621596194059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4453128730377747730796039 6679693095566621596194059)
            ·
              refine ⟨10019539643349932394291089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6679693095566621596194059 10019539643349932394291089)
              ·
                refine ⟨7514654732512449295718317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10019539643349932394291089 7514654732512449295718317)
                ·
                  refine ⟨2817995524692168485894369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7514654732512449295718317 2817995524692168485894369)
                  ·
                    refine ⟨2113496643519126364420777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2817995524692168485894369 2113496643519126364420777)
                    ·
                      refine ⟨1585122482639344773315583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2113496643519126364420777 1585122482639344773315583)
                      ·
                        rfl

theorem cell23_3087015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_3087015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087015 prefixEnd_3087015 := by exact prefixLift 3087015
  have htrace : WordTrace (prefixWord ++ tailWord_3087015) baseStart_3087015 baseEnd_3087015 := by
    simpa [prefixWord, tailWord_3087015, baseEnd_3087015] using wordTrace_append hprefix tailTrace_3087015
  have hstable : (prefixWord ++ tailWord_3087015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087015).length < 2 ^ (prefixWord ++ tailWord_3087015).sum := by decide
  have hdescent : baseEnd_3087015 < baseStart_3087015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087048 : List Nat := [2, 1, 3, 1, 2, 5, 1, 2, 2, 1, 3]
def baseStart_3087048 : Nat := 118140960795 + 3087048 * 2 ^ 59
def prefixEnd_3087048 : Nat := 4983230072969 + 3 ^ 40 * 3087048 * 2
def baseEnd_3087048 : Nat := 1585139427500943144202931

theorem tailTrace_3087048 : CollatzResearch.WordTrace tailWord_3087048 prefixEnd_3087048 1585139427500943144202931 := by
  unfold tailWord_3087048
  simp only [CollatzResearch.WordTrace]
  refine ⟨56296945260079898334458899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75062593680106531112611865 56296945260079898334458899)
  ·
    refine ⟨84445417890119847501688349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56296945260079898334458899 84445417890119847501688349)
    ·
      refine ⟨31667031708794942813133131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84445417890119847501688349 31667031708794942813133131)
      ·
        refine ⟨47500547563192414219699697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31667031708794942813133131 47500547563192414219699697)
        ·
          refine ⟨35625410672394310664774773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47500547563192414219699697 35625410672394310664774773)
          ·
            refine ⟨3339882250536966624822635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35625410672394310664774773 3339882250536966624822635)
            ·
              refine ⟨5009823375805449937233953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339882250536966624822635 5009823375805449937233953)
              ·
                refine ⟨3757367531854087452925465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5009823375805449937233953 3757367531854087452925465)
                ·
                  refine ⟨2818025648890565589694099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3757367531854087452925465 2818025648890565589694099)
                  ·
                    refine ⟨4227038473335848384541149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2818025648890565589694099 4227038473335848384541149)
                    ·
                      refine ⟨1585139427500943144202931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4227038473335848384541149 1585139427500943144202931)
                      ·
                        rfl

theorem cell23_3087048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_3087048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087048 prefixEnd_3087048 := by exact prefixLift 3087048
  have htrace : WordTrace (prefixWord ++ tailWord_3087048) baseStart_3087048 baseEnd_3087048 := by
    simpa [prefixWord, tailWord_3087048, baseEnd_3087048] using wordTrace_append hprefix tailTrace_3087048
  have hstable : (prefixWord ++ tailWord_3087048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087048).length < 2 ^ (prefixWord ++ tailWord_3087048).sum := by decide
  have hdescent : baseEnd_3087048 < baseStart_3087048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087071 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 1, 4, 2]
def baseStart_3087071 : Nat := 118140960795 + 3087071 * 2 ^ 59
def prefixEnd_3087071 : Nat := 4983230072969 + 3 ^ 40 * 3087071 * 2
def baseEnd_3087071 : Nat := 1585151237555996554215325

theorem tailTrace_3087071 : CollatzResearch.WordTrace tailWord_3087071 prefixEnd_3087071 1585151237555996554215325 := by
  unfold tailWord_3087071
  simp only [CollatzResearch.WordTrace]
  refine ⟨112594729399076471597005067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75063152932717647731336711 112594729399076471597005067)
  ·
    refine ⟨168892094098614707395507601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112594729399076471597005067 168892094098614707395507601)
    ·
      refine ⟨126669070573961030546630701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168892094098614707395507601 126669070573961030546630701)
      ·
        refine ⟨47500901465235386454986513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126669070573961030546630701 47500901465235386454986513)
        ·
          refine ⟨35625676098926539841239885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47500901465235386454986513 35625676098926539841239885)
          ·
            refine ⟨13359628537097452440464957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35625676098926539841239885 13359628537097452440464957)
            ·
              refine ⟨5009860701411544665174359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13359628537097452440464957 5009860701411544665174359)
              ·
                refine ⟨7514791052117316997761539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5009860701411544665174359 7514791052117316997761539)
                ·
                  refine ⟨11272186578175975496642309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7514791052117316997761539 11272186578175975496642309)
                  ·
                    refine ⟨2113534983407995405620433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11272186578175975496642309 2113534983407995405620433)
                    ·
                      refine ⟨1585151237555996554215325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2113534983407995405620433 1585151237555996554215325)
                      ·
                        rfl

theorem cell23_3087071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_3087071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087071 prefixEnd_3087071 := by exact prefixLift 3087071
  have htrace : WordTrace (prefixWord ++ tailWord_3087071) baseStart_3087071 baseEnd_3087071 := by
    simpa [prefixWord, tailWord_3087071, baseEnd_3087071] using wordTrace_append hprefix tailTrace_3087071
  have hstable : (prefixWord ++ tailWord_3087071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087071).length < 2 ^ (prefixWord ++ tailWord_3087071).sum := by decide
  have hdescent : baseEnd_3087071 < baseStart_3087071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087111 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 7]
def baseStart_3087111 : Nat := 118140960795 + 3087111 * 2 ^ 59
def prefixEnd_3087111 : Nat := 4983230072969 + 3 ^ 40 * 3087111 * 2
def baseEnd_3087111 : Nat := 176130197420241821968349

theorem tailTrace_3087111 : CollatzResearch.WordTrace tailWord_3087111 prefixEnd_3087111 176130197420241821968349 := by
  unfold tailWord_3087111
  simp only [CollatzResearch.WordTrace]
  refine ⟨112596188318931558428461187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75064125545954372285640791 112596188318931558428461187)
  ·
    refine ⟨168894282478397337642691781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112596188318931558428461187 168894282478397337642691781)
    ·
      refine ⟨31667677964699500808004709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168894282478397337642691781 31667677964699500808004709)
      ·
        refine ⟨5937689618381156401500883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31667677964699500808004709 5937689618381156401500883)
        ·
          refine ⟨8906534427571734602251325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5937689618381156401500883 8906534427571734602251325)
          ·
            refine ⟨3339950410339400475844247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8906534427571734602251325 3339950410339400475844247)
            ·
              refine ⟨5009925615509100713766371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339950410339400475844247 5009925615509100713766371)
              ·
                refine ⟨7514888423263651070649557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5009925615509100713766371 7514888423263651070649557)
                ·
                  refine ⟨176130197420241821968349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7514888423263651070649557 176130197420241821968349)
                  ·
                    rfl

theorem cell23_3087111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 7].length) (baseStart_3087111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087111 prefixEnd_3087111 := by exact prefixLift 3087111
  have htrace : WordTrace (prefixWord ++ tailWord_3087111) baseStart_3087111 baseEnd_3087111 := by
    simpa [prefixWord, tailWord_3087111, baseEnd_3087111] using wordTrace_append hprefix tailTrace_3087111
  have hstable : (prefixWord ++ tailWord_3087111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087111).length < 2 ^ (prefixWord ++ tailWord_3087111).sum := by decide
  have hdescent : baseEnd_3087111 < baseStart_3087111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087122 : List Nat := [3, 2, 4, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_3087122 : Nat := 118140960795 + 3087122 * 2 ^ 59
def prefixEnd_3087122 : Nat := 4983230072969 + 3 ^ 40 * 3087122 * 2
def baseEnd_3087122 : Nat := 1585177425069375854677591

theorem tailTrace_3087122 : CollatzResearch.WordTrace tailWord_3087122 prefixEnd_3087122 1585177425069375854677591 := by
  unfold tailWord_3087122
  simp only [CollatzResearch.WordTrace]
  refine ⟨28149147380472926826777905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75064393014594471538074413 28149147380472926826777905)
  ·
    refine ⟨21111860535354695120083429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28149147380472926826777905 21111860535354695120083429)
    ·
      refine ⟨3958473850379005335015643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21111860535354695120083429 3958473850379005335015643)
      ·
        refine ⟨5937710775568508002523465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3958473850379005335015643 5937710775568508002523465)
        ·
          refine ⟨4453283081676381001892599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5937710775568508002523465 4453283081676381001892599)
          ·
            refine ⟨6679924622514571502838899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4453283081676381001892599 6679924622514571502838899)
            ·
              refine ⟨10019886933771857254258349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6679924622514571502838899 10019886933771857254258349)
              ·
                refine ⟨3757457600164446470346881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10019886933771857254258349 3757457600164446470346881)
                ·
                  refine ⟨2818093200123334852760161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3757457600164446470346881 2818093200123334852760161)
                  ·
                    refine ⟨2113569900092501139570121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2818093200123334852760161 2113569900092501139570121)
                    ·
                      refine ⟨1585177425069375854677591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2113569900092501139570121 1585177425069375854677591)
                      ·
                        rfl

theorem cell23_3087122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_3087122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087122 prefixEnd_3087122 := by exact prefixLift 3087122
  have htrace : WordTrace (prefixWord ++ tailWord_3087122) baseStart_3087122 baseEnd_3087122 := by
    simpa [prefixWord, tailWord_3087122, baseEnd_3087122] using wordTrace_append hprefix tailTrace_3087122
  have hstable : (prefixWord ++ tailWord_3087122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087122).length < 2 ^ (prefixWord ++ tailWord_3087122).sum := by decide
  have hdescent : baseEnd_3087122 < baseStart_3087122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087147 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 5]
def baseStart_3087147 : Nat := 118140960795 + 3087147 * 2 ^ 59
def prefixEnd_3087147 : Nat := 4983230072969 + 3 ^ 40 * 3087147 * 2
def baseEnd_3087147 : Nat := 1585190262085738256864975

theorem tailTrace_3087147 : CollatzResearch.WordTrace tailWord_3087147 prefixEnd_3087147 1585190262085738256864975 := by
  unfold tailWord_3087147
  simp only [CollatzResearch.WordTrace]
  refine ⟨112597501346801136576771695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75065000897867424384514463 112597501346801136576771695)
  ·
    refine ⟨168896252020201704865157543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112597501346801136576771695 168896252020201704865157543)
    ·
      refine ⟨253344378030302557297736315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168896252020201704865157543 253344378030302557297736315)
      ·
        refine ⟨380016567045453835946604473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253344378030302557297736315 380016567045453835946604473)
        ·
          refine ⟨285012425284090376959953355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380016567045453835946604473 285012425284090376959953355)
          ·
            refine ⟨427518637926135565439930033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285012425284090376959953355 427518637926135565439930033)
            ·
              refine ⟨320638978444601674079947525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427518637926135565439930033 320638978444601674079947525)
              ·
                refine ⟨60119808458362813889990161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 320638978444601674079947525 60119808458362813889990161)
                ·
                  refine ⟨45089856343772110417492621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60119808458362813889990161 45089856343772110417492621)
                  ·
                    refine ⟨16908696128914541406559733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45089856343772110417492621 16908696128914541406559733)
                    ·
                      refine ⟨1585190262085738256864975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16908696128914541406559733 1585190262085738256864975)
                      ·
                        rfl

theorem cell23_3087147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 5].length) (baseStart_3087147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087147 prefixEnd_3087147 := by exact prefixLift 3087147
  have htrace : WordTrace (prefixWord ++ tailWord_3087147) baseStart_3087147 baseEnd_3087147 := by
    simpa [prefixWord, tailWord_3087147, baseEnd_3087147] using wordTrace_append hprefix tailTrace_3087147
  have hstable : (prefixWord ++ tailWord_3087147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087147).length < 2 ^ (prefixWord ++ tailWord_3087147).sum := by decide
  have hdescent : baseEnd_3087147 < baseStart_3087147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087164 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 3, 4, 3]
def baseStart_3087164 : Nat := 118140960795 + 3087164 * 2 ^ 59
def prefixEnd_3087164 : Nat := 4983230072969 + 3 ^ 40 * 3087164 * 2
def baseEnd_3087164 : Nat := 1585198991256864690352397

theorem tailTrace_3087164 : CollatzResearch.WordTrace tailWord_3087164 prefixEnd_3087164 1585198991256864690352397 := by
  unfold tailWord_3087164
  simp only [CollatzResearch.WordTrace]
  refine ⟨56299060693869774240070273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75065414258493032320093697 56299060693869774240070273)
  ·
    refine ⟨42224295520402330680052705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56299060693869774240070273 42224295520402330680052705)
    ·
      refine ⟨31668221640301748010039529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42224295520402330680052705 31668221640301748010039529)
      ·
        refine ⟨23751166230226311007529647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31668221640301748010039529 23751166230226311007529647)
        ·
          refine ⟨35626749345339466511294471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23751166230226311007529647 35626749345339466511294471)
          ·
            refine ⟨53440124018009199766941707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35626749345339466511294471 53440124018009199766941707)
            ·
              refine ⟨80160186027013799650412561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53440124018009199766941707 80160186027013799650412561)
              ·
                refine ⟨60120139520260349737809421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80160186027013799650412561 60120139520260349737809421)
                ·
                  refine ⟨22545052320097631151678533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60120139520260349737809421 22545052320097631151678533)
                  ·
                    refine ⟨4227197310018305840939725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22545052320097631151678533 4227197310018305840939725)
                    ·
                      refine ⟨1585198991256864690352397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4227197310018305840939725 1585198991256864690352397)
                      ·
                        rfl

theorem cell23_3087164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_3087164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087164 prefixEnd_3087164 := by exact prefixLift 3087164
  have htrace : WordTrace (prefixWord ++ tailWord_3087164) baseStart_3087164 baseEnd_3087164 := by
    simpa [prefixWord, tailWord_3087164, baseEnd_3087164] using wordTrace_append hprefix tailTrace_3087164
  have hstable : (prefixWord ++ tailWord_3087164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087164).length < 2 ^ (prefixWord ++ tailWord_3087164).sum := by decide
  have hdescent : baseEnd_3087164 < baseStart_3087164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087184 : List Nat := [2, 1, 1, 1, 1, 4, 4, 3, 6]
def baseStart_3087184 : Nat := 118140960795 + 3087184 * 2 ^ 59
def prefixEnd_3087184 : Nat := 4983230072969 + 3 ^ 40 * 3087184 * 2
def baseEnd_3087184 : Nat := 176134362318883845789145

theorem tailTrace_3087184 : CollatzResearch.WordTrace tailWord_3087184 prefixEnd_3087184 176134362318883845789145 := by
  unfold tailWord_3087184
  simp only [CollatzResearch.WordTrace]
  refine ⟨56299425423833545947934303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75065900565111394597245737 56299425423833545947934303)
  ·
    refine ⟨84449138135750318921901455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56299425423833545947934303 84449138135750318921901455)
    ·
      refine ⟨126673707203625478382852183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84449138135750318921901455 126673707203625478382852183)
      ·
        refine ⟨190010560805438217574278275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126673707203625478382852183 190010560805438217574278275)
        ·
          refine ⟨285015841208157326361417413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190010560805438217574278275 285015841208157326361417413)
          ·
            refine ⟨53440470226529498692765765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285015841208157326361417413 53440470226529498692765765)
            ·
              refine ⟨10020088167474281004893581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53440470226529498692765765 10020088167474281004893581)
              ·
                refine ⟨3757533062802855376835093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10020088167474281004893581 3757533062802855376835093)
                ·
                  refine ⟨176134362318883845789145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3757533062802855376835093 176134362318883845789145)
                  ·
                    rfl

theorem cell23_3087184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 6].length) (baseStart_3087184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087184 prefixEnd_3087184 := by exact prefixLift 3087184
  have htrace : WordTrace (prefixWord ++ tailWord_3087184) baseStart_3087184 baseEnd_3087184 := by
    simpa [prefixWord, tailWord_3087184, baseEnd_3087184] using wordTrace_append hprefix tailTrace_3087184
  have hstable : (prefixWord ++ tailWord_3087184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087184).length < 2 ^ (prefixWord ++ tailWord_3087184).sum := by decide
  have hdescent : baseEnd_3087184 < baseStart_3087184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087188 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_3087188 : Nat := 118140960795 + 3087188 * 2 ^ 59
def prefixEnd_3087188 : Nat := 4983230072969 + 3 ^ 40 * 3087188 * 2
def baseEnd_3087188 : Nat := 528403771597524198817429

theorem tailTrace_3087188 : CollatzResearch.WordTrace tailWord_3087188 prefixEnd_3087188 528403771597524198817429 := by
  unfold tailWord_3087188
  simp only [CollatzResearch.WordTrace]
  refine ⟨56299498369826300289507109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75065997826435067052676145 56299498369826300289507109)
  ·
    refine ⟨10556155944342431304282583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56299498369826300289507109 10556155944342431304282583)
    ·
      refine ⟨15834233916513646956423875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10556155944342431304282583 15834233916513646956423875)
      ·
        refine ⟨23751350874770470434635813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15834233916513646956423875 23751350874770470434635813)
        ·
          refine ⟨4453378289019463206494215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23751350874770470434635813 4453378289019463206494215)
          ·
            refine ⟨6680067433529194809741323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4453378289019463206494215 6680067433529194809741323)
            ·
              refine ⟨10020101150293792214611985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6680067433529194809741323 10020101150293792214611985)
              ·
                refine ⟨7515075862720344160958989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10020101150293792214611985 7515075862720344160958989)
                ·
                  refine ⟨2818153448520129060359621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7515075862720344160958989 2818153448520129060359621)
                  ·
                    refine ⟨528403771597524198817429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2818153448520129060359621 528403771597524198817429)
                    ·
                      rfl

theorem cell23_3087188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_3087188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087188 prefixEnd_3087188 := by exact prefixLift 3087188
  have htrace : WordTrace (prefixWord ++ tailWord_3087188) baseStart_3087188 baseEnd_3087188 := by
    simpa [prefixWord, tailWord_3087188, baseEnd_3087188] using wordTrace_append hprefix tailTrace_3087188
  have hstable : (prefixWord ++ tailWord_3087188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087188).length < 2 ^ (prefixWord ++ tailWord_3087188).sum := by decide
  have hdescent : baseEnd_3087188 < baseStart_3087188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087261 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 6, 4]
def baseStart_3087261 : Nat := 118140960795 + 3087261 * 2 ^ 59
def prefixEnd_3087261 : Nat := 4983230072969 + 3 ^ 40 * 3087261 * 2
def baseEnd_3087261 : Nat := 528416266293450270279817

theorem tailTrace_3087261 : CollatzResearch.WordTrace tailWord_3087261 prefixEnd_3087261 528416266293450270279817 := by
  unfold tailWord_3087261
  simp only [CollatzResearch.WordTrace]
  refine ⟨112601659268388134046421637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75067772845592089364281091 112601659268388134046421637)
  ·
    refine ⟨21112811112822775133704057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112601659268388134046421637 21112811112822775133704057)
    ·
      refine ⟨15834608334617081350278043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21112811112822775133704057 15834608334617081350278043)
      ·
        refine ⟨23751912501925622025417065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15834608334617081350278043 23751912501925622025417065)
        ·
          refine ⟨17813934376444216519062799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23751912501925622025417065 17813934376444216519062799)
          ·
            refine ⟨26720901564666324778594199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17813934376444216519062799 26720901564666324778594199)
            ·
              refine ⟨40081352346999487167891299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26720901564666324778594199 40081352346999487167891299)
              ·
                refine ⟨60122028520499230751836949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40081352346999487167891299 60122028520499230751836949)
                ·
                  refine ⟨2818220086898401441492357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60122028520499230751836949 2818220086898401441492357)
                  ·
                    refine ⟨528416266293450270279817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2818220086898401441492357 528416266293450270279817)
                    ·
                      rfl

theorem cell23_3087261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_3087261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087261 prefixEnd_3087261 := by exact prefixLift 3087261
  have htrace : WordTrace (prefixWord ++ tailWord_3087261) baseStart_3087261 baseEnd_3087261 := by
    simpa [prefixWord, tailWord_3087261, baseEnd_3087261] using wordTrace_append hprefix tailTrace_3087261
  have hstable : (prefixWord ++ tailWord_3087261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087261).length < 2 ^ (prefixWord ++ tailWord_3087261).sum := by decide
  have hdescent : baseEnd_3087261 < baseStart_3087261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087286 : List Nat := [5, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_3087286 : Nat := 118140960795 + 3087286 * 2 ^ 59
def prefixEnd_3087286 : Nat := 4983230072969 + 3 ^ 40 * 3087286 * 2
def baseEnd_3087286 : Nat := 176140181766301468114093

theorem tailTrace_3087286 : CollatzResearch.WordTrace tailWord_3087286 prefixEnd_3087286 176140181766301468114093 := by
  unfold tailWord_3087286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7037660693331097707255107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75068380728865042210721141 7037660693331097707255107)
  ·
    refine ⟨10556491039996646560882661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7037660693331097707255107 10556491039996646560882661)
    ·
      refine ⟨1979342069999371230165499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10556491039996646560882661 1979342069999371230165499)
      ·
        refine ⟨2969013104999056845248249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1979342069999371230165499 2969013104999056845248249)
        ·
          refine ⟨2226759828749292633936187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2969013104999056845248249 2226759828749292633936187)
          ·
            refine ⟨3340139743123938950904281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226759828749292633936187 3340139743123938950904281)
            ·
              refine ⟨2505104807342954213178211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3340139743123938950904281 2505104807342954213178211)
              ·
                refine ⟨3757657211014431319767317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2505104807342954213178211 3757657211014431319767317)
                ·
                  refine ⟨176140181766301468114093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3757657211014431319767317 176140181766301468114093)
                  ·
                    rfl

theorem cell23_3087286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_3087286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087286 prefixEnd_3087286 := by exact prefixLift 3087286
  have htrace : WordTrace (prefixWord ++ tailWord_3087286) baseStart_3087286 baseEnd_3087286 := by
    simpa [prefixWord, tailWord_3087286, baseEnd_3087286] using wordTrace_append hprefix tailTrace_3087286
  have hstable : (prefixWord ++ tailWord_3087286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087286).length < 2 ^ (prefixWord ++ tailWord_3087286).sum := by decide
  have hdescent : baseEnd_3087286 < baseStart_3087286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087335 : List Nat := [1, 1, 5, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_3087335 : Nat := 118140960795 + 3087335 * 2 ^ 59
def prefixEnd_3087335 : Nat := 4983230072969 + 3 ^ 40 * 3087335 * 2
def baseEnd_3087335 : Nat := 1585286796448783521314111

theorem tailTrace_3087335 : CollatzResearch.WordTrace tailWord_3087335 prefixEnd_3087335 1585286796448783521314111 := by
  unfold tailWord_3087335
  simp only [CollatzResearch.WordTrace]
  refine ⟨112604358270120044684615459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75069572180080029789743639 112604358270120044684615459)
  ·
    refine ⟨168906537405180067026923189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112604358270120044684615459 168906537405180067026923189)
    ·
      refine ⟨15834987881735631283774049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168906537405180067026923189 15834987881735631283774049)
      ·
        refine ⟨11876240911301723462830537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15834987881735631283774049 11876240911301723462830537)
        ·
          refine ⟨8907180683476292597122903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11876240911301723462830537 8907180683476292597122903)
          ·
            refine ⟨13360771025214438895684355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8907180683476292597122903 13360771025214438895684355)
            ·
              refine ⟨20041156537821658343526533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13360771025214438895684355 20041156537821658343526533)
              ·
                refine ⟨3757716850841560939411225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20041156537821658343526533 3757716850841560939411225)
                ·
                  refine ⟨2818287638131170704558419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3757716850841560939411225 2818287638131170704558419)
                  ·
                    refine ⟨4227431457196756056837629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2818287638131170704558419 4227431457196756056837629)
                    ·
                      refine ⟨1585286796448783521314111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4227431457196756056837629 1585286796448783521314111)
                      ·
                        rfl

theorem cell23_3087335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_3087335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087335 prefixEnd_3087335 := by exact prefixLift 3087335
  have htrace : WordTrace (prefixWord ++ tailWord_3087335) baseStart_3087335 baseEnd_3087335 := by
    simpa [prefixWord, tailWord_3087335, baseEnd_3087335] using wordTrace_append hprefix tailTrace_3087335
  have hstable : (prefixWord ++ tailWord_3087335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087335).length < 2 ^ (prefixWord ++ tailWord_3087335).sum := by decide
  have hdescent : baseEnd_3087335 < baseStart_3087335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087418 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2]
def baseStart_3087418 : Nat := 118140960795 + 3087418 * 2 ^ 59
def prefixEnd_3087418 : Nat := 4983230072969 + 3 ^ 40 * 3087418 * 2
def baseEnd_3087418 : Nat := 1585329415343106696576229

theorem tailTrace_3087418 : CollatzResearch.WordTrace tailWord_3087418 prefixEnd_3087418 1585329415343106696576229 := by
  unfold tailWord_3087418
  simp only [CollatzResearch.WordTrace]
  refine ⟨28151846382204837464971727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75071590352546233239924605 28151846382204837464971727)
  ·
    refine ⟨42227769573307256197457591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28151846382204837464971727 42227769573307256197457591)
    ·
      refine ⟨63341654359960884296186387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42227769573307256197457591 63341654359960884296186387)
      ·
        refine ⟨95012481539941326444279581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63341654359960884296186387 95012481539941326444279581)
        ·
          refine ⟨35629680577477997416604843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95012481539941326444279581 35629680577477997416604843)
          ·
            refine ⟨53444520866216996124907265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35629680577477997416604843 53444520866216996124907265)
            ·
              refine ⟨40083390649662747093680449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53444520866216996124907265 40083390649662747093680449)
              ·
                refine ⟨30062542987247060320260337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40083390649662747093680449 30062542987247060320260337)
                ·
                  refine ⟨22546907240435295240195253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30062542987247060320260337 22546907240435295240195253)
                  ·
                    refine ⟨2113772553790808928768305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22546907240435295240195253 2113772553790808928768305)
                    ·
                      refine ⟨1585329415343106696576229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2113772553790808928768305 1585329415343106696576229)
                      ·
                        rfl

theorem cell23_3087418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2].length) (baseStart_3087418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087418 prefixEnd_3087418 := by exact prefixLift 3087418
  have htrace : WordTrace (prefixWord ++ tailWord_3087418) baseStart_3087418 baseEnd_3087418 := by
    simpa [prefixWord, tailWord_3087418, baseEnd_3087418] using wordTrace_append hprefix tailTrace_3087418
  have hstable : (prefixWord ++ tailWord_3087418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087418).length < 2 ^ (prefixWord ++ tailWord_3087418).sum := by decide
  have hdescent : baseEnd_3087418 < baseStart_3087418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087448 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 2, 1, 4]
def baseStart_3087448 : Nat := 118140960795 + 3087448 * 2 ^ 59
def prefixEnd_3087448 : Nat := 4983230072969 + 3 ^ 40 * 3087448 * 2
def baseEnd_3087448 : Nat := 1585344819762741579201091

theorem tailTrace_3087448 : CollatzResearch.WordTrace tailWord_3087448 prefixEnd_3087448 1585344819762741579201091 := by
  unfold tailWord_3087448
  simp only [CollatzResearch.WordTrace]
  refine ⟨56304239859355332491739499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75072319812473776655652665 56304239859355332491739499)
  ·
    refine ⟨84456359789032998737609249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56304239859355332491739499 84456359789032998737609249)
    ·
      refine ⟨63342269841774749053206937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84456359789032998737609249 63342269841774749053206937)
      ·
        refine ⟨47506702381331061789905203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63342269841774749053206937 47506702381331061789905203)
        ·
          refine ⟨71260053571996592684857805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47506702381331061789905203 71260053571996592684857805)
          ·
            refine ⟨26722520089498722256821677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71260053571996592684857805 26722520089498722256821677)
            ·
              refine ⟨10020945033562020846308129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26722520089498722256821677 10020945033562020846308129)
              ·
                refine ⟨7515708775171515634731097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10020945033562020846308129 7515708775171515634731097)
                ·
                  refine ⟨5636781581378636726048323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7515708775171515634731097 5636781581378636726048323)
                  ·
                    refine ⟨8455172372067955089072485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5636781581378636726048323 8455172372067955089072485)
                    ·
                      refine ⟨1585344819762741579201091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8455172372067955089072485 1585344819762741579201091)
                      ·
                        rfl

theorem cell23_3087448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_3087448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087448 prefixEnd_3087448 := by exact prefixLift 3087448
  have htrace : WordTrace (prefixWord ++ tailWord_3087448) baseStart_3087448 baseEnd_3087448 := by
    simpa [prefixWord, tailWord_3087448, baseEnd_3087448] using wordTrace_append hprefix tailTrace_3087448
  have hstable : (prefixWord ++ tailWord_3087448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087448).length < 2 ^ (prefixWord ++ tailWord_3087448).sum := by decide
  have hdescent : baseEnd_3087448 < baseStart_3087448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087468 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 3]
def baseStart_3087468 : Nat := 118140960795 + 3087468 * 2 ^ 59
def prefixEnd_3087468 : Nat := 4983230072969 + 3 ^ 40 * 3087468 * 2
def baseEnd_3087468 : Nat := 1585355089375831500950999

theorem tailTrace_3087468 : CollatzResearch.WordTrace tailWord_3087468 prefixEnd_3087468 1585355089375831500950999 := by
  unfold tailWord_3087468
  simp only [CollatzResearch.WordTrace]
  refine ⟨56304604589319104199603529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75072806119092138932804705 56304604589319104199603529)
  ·
    refine ⟨42228453441989328149702647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56304604589319104199603529 42228453441989328149702647)
    ·
      refine ⟨63342680162983992224553971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42228453441989328149702647 63342680162983992224553971)
      ·
        refine ⟨95014020244475988336830957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63342680162983992224553971 95014020244475988336830957)
        ·
          refine ⟨35630257591678495626311609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95014020244475988336830957 35630257591678495626311609)
          ·
            refine ⟨26722693193758871719733707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35630257591678495626311609 26722693193758871719733707)
            ·
              refine ⟨40084039790638307579600561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26722693193758871719733707 40084039790638307579600561)
              ·
                refine ⟨30063029842978730684700421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40084039790638307579600561 30063029842978730684700421)
                ·
                  refine ⟨5636818095558512003381329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30063029842978730684700421 5636818095558512003381329)
                  ·
                    refine ⟨4227613571668884002535997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5636818095558512003381329 4227613571668884002535997)
                    ·
                      refine ⟨1585355089375831500950999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4227613571668884002535997 1585355089375831500950999)
                      ·
                        rfl

theorem cell23_3087468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_3087468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087468 prefixEnd_3087468 := by exact prefixLift 3087468
  have htrace : WordTrace (prefixWord ++ tailWord_3087468) baseStart_3087468 baseEnd_3087468 := by
    simpa [prefixWord, tailWord_3087468, baseEnd_3087468] using wordTrace_append hprefix tailTrace_3087468
  have hstable : (prefixWord ++ tailWord_3087468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087468).length < 2 ^ (prefixWord ++ tailWord_3087468).sum := by decide
  have hdescent : baseEnd_3087468 < baseStart_3087468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087485 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 2, 2, 3]
def baseStart_3087485 : Nat := 118140960795 + 3087485 * 2 ^ 59
def prefixEnd_3087485 : Nat := 4983230072969 + 3 ^ 40 * 3087485 * 2
def baseEnd_3087485 : Nat := 1585363818546957934438421

theorem tailTrace_3087485 : CollatzResearch.WordTrace tailWord_3087485 prefixEnd_3087485 1585363818546957934438421 := by
  unfold tailWord_3087485
  simp only [CollatzResearch.WordTrace]
  refine ⟨112609829219576620302575909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75073219479717746868383939 112609829219576620302575909)
  ·
    refine ⟨21114342978670616306732983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112609829219576620302575909 21114342978670616306732983)
    ·
      refine ⟨31671514468005924460099475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21114342978670616306732983 31671514468005924460099475)
      ·
        refine ⟨47507271702008886690149213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31671514468005924460099475 47507271702008886690149213)
        ·
          refine ⟨17815226888253332508805955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47507271702008886690149213 17815226888253332508805955)
          ·
            refine ⟨26722840332379998763208933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17815226888253332508805955 26722840332379998763208933)
            ·
              refine ⟨5010532562321249768101675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26722840332379998763208933 5010532562321249768101675)
              ·
                refine ⟨7515798843481874652152513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5010532562321249768101675 7515798843481874652152513)
                ·
                  refine ⟨5636849132611405989114385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7515798843481874652152513 5636849132611405989114385)
                  ·
                    refine ⟨4227636849458554491835789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5636849132611405989114385 4227636849458554491835789)
                    ·
                      refine ⟨1585363818546957934438421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4227636849458554491835789 1585363818546957934438421)
                      ·
                        rfl

theorem cell23_3087485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_3087485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087485 prefixEnd_3087485 := by exact prefixLift 3087485
  have htrace : WordTrace (prefixWord ++ tailWord_3087485) baseStart_3087485 baseEnd_3087485 := by
    simpa [prefixWord, tailWord_3087485, baseEnd_3087485] using wordTrace_append hprefix tailTrace_3087485
  have hstable : (prefixWord ++ tailWord_3087485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087485).length < 2 ^ (prefixWord ++ tailWord_3087485).sum := by decide
  have hdescent : baseEnd_3087485 < baseStart_3087485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087585 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 1, 2, 4]
def baseStart_3087585 : Nat := 118140960795 + 3087585 * 2 ^ 59
def prefixEnd_3087585 : Nat := 4983230072969 + 3 ^ 40 * 3087585 * 2
def baseEnd_3087585 : Nat := 1585415166612407543187961

theorem tailTrace_3087585 : CollatzResearch.WordTrace tailWord_3087585 prefixEnd_3087585 1585415166612407543187961 := by
  unfold tailWord_3087585
  simp only [CollatzResearch.WordTrace]
  refine ⟨112613476519214337381216209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75075651012809558254144139 112613476519214337381216209)
  ·
    refine ⟨84460107389410753035912157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112613476519214337381216209 84460107389410753035912157)
    ·
      refine ⟨31672540271029032388467059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84460107389410753035912157 31672540271029032388467059)
      ·
        refine ⟨47508810406543548582700589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31672540271029032388467059 47508810406543548582700589)
        ·
          refine ⟨17815803902453830718512721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47508810406543548582700589 17815803902453830718512721)
          ·
            refine ⟨13361852926840373038884541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17815803902453830718512721 13361852926840373038884541)
            ·
              refine ⟨5010694847565139889581703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13361852926840373038884541 5010694847565139889581703)
              ·
                refine ⟨7516042271347709834372555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5010694847565139889581703 7516042271347709834372555)
                ·
                  refine ⟨11274063407021564751558833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7516042271347709834372555 11274063407021564751558833)
                  ·
                    refine ⟨8455547555266173563669125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11274063407021564751558833 8455547555266173563669125)
                    ·
                      refine ⟨1585415166612407543187961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8455547555266173563669125 1585415166612407543187961)
                      ·
                        rfl

theorem cell23_3087585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_3087585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087585 prefixEnd_3087585 := by exact prefixLift 3087585
  have htrace : WordTrace (prefixWord ++ tailWord_3087585) baseStart_3087585 baseEnd_3087585 := by
    simpa [prefixWord, tailWord_3087585, baseEnd_3087585] using wordTrace_append hprefix tailTrace_3087585
  have hstable : (prefixWord ++ tailWord_3087585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087585).length < 2 ^ (prefixWord ++ tailWord_3087585).sum := by decide
  have hdescent : baseEnd_3087585 < baseStart_3087585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087592 : List Nat := [2, 1, 4, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_3087592 : Nat := 118140960795 + 3087592 * 2 ^ 59
def prefixEnd_3087592 : Nat := 4983230072969 + 3 ^ 40 * 3087592 * 2
def baseEnd_3087592 : Nat := 1585418760976989015800429

theorem tailTrace_3087592 : CollatzResearch.WordTrace tailWord_3087592 prefixEnd_3087592 1585418760976989015800429 := by
  unfold tailWord_3087592
  simp only [CollatzResearch.WordTrace]
  refine ⟨56306865915094488788360515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75075821220125985051147353 56306865915094488788360515)
  ·
    refine ⟨84460298872641733182540773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56306865915094488788360515 84460298872641733182540773)
    ·
      refine ⟨15836306038620324971726395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84460298872641733182540773 15836306038620324971726395)
      ·
        refine ⟨23754459057930487457589593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15836306038620324971726395 23754459057930487457589593)
        ·
          refine ⟨17815844293447865593192195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23754459057930487457589593 17815844293447865593192195)
          ·
            refine ⟨26723766440171798389788293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17815844293447865593192195 26723766440171798389788293)
            ·
              refine ⟨5010706207532212198085305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26723766440171798389788293 5010706207532212198085305)
              ·
                refine ⟨3758029655649159148563979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5010706207532212198085305 3758029655649159148563979)
                ·
                  refine ⟨5637044483473738722845969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3758029655649159148563979 5637044483473738722845969)
                  ·
                    refine ⟨4227783362605304042134477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5637044483473738722845969 4227783362605304042134477)
                    ·
                      refine ⟨1585418760976989015800429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4227783362605304042134477 1585418760976989015800429)
                      ·
                        rfl

theorem cell23_3087592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_3087592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087592 prefixEnd_3087592 := by exact prefixLift 3087592
  have htrace : WordTrace (prefixWord ++ tailWord_3087592) baseStart_3087592 baseEnd_3087592 := by
    simpa [prefixWord, tailWord_3087592, baseEnd_3087592] using wordTrace_append hprefix tailTrace_3087592
  have hstable : (prefixWord ++ tailWord_3087592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087592).length < 2 ^ (prefixWord ++ tailWord_3087592).sum := by decide
  have hdescent : baseEnd_3087592 < baseStart_3087592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087595 : List Nat := [1, 1, 1, 1, 2, 8, 2, 7]
def baseStart_3087595 : Nat := 118140960795 + 3087595 * 2 ^ 59
def prefixEnd_3087595 : Nat := 4983230072969 + 3 ^ 40 * 3087595 * 2
def baseEnd_3087595 : Nat := 58719270422924166817145

theorem tailTrace_3087595 : CollatzResearch.WordTrace tailWord_3087595 prefixEnd_3087595 58719270422924166817145 := by
  unfold tailWord_3087595
  simp only [CollatzResearch.WordTrace]
  refine ⟨112613841249178109089080239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75075894166118739392720159 112613841249178109089080239)
  ·
    refine ⟨168920761873767163633620359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112613841249178109089080239 168920761873767163633620359)
    ·
      refine ⟨253381142810650745450430539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168920761873767163633620359 253381142810650745450430539)
      ·
        refine ⟨380071714215976118175645809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253381142810650745450430539 380071714215976118175645809)
        ·
          refine ⟨285053785661982088631734357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380071714215976118175645809 285053785661982088631734357)
          ·
            refine ⟨3340474050726352601153137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 285053785661982088631734357 3340474050726352601153137)
            ·
              refine ⟨2505355538044764450864853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3340474050726352601153137 2505355538044764450864853)
              ·
                refine ⟨58719270422924166817145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2505355538044764450864853 58719270422924166817145)
                ·
                  rfl

theorem cell23_3087595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 7].length) (baseStart_3087595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087595 prefixEnd_3087595 := by exact prefixLift 3087595
  have htrace : WordTrace (prefixWord ++ tailWord_3087595) baseStart_3087595 baseEnd_3087595 := by
    simpa [prefixWord, tailWord_3087595, baseEnd_3087595] using wordTrace_append hprefix tailTrace_3087595
  have hstable : (prefixWord ++ tailWord_3087595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087595).length < 2 ^ (prefixWord ++ tailWord_3087595).sum := by decide
  have hdescent : baseEnd_3087595 < baseStart_3087595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087665 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 2, 1, 5]
def baseStart_3087665 : Nat := 118140960795 + 3087665 * 2 ^ 59
def prefixEnd_3087665 : Nat := 4983230072969 + 3 ^ 40 * 3087665 * 2
def baseEnd_3087665 : Nat := 1585456245064767230187593

theorem tailTrace_3087665 : CollatzResearch.WordTrace tailWord_3087665 prefixEnd_3087665 1585456245064767230187593 := by
  unfold tailWord_3087665
  simp only [CollatzResearch.WordTrace]
  refine ⟨112616394358924511044128449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75077596239283007362752299 112616394358924511044128449)
  ·
    refine ⟨84462295769193383283096337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112616394358924511044128449 84462295769193383283096337)
    ·
      refine ⟨63346721826895037462322253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84462295769193383283096337 63346721826895037462322253)
      ·
        refine ⟨23755020685085639048370845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63346721826895037462322253 23755020685085639048370845)
        ·
          refine ⟨8908132756907114643139067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23755020685085639048370845 8908132756907114643139067)
          ·
            refine ⟨13362199135360671964708601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8908132756907114643139067 13362199135360671964708601)
            ·
              refine ⟨10021649351520503973531451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13362199135360671964708601 10021649351520503973531451)
              ·
                refine ⟨15032474027280755960297177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10021649351520503973531451 15032474027280755960297177)
                ·
                  refine ⟨11274355520460566970222883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15032474027280755960297177 11274355520460566970222883)
                  ·
                    refine ⟨16911533280690850455334325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11274355520460566970222883 16911533280690850455334325)
                    ·
                      refine ⟨1585456245064767230187593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16911533280690850455334325 1585456245064767230187593)
                      ·
                        rfl

theorem cell23_3087665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_3087665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087665 prefixEnd_3087665 := by exact prefixLift 3087665
  have htrace : WordTrace (prefixWord ++ tailWord_3087665) baseStart_3087665 baseEnd_3087665 := by
    simpa [prefixWord, tailWord_3087665, baseEnd_3087665] using wordTrace_append hprefix tailTrace_3087665
  have hstable : (prefixWord ++ tailWord_3087665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087665).length < 2 ^ (prefixWord ++ tailWord_3087665).sum := by decide
  have hdescent : baseEnd_3087665 < baseStart_3087665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087666 : List Nat := [3, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2]
def baseStart_3087666 : Nat := 118140960795 + 3087666 * 2 ^ 59
def prefixEnd_3087666 : Nat := 4983230072969 + 3 ^ 40 * 3087666 * 2
def baseEnd_3087666 : Nat := 1585456758545421726275089

theorem tailTrace_3087666 : CollatzResearch.WordTrace tailWord_3087666 prefixEnd_3087666 1585456758545421726275089 := by
  unfold tailWord_3087666
  simp only [CollatzResearch.WordTrace]
  refine ⟨28154107707980222053728713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75077620554613925476609901 28154107707980222053728713)
  ·
    refine ⟨21115580780985166540296535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28154107707980222053728713 21115580780985166540296535)
    ·
      refine ⟨31673371171477749810444803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21115580780985166540296535 31673371171477749810444803)
      ·
        refine ⟨47510056757216624715667205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31673371171477749810444803 47510056757216624715667205)
        ·
          refine ⟨8908135641978117134187601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47510056757216624715667205 8908135641978117134187601)
          ·
            refine ⟨6681101731483587850640701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8908135641978117134187601 6681101731483587850640701)
            ·
              refine ⟨2505413149306345443990263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6681101731483587850640701 2505413149306345443990263)
              ·
                refine ⟨3758119723959518165985395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2505413149306345443990263 3758119723959518165985395)
                ·
                  refine ⟨5637179585939277248978093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3758119723959518165985395 5637179585939277248978093)
                  ·
                    refine ⟨2113942344727228968366785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5637179585939277248978093 2113942344727228968366785)
                    ·
                      refine ⟨1585456758545421726275089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2113942344727228968366785 1585456758545421726275089)
                      ·
                        rfl

theorem cell23_3087666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_3087666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087666 prefixEnd_3087666 := by exact prefixLift 3087666
  have htrace : WordTrace (prefixWord ++ tailWord_3087666) baseStart_3087666 baseEnd_3087666 := by
    simpa [prefixWord, tailWord_3087666, baseEnd_3087666] using wordTrace_append hprefix tailTrace_3087666
  have hstable : (prefixWord ++ tailWord_3087666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087666).length < 2 ^ (prefixWord ++ tailWord_3087666).sum := by decide
  have hdescent : baseEnd_3087666 < baseStart_3087666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087679 : List Nat := [1, 1, 2, 2, 4, 2, 1, 4, 2, 2, 2]
def baseStart_3087679 : Nat := 118140960795 + 3087679 * 2 ^ 59
def prefixEnd_3087679 : Nat := 4983230072969 + 3 ^ 40 * 3087679 * 2
def baseEnd_3087679 : Nat := 1585463433793930175412529

theorem tailTrace_3087679 : CollatzResearch.WordTrace tailWord_3087679 prefixEnd_3087679 1585463433793930175412529 := by
  unfold tailWord_3087679
  simp only [CollatzResearch.WordTrace]
  refine ⟨112616904980873791435138091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75077936653915860956758727 112616904980873791435138091)
  ·
    refine ⟨168925357471310687152707137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112616904980873791435138091 168925357471310687152707137)
    ·
      refine ⟨126694018103483015364530353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168925357471310687152707137 126694018103483015364530353)
      ·
        refine ⟨95020513577612261523397765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126694018103483015364530353 95020513577612261523397765)
        ·
          refine ⟨17816346295802299035637081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95020513577612261523397765 17816346295802299035637081)
          ·
            refine ⟨13362259721851724276727811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17816346295802299035637081 13362259721851724276727811)
            ·
              refine ⟨20043389582777586415091717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13362259721851724276727811 20043389582777586415091717)
              ·
                refine ⟨3758135546770797452829697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20043389582777586415091717 3758135546770797452829697)
                ·
                  refine ⟨2818601660078098089622273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3758135546770797452829697 2818601660078098089622273)
                  ·
                    refine ⟨2113951245058573567216705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2818601660078098089622273 2113951245058573567216705)
                    ·
                      refine ⟨1585463433793930175412529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2113951245058573567216705 1585463433793930175412529)
                      ·
                        rfl

theorem cell23_3087679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 2, 2].length) (baseStart_3087679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087679 prefixEnd_3087679 := by exact prefixLift 3087679
  have htrace : WordTrace (prefixWord ++ tailWord_3087679) baseStart_3087679 baseEnd_3087679 := by
    simpa [prefixWord, tailWord_3087679, baseEnd_3087679] using wordTrace_append hprefix tailTrace_3087679
  have hstable : (prefixWord ++ tailWord_3087679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087679).length < 2 ^ (prefixWord ++ tailWord_3087679).sum := by decide
  have hdescent : baseEnd_3087679 < baseStart_3087679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087688 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_3087688 : Nat := 118140960795 + 3087688 * 2 ^ 59
def prefixEnd_3087688 : Nat := 4983230072969 + 3 ^ 40 * 3087688 * 2
def baseEnd_3087688 : Nat := 1585468055119820640199987

theorem tailTrace_3087688 : CollatzResearch.WordTrace tailWord_3087688 prefixEnd_3087688 1585468055119820640199987 := by
  unfold tailWord_3087688
  simp only [CollatzResearch.WordTrace]
  refine ⟨56308616618920592986107859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75078155491894123981477145 56308616618920592986107859)
  ·
    refine ⟨84462924928380889479161789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56308616618920592986107859 84462924928380889479161789)
    ·
      refine ⟨31673596848142833554685671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84462924928380889479161789 31673596848142833554685671)
      ·
        refine ⟨47510395272214250332028507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31673596848142833554685671 47510395272214250332028507)
        ·
          refine ⟨71265592908321375498042761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47510395272214250332028507 71265592908321375498042761)
          ·
            refine ⟨53449194681241031623532071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71265592908321375498042761 53449194681241031623532071)
            ·
              refine ⟨80173792021861547435298107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53449194681241031623532071 80173792021861547435298107)
              ·
                refine ⟨120260688032792321152947161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80173792021861547435298107 120260688032792321152947161)
                ·
                  refine ⟨90195516024594240864710371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120260688032792321152947161 90195516024594240864710371)
                  ·
                    refine ⟨135293274036891361297065557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90195516024594240864710371 135293274036891361297065557)
                    ·
                      refine ⟨1585468055119820640199987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 135293274036891361297065557 1585468055119820640199987)
                      ·
                        rfl

theorem cell23_3087688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_3087688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087688 prefixEnd_3087688 := by exact prefixLift 3087688
  have htrace : WordTrace (prefixWord ++ tailWord_3087688) baseStart_3087688 baseEnd_3087688 := by
    simpa [prefixWord, tailWord_3087688, baseEnd_3087688] using wordTrace_append hprefix tailTrace_3087688
  have hstable : (prefixWord ++ tailWord_3087688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087688).length < 2 ^ (prefixWord ++ tailWord_3087688).sum := by decide
  have hdescent : baseEnd_3087688 < baseStart_3087688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087715 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 1, 7]
def baseStart_3087715 : Nat := 118140960795 + 3087715 * 2 ^ 59
def prefixEnd_3087715 : Nat := 4983230072969 + 3 ^ 40 * 3087715 * 2
def baseEnd_3087715 : Nat := 528493973032497344854121

theorem tailTrace_3087715 : CollatzResearch.WordTrace tailWord_3087715 prefixEnd_3087715 528493973032497344854121 := by
  unfold tailWord_3087715
  simp only [CollatzResearch.WordTrace]
  refine ⟨112618218008743369583448599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75078812005828913055632399 112618218008743369583448599)
  ·
    refine ⟨168927327013115054375172899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112618218008743369583448599 168927327013115054375172899)
    ·
      refine ⟨253390990519672581562759349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168927327013115054375172899 253390990519672581562759349)
      ·
        refine ⟨23755405361219304521508689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253390990519672581562759349 23755405361219304521508689)
        ·
          refine ⟨17816554020914478391131517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23755405361219304521508689 17816554020914478391131517)
          ·
            refine ⟨6681207757842929396674319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17816554020914478391131517 6681207757842929396674319)
            ·
              refine ⟨10021811636764394095011479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6681207757842929396674319 10021811636764394095011479)
              ·
                refine ⟨15032717455146591142517219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10021811636764394095011479 15032717455146591142517219)
                ·
                  refine ⟨22549076182719886713775829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15032717455146591142517219 22549076182719886713775829)
                  ·
                    refine ⟨528493973032497344854121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22549076182719886713775829 528493973032497344854121)
                    ·
                      rfl

theorem cell23_3087715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 7].length) (baseStart_3087715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087715 prefixEnd_3087715 := by exact prefixLift 3087715
  have htrace : WordTrace (prefixWord ++ tailWord_3087715) baseStart_3087715 baseEnd_3087715 := by
    simpa [prefixWord, tailWord_3087715, baseEnd_3087715] using wordTrace_append hprefix tailTrace_3087715
  have hstable : (prefixWord ++ tailWord_3087715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087715).length < 2 ^ (prefixWord ++ tailWord_3087715).sum := by decide
  have hdescent : baseEnd_3087715 < baseStart_3087715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087719 : List Nat := [1, 1, 5, 1, 4, 1, 2, 3, 5]
def baseStart_3087719 : Nat := 118140960795 + 3087719 * 2 ^ 59
def prefixEnd_3087719 : Nat := 4983230072969 + 3 ^ 40 * 3087719 * 2
def baseEnd_3087719 : Nat := 176164885891123335434705

theorem tailTrace_3087719 : CollatzResearch.WordTrace tailWord_3087719 prefixEnd_3087719 176164885891123335434705 := by
  unfold tailWord_3087719
  simp only [CollatzResearch.WordTrace]
  refine ⟨112618363900728878266594211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75078909267152585511062807 112618363900728878266594211)
  ·
    refine ⟨168927545851093317399891317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112618363900728878266594211 168927545851093317399891317)
    ·
      refine ⟨15836957423539998506239811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168927545851093317399891317 15836957423539998506239811)
      ·
        refine ⟨23755436135309997759359717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15836957423539998506239811 23755436135309997759359717)
        ·
          refine ⟨4454144275370624579879947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23755436135309997759359717 4454144275370624579879947)
          ·
            refine ⟨6681216413055936869819921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4454144275370624579879947 6681216413055936869819921)
            ·
              refine ⟨5010912309791952652364941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6681216413055936869819921 5010912309791952652364941)
              ·
                refine ⟨1879092116171982244636853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5010912309791952652364941 1879092116171982244636853)
                ·
                  refine ⟨176164885891123335434705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1879092116171982244636853 176164885891123335434705)
                  ·
                    rfl

theorem cell23_3087719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 5].length) (baseStart_3087719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087719 prefixEnd_3087719 := by exact prefixLift 3087719
  have htrace : WordTrace (prefixWord ++ tailWord_3087719) baseStart_3087719 baseEnd_3087719 := by
    simpa [prefixWord, tailWord_3087719, baseEnd_3087719] using wordTrace_append hprefix tailTrace_3087719
  have hstable : (prefixWord ++ tailWord_3087719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087719).length < 2 ^ (prefixWord ++ tailWord_3087719).sum := by decide
  have hdescent : baseEnd_3087719 < baseStart_3087719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087735 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 4]
def baseStart_3087735 : Nat := 118140960795 + 3087735 * 2 ^ 59
def prefixEnd_3087735 : Nat := 4983230072969 + 3 ^ 40 * 3087735 * 2
def baseEnd_3087735 : Nat := 1585492188710581956312271

theorem tailTrace_3087735 : CollatzResearch.WordTrace tailWord_3087735 prefixEnd_3087735 1585492188710581956312271 := by
  unfold tailWord_3087735
  simp only [CollatzResearch.WordTrace]
  refine ⟨112618947468670912999176659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75079298312447275332784439 112618947468670912999176659)
  ·
    refine ⟨168928421203006369498764989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112618947468670912999176659 168928421203006369498764989)
    ·
      refine ⟨63348157951127388562036871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168928421203006369498764989 63348157951127388562036871)
      ·
        refine ⟨95022236926691082843055307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63348157951127388562036871 95022236926691082843055307)
        ·
          refine ⟨142533355390036624264582961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95022236926691082843055307 142533355390036624264582961)
          ·
            refine ⟨106900016542527468198437221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142533355390036624264582961 106900016542527468198437221)
            ·
              refine ⟨20043753101723900287206979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106900016542527468198437221 20043753101723900287206979)
              ·
                refine ⟨30065629652585850430810469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20043753101723900287206979 30065629652585850430810469)
                ·
                  refine ⟨5637305559859846955776963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30065629652585850430810469 5637305559859846955776963)
                  ·
                    refine ⟨8455958339789770433665445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5637305559859846955776963 8455958339789770433665445)
                    ·
                      refine ⟨1585492188710581956312271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8455958339789770433665445 1585492188710581956312271)
                      ·
                        rfl

theorem cell23_3087735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_3087735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087735 prefixEnd_3087735 := by exact prefixLift 3087735
  have htrace : WordTrace (prefixWord ++ tailWord_3087735) baseStart_3087735 baseEnd_3087735 := by
    simpa [prefixWord, tailWord_3087735, baseEnd_3087735] using wordTrace_append hprefix tailTrace_3087735
  have hstable : (prefixWord ++ tailWord_3087735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087735).length < 2 ^ (prefixWord ++ tailWord_3087735).sum := by decide
  have hdescent : baseEnd_3087735 < baseStart_3087735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087755 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 3]
def baseStart_3087755 : Nat := 118140960795 + 3087755 * 2 ^ 59
def prefixEnd_3087755 : Nat := 4983230072969 + 3 ^ 40 * 3087755 * 2
def baseEnd_3087755 : Nat := 1585502458323671878062179

theorem tailTrace_3087755 : CollatzResearch.WordTrace tailWord_3087755 prefixEnd_3087755 1585502458323671878062179 := by
  unfold tailWord_3087755
  simp only [CollatzResearch.WordTrace]
  refine ⟨112619676928598456414904719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75079784619065637609936479 112619676928598456414904719)
  ·
    refine ⟨168929515392897684622357079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112619676928598456414904719 168929515392897684622357079)
    ·
      refine ⟨253394273089346526933535619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168929515392897684622357079 253394273089346526933535619)
      ·
        refine ⟨380091409634019790400303429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253394273089346526933535619 380091409634019790400303429)
        ·
          refine ⟨71267139306378710700056893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 380091409634019790400303429 71267139306378710700056893)
          ·
            refine ⟨26725177239892016512521335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71267139306378710700056893 26725177239892016512521335)
            ·
              refine ⟨40087765859838024768782003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26725177239892016512521335 40087765859838024768782003)
              ·
                refine ⟨60131648789757037153173005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40087765859838024768782003 60131648789757037153173005)
                ·
                  refine ⟨22549368296158888932439877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60131648789757037153173005 22549368296158888932439877)
                  ·
                    refine ⟨4228006555529791674832477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22549368296158888932439877 4228006555529791674832477)
                    ·
                      refine ⟨1585502458323671878062179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4228006555529791674832477 1585502458323671878062179)
                      ·
                        rfl

theorem cell23_3087755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 3].length) (baseStart_3087755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087755 prefixEnd_3087755 := by exact prefixLift 3087755
  have htrace : WordTrace (prefixWord ++ tailWord_3087755) baseStart_3087755 baseEnd_3087755 := by
    simpa [prefixWord, tailWord_3087755, baseEnd_3087755] using wordTrace_append hprefix tailTrace_3087755
  have hstable : (prefixWord ++ tailWord_3087755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087755).length < 2 ^ (prefixWord ++ tailWord_3087755).sum := by decide
  have hdescent : baseEnd_3087755 < baseStart_3087755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087775 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 8]
def baseStart_3087775 : Nat := 118140960795 + 3087775 * 2 ^ 59
def prefixEnd_3087775 : Nat := 4983230072969 + 3 ^ 40 * 3087775 * 2
def baseEnd_3087775 : Nat := 176168080881862422201343

theorem tailTrace_3087775 : CollatzResearch.WordTrace tailWord_3087775 prefixEnd_3087775 176168080881862422201343 := by
  unfold tailWord_3087775
  simp only [CollatzResearch.WordTrace]
  refine ⟨112620406388525999830632779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75080270925683999887088519 112620406388525999830632779)
  ·
    refine ⟨168930609582788999745949169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112620406388525999830632779 168930609582788999745949169)
    ·
      refine ⟨126697957187091749809461877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168930609582788999745949169 126697957187091749809461877)
      ·
        refine ⟨11877933486289851544637051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126697957187091749809461877 11877933486289851544637051)
        ·
          refine ⟨17816900229434777316955577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11877933486289851544637051 17816900229434777316955577)
          ·
            refine ⟨13362675172076082987716683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17816900229434777316955577 13362675172076082987716683)
            ·
              refine ⟨20044012758114124481575025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13362675172076082987716683 20044012758114124481575025)
              ·
                refine ⟨15033009568585593361181269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20044012758114124481575025 15033009568585593361181269)
                ·
                  refine ⟨176168080881862422201343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15033009568585593361181269 176168080881862422201343)
                  ·
                    rfl

theorem cell23_3087775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 8].length) (baseStart_3087775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087775 prefixEnd_3087775 := by exact prefixLift 3087775
  have htrace : WordTrace (prefixWord ++ tailWord_3087775) baseStart_3087775 baseEnd_3087775 := by
    simpa [prefixWord, tailWord_3087775, baseEnd_3087775] using wordTrace_append hprefix tailTrace_3087775
  have hstable : (prefixWord ++ tailWord_3087775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087775).length < 2 ^ (prefixWord ++ tailWord_3087775).sum := by decide
  have hdescent : baseEnd_3087775 < baseStart_3087775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087789 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3087789 : Nat := 118140960795 + 3087789 * 2 ^ 59
def prefixEnd_3087789 : Nat := 4983230072969 + 3 ^ 40 * 3087789 * 2
def baseEnd_3087789 : Nat := 1585519916665924745037023

theorem tailTrace_3087789 : CollatzResearch.WordTrace tailWord_3087789 prefixEnd_3087789 1585519916665924745037023 := by
  unfold tailWord_3087789
  simp only [CollatzResearch.WordTrace]
  refine ⟨112620917010475280221642421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75080611340316853481094947 112620917010475280221642421)
  ·
    refine ⟨10558210969732057520778977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112620917010475280221642421 10558210969732057520778977)
    ·
      refine ⟨7918658227299043140584233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10558210969732057520778977 7918658227299043140584233)
      ·
        refine ⟨5938993670474282355438175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7918658227299043140584233 5938993670474282355438175)
        ·
          refine ⟨8908490505711423533157263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5938993670474282355438175 8908490505711423533157263)
          ·
            refine ⟨13362735758567135299735895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8908490505711423533157263 13362735758567135299735895)
            ·
              refine ⟨20044103637850702949603843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13362735758567135299735895 20044103637850702949603843)
              ·
                refine ⟨30066155456776054424405765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20044103637850702949603843 30066155456776054424405765)
                ·
                  refine ⟨5637404148145510204576081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30066155456776054424405765 5637404148145510204576081)
                  ·
                    refine ⟨4228053111109132653432061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5637404148145510204576081 4228053111109132653432061)
                    ·
                      refine ⟨1585519916665924745037023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4228053111109132653432061 1585519916665924745037023)
                      ·
                        rfl

theorem cell23_3087789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3087789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087789 prefixEnd_3087789 := by exact prefixLift 3087789
  have htrace : WordTrace (prefixWord ++ tailWord_3087789) baseStart_3087789 baseEnd_3087789 := by
    simpa [prefixWord, tailWord_3087789, baseEnd_3087789] using wordTrace_append hprefix tailTrace_3087789
  have hstable : (prefixWord ++ tailWord_3087789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087789).length < 2 ^ (prefixWord ++ tailWord_3087789).sum := by decide
  have hdescent : baseEnd_3087789 < baseStart_3087789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087839 : List Nat := [1, 1, 2, 3, 3, 1, 5, 1, 1, 5]
def baseStart_3087839 : Nat := 118140960795 + 3087839 * 2 ^ 59
def prefixEnd_3087839 : Nat := 4983230072969 + 3 ^ 40 * 3087839 * 2
def baseEnd_3087839 : Nat := 528515196899549849803931

theorem tailTrace_3087839 : CollatzResearch.WordTrace tailWord_3087839 prefixEnd_3087839 528515196899549849803931 := by
  unfold tailWord_3087839
  simp only [CollatzResearch.WordTrace]
  refine ⟨112622740660294138760962571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75081827106862759173975047 112622740660294138760962571)
  ·
    refine ⟨168934110990441208141443857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112622740660294138760962571 168934110990441208141443857)
    ·
      refine ⟨126700583242830906106082893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168934110990441208141443857 126700583242830906106082893)
      ·
        refine ⟨47512718716061589789781085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126700583242830906106082893 47512718716061589789781085)
        ·
          refine ⟨17817269518523096171167907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47512718716061589789781085 17817269518523096171167907)
          ·
            refine ⟨26725904277784644256751861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17817269518523096171167907 26725904277784644256751861)
            ·
              refine ⟨2505553526042310399070487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26725904277784644256751861 2505553526042310399070487)
              ·
                refine ⟨3758330289063465598605731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2505553526042310399070487 3758330289063465598605731)
                ·
                  refine ⟨5637495433595198397908597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3758330289063465598605731 5637495433595198397908597)
                  ·
                    refine ⟨528515196899549849803931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5637495433595198397908597 528515196899549849803931)
                    ·
                      rfl

theorem cell23_3087839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 1, 5].length) (baseStart_3087839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087839 prefixEnd_3087839 := by exact prefixLift 3087839
  have htrace : WordTrace (prefixWord ++ tailWord_3087839) baseStart_3087839 baseEnd_3087839 := by
    simpa [prefixWord, tailWord_3087839, baseEnd_3087839] using wordTrace_append hprefix tailTrace_3087839
  have hstable : (prefixWord ++ tailWord_3087839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087839).length < 2 ^ (prefixWord ++ tailWord_3087839).sum := by decide
  have hdescent : baseEnd_3087839 < baseStart_3087839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087855 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 6]
def baseStart_3087855 : Nat := 118140960795 + 3087855 * 2 ^ 59
def prefixEnd_3087855 : Nat := 4983230072969 + 3 ^ 40 * 3087855 * 2
def baseEnd_3087855 : Nat := 1585553806389121486811719

theorem tailTrace_3087855 : CollatzResearch.WordTrace tailWord_3087855 prefixEnd_3087855 1585553806389121486811719 := by
  unfold tailWord_3087855
  simp only [CollatzResearch.WordTrace]
  refine ⟨112623324228236173493545019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75082216152157448995696679 112623324228236173493545019)
  ·
    refine ⟨168934986342354260240317529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112623324228236173493545019 168934986342354260240317529)
    ·
      refine ⟨126701239756765695180238147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168934986342354260240317529 126701239756765695180238147)
      ·
        refine ⟨190051859635148542770357221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126701239756765695180238147 190051859635148542770357221)
        ·
          refine ⟨35634723681590351769441979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190051859635148542770357221 35634723681590351769441979)
          ·
            refine ⟨53452085522385527654162969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35634723681590351769441979 53452085522385527654162969)
            ·
              refine ⟨40089064141789145740622227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53452085522385527654162969 40089064141789145740622227)
              ·
                refine ⟨60133596212683718610933341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40089064141789145740622227 60133596212683718610933341)
                ·
                  refine ⟨22550098579756394479100003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60133596212683718610933341 22550098579756394479100003)
                  ·
                    refine ⟨33825147869634591718650005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22550098579756394479100003 33825147869634591718650005)
                    ·
                      refine ⟨1585553806389121486811719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33825147869634591718650005 1585553806389121486811719)
                      ·
                        rfl

theorem cell23_3087855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_3087855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087855 prefixEnd_3087855 := by exact prefixLift 3087855
  have htrace : WordTrace (prefixWord ++ tailWord_3087855) baseStart_3087855 baseEnd_3087855 := by
    simpa [prefixWord, tailWord_3087855, baseEnd_3087855] using wordTrace_append hprefix tailTrace_3087855
  have hstable : (prefixWord ++ tailWord_3087855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087855).length < 2 ^ (prefixWord ++ tailWord_3087855).sum := by decide
  have hdescent : baseEnd_3087855 < baseStart_3087855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087869 : List Nat := [1, 4, 1, 1, 1, 4, 2, 3, 2, 4]
def baseStart_3087869 : Nat := 118140960795 + 3087869 * 2 ^ 59
def prefixEnd_3087869 : Nat := 4983230072969 + 3 ^ 40 * 3087869 * 2
def baseEnd_3087869 : Nat := 528520331706094810678885

theorem tailTrace_3087869 : CollatzResearch.WordTrace tailWord_3087869 prefixEnd_3087869 528520331706094810678885 := by
  unfold tailWord_3087869
  simp only [CollatzResearch.WordTrace]
  refine ⟨112623834850185453884554661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75082556566790302589703107 112623834850185453884554661)
  ·
    refine ⟨21116969034409772603353999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112623834850185453884554661 21116969034409772603353999)
    ·
      refine ⟨31675453551614658905030999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21116969034409772603353999 31675453551614658905030999)
      ·
        refine ⟨47513180327421988357546499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31675453551614658905030999 47513180327421988357546499)
        ·
          refine ⟨71269770491132982536319749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47513180327421988357546499 71269770491132982536319749)
          ·
            refine ⟨13363081967087434225559953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71269770491132982536319749 13363081967087434225559953)
            ·
              refine ⟨10022311475315575669169965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13363081967087434225559953 10022311475315575669169965)
              ·
                refine ⟨3758366803243340875938737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10022311475315575669169965 3758366803243340875938737)
                ·
                  refine ⟨2818775102432505656954053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3758366803243340875938737 2818775102432505656954053)
                  ·
                    refine ⟨528520331706094810678885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2818775102432505656954053 528520331706094810678885)
                    ·
                      rfl

theorem cell23_3087869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_3087869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087869 prefixEnd_3087869 := by exact prefixLift 3087869
  have htrace : WordTrace (prefixWord ++ tailWord_3087869) baseStart_3087869 baseEnd_3087869 := by
    simpa [prefixWord, tailWord_3087869, baseEnd_3087869] using wordTrace_append hprefix tailTrace_3087869
  have hstable : (prefixWord ++ tailWord_3087869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087869).length < 2 ^ (prefixWord ++ tailWord_3087869).sum := by decide
  have hdescent : baseEnd_3087869 < baseStart_3087869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087879 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 3]
def baseStart_3087879 : Nat := 118140960795 + 3087879 * 2 ^ 59
def prefixEnd_3087879 : Nat := 4983230072969 + 3 ^ 40 * 3087879 * 2
def baseEnd_3087879 : Nat := 1585566129924829392911609

theorem tailTrace_3087879 : CollatzResearch.WordTrace tailWord_3087879 prefixEnd_3087879 1585566129924829392911609 := by
  unfold tailWord_3087879
  simp only [CollatzResearch.WordTrace]
  refine ⟨112624199580149225592418691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75082799720099483728279127 112624199580149225592418691)
  ·
    refine ⟨168936299370223838388628037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112624199580149225592418691 168936299370223838388628037)
    ·
      refine ⟨31675556131916969697867757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168936299370223838388628037 31675556131916969697867757)
      ·
        refine ⟨11878333549468863636700409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31675556131916969697867757 11878333549468863636700409)
        ·
          refine ⟨8908750162101647727525307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11878333549468863636700409 8908750162101647727525307)
          ·
            refine ⟨13363125243152471591287961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8908750162101647727525307 13363125243152471591287961)
            ·
              refine ⟨10022343932364353693465971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13363125243152471591287961 10022343932364353693465971)
              ·
                refine ⟨15033515898546530540198957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10022343932364353693465971 15033515898546530540198957)
                ·
                  refine ⟨5637568461954948952574609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15033515898546530540198957 5637568461954948952574609)
                  ·
                    refine ⟨4228176346466211714430957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5637568461954948952574609 4228176346466211714430957)
                    ·
                      refine ⟨1585566129924829392911609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4228176346466211714430957 1585566129924829392911609)
                      ·
                        rfl

theorem cell23_3087879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_3087879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087879 prefixEnd_3087879 := by exact prefixLift 3087879
  have htrace : WordTrace (prefixWord ++ tailWord_3087879) baseStart_3087879 baseEnd_3087879 := by
    simpa [prefixWord, tailWord_3087879, baseEnd_3087879] using wordTrace_append hprefix tailTrace_3087879
  have hstable : (prefixWord ++ tailWord_3087879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087879).length < 2 ^ (prefixWord ++ tailWord_3087879).sum := by decide
  have hdescent : baseEnd_3087879 < baseStart_3087879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087893 : List Nat := [1, 3, 2, 1, 3, 2, 1, 5, 1, 2, 2]
def baseStart_3087893 : Nat := 118140960795 + 3087893 * 2 ^ 59
def prefixEnd_3087893 : Nat := 4983230072969 + 3 ^ 40 * 3087893 * 2
def baseEnd_3087893 : Nat := 1585573318653992338136545

theorem tailTrace_3087893 : CollatzResearch.WordTrace tailWord_3087893 prefixEnd_3087893 1585573318653992338136545 := by
  unfold tailWord_3087893
  simp only [CollatzResearch.WordTrace]
  refine ⟨112624710202098505983428333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75083140134732337322285555 112624710202098505983428333)
  ·
    refine ⟨42234266325786939743785625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112624710202098505983428333 42234266325786939743785625)
    ·
      refine ⟨31675699744340204807839219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42234266325786939743785625 31675699744340204807839219)
      ·
        refine ⟨47513549616510307211758829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31675699744340204807839219 47513549616510307211758829)
        ·
          refine ⟨17817581106191365204409561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47513549616510307211758829 17817581106191365204409561)
          ·
            refine ⟨13363185829643523903307171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17817581106191365204409561 13363185829643523903307171)
            ·
              refine ⟨20044778744465285854960757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13363185829643523903307171 20044778744465285854960757)
              ·
                refine ⟨1879198007293620548902571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20044778744465285854960757 1879198007293620548902571)
                ·
                  refine ⟨2818797010940430823353857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879198007293620548902571 2818797010940430823353857)
                  ·
                    refine ⟨2114097758205323117515393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2818797010940430823353857 2114097758205323117515393)
                    ·
                      refine ⟨1585573318653992338136545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2114097758205323117515393 1585573318653992338136545)
                      ·
                        rfl

theorem cell23_3087893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_3087893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087893 prefixEnd_3087893 := by exact prefixLift 3087893
  have htrace : WordTrace (prefixWord ++ tailWord_3087893) baseStart_3087893 baseEnd_3087893 := by
    simpa [prefixWord, tailWord_3087893, baseEnd_3087893] using wordTrace_append hprefix tailTrace_3087893
  have hstable : (prefixWord ++ tailWord_3087893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087893).length < 2 ^ (prefixWord ++ tailWord_3087893).sum := by decide
  have hdescent : baseEnd_3087893 < baseStart_3087893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087896 : List Nat := [2, 1, 2, 3, 4, 1, 1, 3, 1, 2, 3]
def baseStart_3087896 : Nat := 118140960795 + 3087896 * 2 ^ 59
def prefixEnd_3087896 : Nat := 4983230072969 + 3 ^ 40 * 3087896 * 2
def baseEnd_3087896 : Nat := 1585574859095955826399031

theorem tailTrace_3087896 : CollatzResearch.WordTrace tailWord_3087896 prefixEnd_3087896 1585574859095955826399031 := by
  unfold tailWord_3087896
  simp only [CollatzResearch.WordTrace]
  refine ⟨56312409810543818747893771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75083213080725091663858361 56312409810543818747893771)
  ·
    refine ⟨84468614715815728121840657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56312409810543818747893771 84468614715815728121840657)
    ·
      refine ⟨63351461036861796091380493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84468614715815728121840657 63351461036861796091380493)
      ·
        refine ⟨23756797888823173534267685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63351461036861796091380493 23756797888823173534267685)
        ·
          refine ⟨4454399604154345037675191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23756797888823173534267685 4454399604154345037675191)
          ·
            refine ⟨6681599406231517556512787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4454399604154345037675191 6681599406231517556512787)
            ·
              refine ⟨10022399109347276334769181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6681599406231517556512787 10022399109347276334769181)
              ·
                refine ⟨3758399666005228625538443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10022399109347276334769181 3758399666005228625538443)
                ·
                  refine ⟨5637599499007842938307665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3758399666005228625538443 5637599499007842938307665)
                  ·
                    refine ⟨4228199624255882203730749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5637599499007842938307665 4228199624255882203730749)
                    ·
                      refine ⟨1585574859095955826399031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4228199624255882203730749 1585574859095955826399031)
                      ·
                        rfl

theorem cell23_3087896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_3087896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087896 prefixEnd_3087896 := by exact prefixLift 3087896
  have htrace : WordTrace (prefixWord ++ tailWord_3087896) baseStart_3087896 baseEnd_3087896 := by
    simpa [prefixWord, tailWord_3087896, baseEnd_3087896] using wordTrace_append hprefix tailTrace_3087896
  have hstable : (prefixWord ++ tailWord_3087896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087896).length < 2 ^ (prefixWord ++ tailWord_3087896).sum := by decide
  have hdescent : baseEnd_3087896 < baseStart_3087896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087952 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 5]
def baseStart_3087952 : Nat := 118140960795 + 3087952 * 2 ^ 59
def prefixEnd_3087952 : Nat := 4983230072969 + 3 ^ 40 * 3087952 * 2
def baseEnd_3087952 : Nat := 1585603614012607607298773

theorem tailTrace_3087952 : CollatzResearch.WordTrace tailWord_3087952 prefixEnd_3087952 1585603614012607607298773 := by
  unfold tailWord_3087952
  simp only [CollatzResearch.WordTrace]
  refine ⟨56313431054442379529913055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75084574739256506039884073 56313431054442379529913055)
  ·
    refine ⟨84470146581663569294869583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56313431054442379529913055 84470146581663569294869583)
    ·
      refine ⟨126705219872495353942304375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84470146581663569294869583 126705219872495353942304375)
      ·
        refine ⟨190057829808743030913456563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126705219872495353942304375 190057829808743030913456563)
        ·
          refine ⟨285086744713114546370184845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190057829808743030913456563 285086744713114546370184845)
          ·
            refine ⟨106907529267417954888819317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285086744713114546370184845 106907529267417954888819317)
            ·
              refine ⟨10022580868820433270826811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106907529267417954888819317 10022580868820433270826811)
              ·
                refine ⟨15033871303230649906240217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10022580868820433270826811 15033871303230649906240217)
                ·
                  refine ⟨11275403477422987429680163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15033871303230649906240217 11275403477422987429680163)
                  ·
                    refine ⟨16913105216134481144520245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11275403477422987429680163 16913105216134481144520245)
                    ·
                      refine ⟨1585603614012607607298773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16913105216134481144520245 1585603614012607607298773)
                      ·
                        rfl

theorem cell23_3087952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_3087952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087952 prefixEnd_3087952 := by exact prefixLift 3087952
  have htrace : WordTrace (prefixWord ++ tailWord_3087952) baseStart_3087952 baseEnd_3087952 := by
    simpa [prefixWord, tailWord_3087952, baseEnd_3087952] using wordTrace_append hprefix tailTrace_3087952
  have hstable : (prefixWord ++ tailWord_3087952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087952).length < 2 ^ (prefixWord ++ tailWord_3087952).sum := by decide
  have hdescent : baseEnd_3087952 < baseStart_3087952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087962 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4]
def baseStart_3087962 : Nat := 118140960795 + 3087962 * 2 ^ 59
def prefixEnd_3087962 : Nat := 4983230072969 + 3 ^ 40 * 3087962 * 2
def baseEnd_3087962 : Nat := 1585608748819152568173727

theorem tailTrace_3087962 : CollatzResearch.WordTrace tailWord_3087962 prefixEnd_3087962 1585608748819152568173727 := by
  unfold tailWord_3087962
  simp only [CollatzResearch.WordTrace]
  refine ⟨28156806709712132691922535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75084817892565687178460093 28156806709712132691922535)
  ·
    refine ⟨42235210064568199037883803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28156806709712132691922535 42235210064568199037883803)
    ·
      refine ⟨63352815096852298556825705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42235210064568199037883803 63352815096852298556825705)
      ·
        refine ⟨47514611322639223917619279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63352815096852298556825705 47514611322639223917619279)
        ·
          refine ⟨71271916983958835876428919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47514611322639223917619279 71271916983958835876428919)
          ·
            refine ⟨106907875475938253814643379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71271916983958835876428919 106907875475938253814643379)
            ·
              refine ⟨160361813213907380721965069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106907875475938253814643379 160361813213907380721965069)
              ·
                refine ⟨60135679955215267770736901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160361813213907380721965069 60135679955215267770736901)
                ·
                  refine ⟨11275439991602862707013169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60135679955215267770736901 11275439991602862707013169)
                  ·
                    refine ⟨8456579993702147030259877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11275439991602862707013169 8456579993702147030259877)
                    ·
                      refine ⟨1585608748819152568173727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8456579993702147030259877 1585608748819152568173727)
                      ·
                        rfl

theorem cell23_3087962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_3087962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3087962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3087962 prefixEnd_3087962 := by exact prefixLift 3087962
  have htrace : WordTrace (prefixWord ++ tailWord_3087962) baseStart_3087962 baseEnd_3087962 := by
    simpa [prefixWord, tailWord_3087962, baseEnd_3087962] using wordTrace_append hprefix tailTrace_3087962
  have hstable : (prefixWord ++ tailWord_3087962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087962).length < 2 ^ (prefixWord ++ tailWord_3087962).sum := by decide
  have hdescent : baseEnd_3087962 < baseStart_3087962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088012 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_3088012 : Nat := 118140960795 + 3088012 * 2 ^ 59
def prefixEnd_3088012 : Nat := 4983230072969 + 3 ^ 40 * 3088012 * 2
def baseEnd_3088012 : Nat := 1585634422851877372548497

theorem tailTrace_3088012 : CollatzResearch.WordTrace tailWord_3088012 prefixEnd_3088012 1585634422851877372548497 := by
  unfold tailWord_3088012
  simp only [CollatzResearch.WordTrace]
  refine ⟨56314525244333694653505145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75086033659111592871340193 56314525244333694653505145)
  ·
    refine ⟨42235893933250270990128859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56314525244333694653505145 42235893933250270990128859)
    ·
      refine ⟨63353840899875406485193289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42235893933250270990128859 63353840899875406485193289)
      ·
        refine ⟨47515380674906554863894967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63353840899875406485193289 47515380674906554863894967)
        ·
          refine ⟨71273071012359832295842451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47515380674906554863894967 71273071012359832295842451)
          ·
            refine ⟨106909606518539748443763677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71273071012359832295842451 106909606518539748443763677)
            ·
              refine ⟨40091102444452405666411379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106909606518539748443763677 40091102444452405666411379)
              ·
                refine ⟨60136653666678608499617069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40091102444452405666411379 60136653666678608499617069)
                ·
                  refine ⟨22551245125004478187356401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60136653666678608499617069 22551245125004478187356401)
                  ·
                    refine ⟨16913433843753358640517301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22551245125004478187356401 16913433843753358640517301)
                    ·
                      refine ⟨1585634422851877372548497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16913433843753358640517301 1585634422851877372548497)
                      ·
                        rfl

theorem cell23_3088012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_3088012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088012 prefixEnd_3088012 := by exact prefixLift 3088012
  have htrace : WordTrace (prefixWord ++ tailWord_3088012) baseStart_3088012 baseEnd_3088012 := by
    simpa [prefixWord, tailWord_3088012, baseEnd_3088012] using wordTrace_append hprefix tailTrace_3088012
  have hstable : (prefixWord ++ tailWord_3088012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088012).length < 2 ^ (prefixWord ++ tailWord_3088012).sum := by decide
  have hdescent : baseEnd_3088012 < baseStart_3088012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088023 : List Nat := [1, 1, 3, 3, 2, 4, 2, 2, 5]
def baseStart_3088023 : Nat := 118140960795 + 3088023 * 2 ^ 59
def prefixEnd_3088023 : Nat := 4983230072969 + 3 ^ 40 * 3088023 * 2
def baseEnd_3088023 : Nat := 176182230126564092167883

theorem tailTrace_3088023 : CollatzResearch.WordTrace tailWord_3088023 prefixEnd_3088023 176182230126564092167883 := by
  unfold tailWord_3088023
  simp only [CollatzResearch.WordTrace]
  refine ⟨112629451691627538185660723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75086301127751692123773815 112629451691627538185660723)
  ·
    refine ⟨168944177537441307278491085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112629451691627538185660723 168944177537441307278491085)
    ·
      refine ⟨63354066576540490229434157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168944177537441307278491085 63354066576540490229434157)
      ·
        refine ⟨23757774966202683836037809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63354066576540490229434157 23757774966202683836037809)
        ·
          refine ⟨17818331224652012877028357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23757774966202683836037809 17818331224652012877028357)
          ·
            refine ⟨3340937104622252414442817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17818331224652012877028357 3340937104622252414442817)
            ·
              refine ⟨2505702828466689310832113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3340937104622252414442817 2505702828466689310832113)
              ·
                refine ⟨1879277121350016983124085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2505702828466689310832113 1879277121350016983124085)
                ·
                  refine ⟨176182230126564092167883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1879277121350016983124085 176182230126564092167883)
                  ·
                    rfl

theorem cell23_3088023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 5].length) (baseStart_3088023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088023 prefixEnd_3088023 := by exact prefixLift 3088023
  have htrace : WordTrace (prefixWord ++ tailWord_3088023) baseStart_3088023 baseEnd_3088023 := by
    simpa [prefixWord, tailWord_3088023, baseEnd_3088023] using wordTrace_append hprefix tailTrace_3088023
  have hstable : (prefixWord ++ tailWord_3088023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088023).length < 2 ^ (prefixWord ++ tailWord_3088023).sum := by decide
  have hdescent : baseEnd_3088023 < baseStart_3088023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088053 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 2, 5]
def baseStart_3088053 : Nat := 118140960795 + 3088053 * 2 ^ 59
def prefixEnd_3088053 : Nat := 4983230072969 + 3 ^ 40 * 3088053 * 2
def baseEnd_3088053 : Nat := 528551825186237237378603

theorem tailTrace_3088053 : CollatzResearch.WordTrace tailWord_3088053 prefixEnd_3088053 528551825186237237378603 := by
  unfold tailWord_3088053
  simp only [CollatzResearch.WordTrace]
  refine ⟨112630545881518853309252813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75087030587679235539501875 112630545881518853309252813)
  ·
    refine ⟨42236454705569569990969805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112630545881518853309252813 42236454705569569990969805)
    ·
      refine ⟨15838670514588588746613677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42236454705569569990969805 15838670514588588746613677)
      ·
        refine ⟨5939501442970720779980129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15838670514588588746613677 5939501442970720779980129)
        ·
          refine ⟨4454626082228040584985097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5939501442970720779980129 4454626082228040584985097)
          ·
            refine ⟨3340969561671030438738823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4454626082228040584985097 3340969561671030438738823)
            ·
              refine ⟨5011454342506545658108235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3340969561671030438738823 5011454342506545658108235)
              ·
                refine ⟨7517181513759818487162353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5011454342506545658108235 7517181513759818487162353)
                ·
                  refine ⟨5637886135319863865371765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7517181513759818487162353 5637886135319863865371765)
                  ·
                    refine ⟨528551825186237237378603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5637886135319863865371765 528551825186237237378603)
                    ·
                      rfl

theorem cell23_3088053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_3088053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088053 prefixEnd_3088053 := by exact prefixLift 3088053
  have htrace : WordTrace (prefixWord ++ tailWord_3088053) baseStart_3088053 baseEnd_3088053 := by
    simpa [prefixWord, tailWord_3088053, baseEnd_3088053] using wordTrace_append hprefix tailTrace_3088053
  have hstable : (prefixWord ++ tailWord_3088053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088053).length < 2 ^ (prefixWord ++ tailWord_3088053).sum := by decide
  have hdescent : baseEnd_3088053 < baseStart_3088053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088123 : List Nat := [1, 1, 1, 1, 1, 3, 1, 9, 1, 1, 3]
def baseStart_3088123 : Nat := 118140960795 + 3088123 * 2 ^ 59
def prefixEnd_3088123 : Nat := 4983230072969 + 3 ^ 40 * 3088123 * 2
def baseEnd_3088123 : Nat := 1585691419204526438260487

theorem tailTrace_3088123 : CollatzResearch.WordTrace tailWord_3088123 prefixEnd_3088123 1585691419204526438260487 := by
  unfold tailWord_3088123
  simp only [CollatzResearch.WordTrace]
  refine ⟨112633098991265255264301023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75088732660843503509534015 112633098991265255264301023)
  ·
    refine ⟨168949648486897882896451535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112633098991265255264301023 168949648486897882896451535)
    ·
      refine ⟨253424472730346824344677303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168949648486897882896451535 253424472730346824344677303)
      ·
        refine ⟨380136709095520236517015955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253424472730346824344677303 380136709095520236517015955)
        ·
          refine ⟨570205063643280354775523933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380136709095520236517015955 570205063643280354775523933)
          ·
            refine ⟨213826898866230133040821475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 570205063643280354775523933 213826898866230133040821475)
            ·
              refine ⟨320740348299345199561232213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213826898866230133040821475 320740348299345199561232213)
              ·
                refine ⟨1879337978316475778679095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 320740348299345199561232213 1879337978316475778679095)
                ·
                  refine ⟨2819006967474713668018643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879337978316475778679095 2819006967474713668018643)
                  ·
                    refine ⟨4228510451212070502027965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2819006967474713668018643 4228510451212070502027965)
                    ·
                      refine ⟨1585691419204526438260487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4228510451212070502027965 1585691419204526438260487)
                      ·
                        rfl

theorem cell23_3088123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 1, 1, 3].length) (baseStart_3088123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088123 prefixEnd_3088123 := by exact prefixLift 3088123
  have htrace : WordTrace (prefixWord ++ tailWord_3088123) baseStart_3088123 baseEnd_3088123 := by
    simpa [prefixWord, tailWord_3088123, baseEnd_3088123] using wordTrace_append hprefix tailTrace_3088123
  have hstable : (prefixWord ++ tailWord_3088123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088123).length < 2 ^ (prefixWord ++ tailWord_3088123).sum := by decide
  have hdescent : baseEnd_3088123 < baseStart_3088123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088159 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 6]
def baseStart_3088159 : Nat := 118140960795 + 3088159 * 2 ^ 59
def prefixEnd_3088159 : Nat := 4983230072969 + 3 ^ 40 * 3088159 * 2
def baseEnd_3088159 : Nat := 1585709904508088297410321

theorem tailTrace_3088159 : CollatzResearch.WordTrace tailWord_3088159 prefixEnd_3088159 1585709904508088297410321 := by
  unfold tailWord_3088159
  simp only [CollatzResearch.WordTrace]
  refine ⟨112634412019134833412611531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75089608012756555608407687 112634412019134833412611531)
  ·
    refine ⟨168951618028702250118917297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112634412019134833412611531 168951618028702250118917297)
    ·
      refine ⟨126713713521526687589187973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168951618028702250118917297 126713713521526687589187973)
      ·
        refine ⟨23758821285286253922972745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126713713521526687589187973 23758821285286253922972745)
        ·
          refine ⟨17819115963964690442229559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23758821285286253922972745 17819115963964690442229559)
          ·
            refine ⟨26728673945947035663344339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17819115963964690442229559 26728673945947035663344339)
            ·
              refine ⟨40093010918920553495016509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26728673945947035663344339 40093010918920553495016509)
              ·
                refine ⟨15034879094595207560631191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40093010918920553495016509 15034879094595207560631191)
                ·
                  refine ⟨22552318641892811340946787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15034879094595207560631191 22552318641892811340946787)
                  ·
                    refine ⟨33828477962839217011420181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22552318641892811340946787 33828477962839217011420181)
                    ·
                      refine ⟨1585709904508088297410321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33828477962839217011420181 1585709904508088297410321)
                      ·
                        rfl

theorem cell23_3088159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_3088159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088159 prefixEnd_3088159 := by exact prefixLift 3088159
  have htrace : WordTrace (prefixWord ++ tailWord_3088159) baseStart_3088159 baseEnd_3088159 := by
    simpa [prefixWord, tailWord_3088159, baseEnd_3088159] using wordTrace_append hprefix tailTrace_3088159
  have hstable : (prefixWord ++ tailWord_3088159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088159).length < 2 ^ (prefixWord ++ tailWord_3088159).sum := by decide
  have hdescent : baseEnd_3088159 < baseStart_3088159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088163 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 3, 2, 2]
def baseStart_3088163 : Nat := 118140960795 + 3088163 * 2 ^ 59
def prefixEnd_3088163 : Nat := 4983230072969 + 3 ^ 40 * 3088163 * 2
def baseEnd_3088163 : Nat := 1585711958430706281760303

theorem tailTrace_3088163 : CollatzResearch.WordTrace tailWord_3088163 prefixEnd_3088163 1585711958430706281760303 := by
  unfold tailWord_3088163
  simp only [CollatzResearch.WordTrace]
  refine ⟨112634557911120342095757143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75089705274080228063838095 112634557911120342095757143)
  ·
    refine ⟨168951836866680513143635715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112634557911120342095757143 168951836866680513143635715)
    ·
      refine ⟨253427755300020769715453573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168951836866680513143635715 253427755300020769715453573)
      ·
        refine ⟨47517704118753894321647545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253427755300020769715453573 47517704118753894321647545)
        ·
          refine ⟨35638278089065420741235659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47517704118753894321647545 35638278089065420741235659)
          ·
            refine ⟨53457417133598131111853489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35638278089065420741235659 53457417133598131111853489)
            ·
              refine ⟨40093062850198598333890117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53457417133598131111853489 40093062850198598333890117)
              ·
                refine ⟨7517449284412237187604397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40093062850198598333890117 7517449284412237187604397)
                ·
                  refine ⟨2819043481654588945351649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7517449284412237187604397 2819043481654588945351649)
                  ·
                    refine ⟨2114282611240941709013737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2819043481654588945351649 2114282611240941709013737)
                    ·
                      refine ⟨1585711958430706281760303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2114282611240941709013737 1585711958430706281760303)
                      ·
                        rfl

theorem cell23_3088163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_3088163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088163 prefixEnd_3088163 := by exact prefixLift 3088163
  have htrace : WordTrace (prefixWord ++ tailWord_3088163) baseStart_3088163 baseEnd_3088163 := by
    simpa [prefixWord, tailWord_3088163, baseEnd_3088163] using wordTrace_append hprefix tailTrace_3088163
  have hstable : (prefixWord ++ tailWord_3088163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088163).length < 2 ^ (prefixWord ++ tailWord_3088163).sum := by decide
  have hdescent : baseEnd_3088163 < baseStart_3088163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088190 : List Nat := [4, 2, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_3088190 : Nat := 118140960795 + 3088190 * 2 ^ 59
def prefixEnd_3088190 : Nat := 4983230072969 + 3 ^ 40 * 3088190 * 2
def baseEnd_3088190 : Nat := 528575274136125892040893

theorem tailTrace_3088190 : CollatzResearch.WordTrace tailWord_3088190 prefixEnd_3088190 528575274136125892040893 := by
  unfold tailWord_3088190
  simp only [CollatzResearch.WordTrace]
  refine ⟨14079442835252815713373753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75090361788015017137993349 14079442835252815713373753)
  ·
    refine ⟨10559582126439611785030315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14079442835252815713373753 10559582126439611785030315)
    ·
      refine ⟨15839373189659417677545473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10559582126439611785030315 15839373189659417677545473)
      ·
        refine ⟨11879529892244563258159105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15839373189659417677545473 11879529892244563258159105)
        ·
          refine ⟨8909647419183422443619329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11879529892244563258159105 8909647419183422443619329)
          ·
            refine ⟨6682235564387566832714497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8909647419183422443619329 6682235564387566832714497)
            ·
              refine ⟨5011676673290675124535873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6682235564387566832714497 5011676673290675124535873)
              ·
                refine ⟨3758757504968006343401905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5011676673290675124535873 3758757504968006343401905)
                ·
                  refine ⟨2819068128726004757551429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3758757504968006343401905 2819068128726004757551429)
                  ·
                    refine ⟨528575274136125892040893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2819068128726004757551429 528575274136125892040893)
                    ·
                      rfl

theorem cell23_3088190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_3088190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088190 prefixEnd_3088190 := by exact prefixLift 3088190
  have htrace : WordTrace (prefixWord ++ tailWord_3088190) baseStart_3088190 baseEnd_3088190 := by
    simpa [prefixWord, tailWord_3088190, baseEnd_3088190] using wordTrace_append hprefix tailTrace_3088190
  have hstable : (prefixWord ++ tailWord_3088190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088190).length < 2 ^ (prefixWord ++ tailWord_3088190).sum := by decide
  have hdescent : baseEnd_3088190 < baseStart_3088190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088199 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 2, 7]
def baseStart_3088199 : Nat := 118140960795 + 3088199 * 2 ^ 59
def prefixEnd_3088199 : Nat := 4983230072969 + 3 ^ 40 * 3088199 * 2
def baseEnd_3088199 : Nat := 528576814578089380303379

theorem tailTrace_3088199 : CollatzResearch.WordTrace tailWord_3088199 prefixEnd_3088199 528576814578089380303379 := by
  unfold tailWord_3088199
  simp only [CollatzResearch.WordTrace]
  refine ⟨112635870938989920244067651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75090580625993280162711767 112635870938989920244067651)
  ·
    refine ⟨168953806408484880366101477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112635870938989920244067651 168953806408484880366101477)
    ·
      refine ⟨31678838701590915068644027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168953806408484880366101477 31678838701590915068644027)
      ·
        refine ⟨47518258052386372602966041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31678838701590915068644027 47518258052386372602966041)
        ·
          refine ⟨35638693539289779452224531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47518258052386372602966041 35638693539289779452224531)
          ·
            refine ⟨53458040308934669178336797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35638693539289779452224531 53458040308934669178336797)
            ·
              refine ⟨20046765115850500941876299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53458040308934669178336797 20046765115850500941876299)
              ·
                refine ⟨30070147673775751412814449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20046765115850500941876299 30070147673775751412814449)
                ·
                  refine ⟨22552610755331813559610837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30070147673775751412814449 22552610755331813559610837)
                  ·
                    refine ⟨528576814578089380303379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22552610755331813559610837 528576814578089380303379)
                    ·
                      rfl

theorem cell23_3088199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_3088199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088199 prefixEnd_3088199 := by exact prefixLift 3088199
  have htrace : WordTrace (prefixWord ++ tailWord_3088199) baseStart_3088199 baseEnd_3088199 := by
    simpa [prefixWord, tailWord_3088199, baseEnd_3088199] using wordTrace_append hprefix tailTrace_3088199
  have hstable : (prefixWord ++ tailWord_3088199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088199).length < 2 ^ (prefixWord ++ tailWord_3088199).sum := by decide
  have hdescent : baseEnd_3088199 < baseStart_3088199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088213 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 1, 3, 3]
def baseStart_3088213 : Nat := 118140960795 + 3088213 * 2 ^ 59
def prefixEnd_3088213 : Nat := 4983230072969 + 3 ^ 40 * 3088213 * 2
def baseEnd_3088213 : Nat := 1585737632463431086135073

theorem tailTrace_3088213 : CollatzResearch.WordTrace tailWord_3088213 prefixEnd_3088213 1585737632463431086135073 := by
  unfold tailWord_3088213
  simp only [CollatzResearch.WordTrace]
  refine ⟨112636381560939200635077293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75090921040626133756718195 112636381560939200635077293)
  ·
    refine ⟨42238643085352200238153985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112636381560939200635077293 42238643085352200238153985)
    ·
      refine ⟨31678982314014150178615489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42238643085352200238153985 31678982314014150178615489)
      ·
        refine ⟨23759236735510612633961617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31678982314014150178615489 23759236735510612633961617)
        ·
          refine ⟨17819427551632959475471213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23759236735510612633961617 17819427551632959475471213)
          ·
            refine ⟨6682285331862359803301705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17819427551632959475471213 6682285331862359803301705)
            ·
              refine ⟨5011713998896769852476279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6682285331862359803301705 5011713998896769852476279)
              ·
                refine ⟨7517570998345154778714419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5011713998896769852476279 7517570998345154778714419)
                ·
                  refine ⟨11276356497517732168071629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7517570998345154778714419 11276356497517732168071629)
                  ·
                    refine ⟨4228633686569149563026861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11276356497517732168071629 4228633686569149563026861)
                    ·
                      refine ⟨1585737632463431086135073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4228633686569149563026861 1585737632463431086135073)
                      ·
                        rfl

theorem cell23_3088213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_3088213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088213 prefixEnd_3088213 := by exact prefixLift 3088213
  have htrace : WordTrace (prefixWord ++ tailWord_3088213) baseStart_3088213 baseEnd_3088213 := by
    simpa [prefixWord, tailWord_3088213, baseEnd_3088213] using wordTrace_append hprefix tailTrace_3088213
  have hstable : (prefixWord ++ tailWord_3088213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088213).length < 2 ^ (prefixWord ++ tailWord_3088213).sum := by decide
  have hdescent : baseEnd_3088213 < baseStart_3088213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088223 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 3, 3, 2]
def baseStart_3088223 : Nat := 118140960795 + 3088223 * 2 ^ 59
def prefixEnd_3088223 : Nat := 4983230072969 + 3 ^ 40 * 3088223 * 2
def baseEnd_3088223 : Nat := 1585742767269976047010027

theorem tailTrace_3088223 : CollatzResearch.WordTrace tailWord_3088223 prefixEnd_3088223 1585742767269976047010027 := by
  unfold tailWord_3088223
  simp only [CollatzResearch.WordTrace]
  refine ⟨112636746290902972342941323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75091164193935314895294215 112636746290902972342941323)
  ·
    refine ⟨168955119436354458514411985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112636746290902972342941323 168955119436354458514411985)
    ·
      refine ⟨126716339577265843885808989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168955119436354458514411985 126716339577265843885808989)
      ·
        refine ⟨47518627341474691457178371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126716339577265843885808989 47518627341474691457178371)
        ·
          refine ⟨71277941012212037185767557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47518627341474691457178371 71277941012212037185767557)
          ·
            refine ⟨13364613939789756972331417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71277941012212037185767557 13364613939789756972331417)
            ·
              refine ⟨10023460454842317729248563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13364613939789756972331417 10023460454842317729248563)
              ·
                refine ⟨15035190682263476593872845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10023460454842317729248563 15035190682263476593872845)
                ·
                  refine ⟨5638196505848803722702317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15035190682263476593872845 5638196505848803722702317)
                  ·
                    refine ⟨2114323689693301396013369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5638196505848803722702317 2114323689693301396013369)
                    ·
                      refine ⟨1585742767269976047010027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2114323689693301396013369 1585742767269976047010027)
                      ·
                        rfl

theorem cell23_3088223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_3088223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088223 prefixEnd_3088223 := by exact prefixLift 3088223
  have htrace : WordTrace (prefixWord ++ tailWord_3088223) baseStart_3088223 baseEnd_3088223 := by
    simpa [prefixWord, tailWord_3088223, baseEnd_3088223] using wordTrace_append hprefix tailTrace_3088223
  have hstable : (prefixWord ++ tailWord_3088223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088223).length < 2 ^ (prefixWord ++ tailWord_3088223).sum := by decide
  have hdescent : baseEnd_3088223 < baseStart_3088223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088229 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 3, 8]
def baseStart_3088229 : Nat := 118140960795 + 3088229 * 2 ^ 59
def prefixEnd_3088229 : Nat := 4983230072969 + 3 ^ 40 * 3088229 * 2
def baseEnd_3088229 : Nat := 528581949384634341178333

theorem tailTrace_3088229 : CollatzResearch.WordTrace tailWord_3088229 prefixEnd_3088229 528581949384634341178333 := by
  unfold tailWord_3088229
  simp only [CollatzResearch.WordTrace]
  refine ⟨112636965128881235367659741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75091310085920823578439827 112636965128881235367659741)
  ·
    refine ⟨42238861923330463262872403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112636965128881235367659741 42238861923330463262872403)
    ·
      refine ⟨63358292884995694894308605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42238861923330463262872403 63358292884995694894308605)
      ·
        refine ⟨23759359831873385585365727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63358292884995694894308605 23759359831873385585365727)
        ·
          refine ⟨35639039747810078378048591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23759359831873385585365727 35639039747810078378048591)
          ·
            refine ⟨53458559621715117567072887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35639039747810078378048591 53458559621715117567072887)
            ·
              refine ⟨80187839432572676350609331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53458559621715117567072887 80187839432572676350609331)
              ·
                refine ⟨120281759148859014525913997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80187839432572676350609331 120281759148859014525913997)
                ·
                  refine ⟨45105659680822130447217749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120281759148859014525913997 45105659680822130447217749)
                  ·
                    refine ⟨528581949384634341178333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45105659680822130447217749 528581949384634341178333)
                    ·
                      rfl

theorem cell23_3088229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_3088229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088229 prefixEnd_3088229 := by exact prefixLift 3088229
  have htrace : WordTrace (prefixWord ++ tailWord_3088229) baseStart_3088229 baseEnd_3088229 := by
    simpa [prefixWord, tailWord_3088229, baseEnd_3088229] using wordTrace_append hprefix tailTrace_3088229
  have hstable : (prefixWord ++ tailWord_3088229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088229).length < 2 ^ (prefixWord ++ tailWord_3088229).sum := by decide
  have hdescent : baseEnd_3088229 < baseStart_3088229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088234 : List Nat := [3, 1, 3, 4, 1, 2, 2, 1, 1, 2, 3]
def baseStart_3088234 : Nat := 118140960795 + 3088234 * 2 ^ 59
def prefixEnd_3088234 : Nat := 4983230072969 + 3 ^ 40 * 3088234 * 2
def baseEnd_3088234 : Nat := 1585748415557175503972477

theorem tailTrace_3088234 : CollatzResearch.WordTrace tailWord_3088234 prefixEnd_3088234 1585748415557175503972477 := by
  unfold tailWord_3088234
  simp only [CollatzResearch.WordTrace]
  refine ⟨28159286873465780305397939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75091431662575414147727837 28159286873465780305397939)
  ·
    refine ⟨42238930310198670458096909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28159286873465780305397939 42238930310198670458096909)
    ·
      refine ⟨15839598866324501421786341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42238930310198670458096909 15839598866324501421786341)
      ·
        refine ⟨2969924787435844016584939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15839598866324501421786341 2969924787435844016584939)
        ·
          refine ⟨4454887181153766024877409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2969924787435844016584939 4454887181153766024877409)
          ·
            refine ⟨3341165385865324518658057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4454887181153766024877409 3341165385865324518658057)
            ·
              refine ⟨2505874039398993388993543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3341165385865324518658057 2505874039398993388993543)
              ·
                refine ⟨3758811059098490083490315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2505874039398993388993543 3758811059098490083490315)
                ·
                  refine ⟨5638216588647735125235473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3758811059098490083490315 5638216588647735125235473)
                  ·
                    refine ⟨4228662441485801343926605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5638216588647735125235473 4228662441485801343926605)
                    ·
                      refine ⟨1585748415557175503972477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4228662441485801343926605 1585748415557175503972477)
                      ·
                        rfl

theorem cell23_3088234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_3088234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088234 prefixEnd_3088234 := by exact prefixLift 3088234
  have htrace : WordTrace (prefixWord ++ tailWord_3088234) baseStart_3088234 baseEnd_3088234 := by
    simpa [prefixWord, tailWord_3088234, baseEnd_3088234] using wordTrace_append hprefix tailTrace_3088234
  have hstable : (prefixWord ++ tailWord_3088234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088234).length < 2 ^ (prefixWord ++ tailWord_3088234).sum := by decide
  have hdescent : baseEnd_3088234 < baseStart_3088234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088313 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 2, 5, 2]
def baseStart_3088313 : Nat := 118140960795 + 3088313 * 2 ^ 59
def prefixEnd_3088313 : Nat := 4983230072969 + 3 ^ 40 * 3088313 * 2
def baseEnd_3088313 : Nat := 1585788980528880694884613

theorem tailTrace_3088313 : CollatzResearch.WordTrace tailWord_3088313 prefixEnd_3088313 1585788980528880694884613 := by
  unfold tailWord_3088313
  simp only [CollatzResearch.WordTrace]
  refine ⟨112640028860576917713717593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75093352573717945142478395 112640028860576917713717593)
  ·
    refine ⟨84480021645432688285288195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112640028860576917713717593 84480021645432688285288195)
    ·
      refine ⟨126720032468149032427932293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84480021645432688285288195 126720032468149032427932293)
      ·
        refine ⟨23760006087777943580237305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126720032468149032427932293 23760006087777943580237305)
        ·
          refine ⟨17820004565833457685177979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23760006087777943580237305 17820004565833457685177979)
          ·
            refine ⟨26730006848750186527766969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17820004565833457685177979 26730006848750186527766969)
            ·
              refine ⟨20047505136562639895825227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26730006848750186527766969 20047505136562639895825227)
              ·
                refine ⟨30071257704843959843737841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20047505136562639895825227 30071257704843959843737841)
                ·
                  refine ⟨22553443278632969882803381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30071257704843959843737841 22553443278632969882803381)
                  ·
                    refine ⟨2114385307371840926512817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22553443278632969882803381 2114385307371840926512817)
                    ·
                      refine ⟨1585788980528880694884613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2114385307371840926512817 1585788980528880694884613)
                      ·
                        rfl

theorem cell23_3088313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_3088313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088313 prefixEnd_3088313 := by exact prefixLift 3088313
  have htrace : WordTrace (prefixWord ++ tailWord_3088313) baseStart_3088313 baseEnd_3088313 := by
    simpa [prefixWord, tailWord_3088313, baseEnd_3088313] using wordTrace_append hprefix tailTrace_3088313
  have hstable : (prefixWord ++ tailWord_3088313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088313).length < 2 ^ (prefixWord ++ tailWord_3088313).sum := by decide
  have hdescent : baseEnd_3088313 < baseStart_3088313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088343 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 4]
def baseStart_3088343 : Nat := 118140960795 + 3088343 * 2 ^ 59
def prefixEnd_3088343 : Nat := 4983230072969 + 3 ^ 40 * 3088343 * 2
def baseEnd_3088343 : Nat := 1585804384948515577509475

theorem tailTrace_3088343 : CollatzResearch.WordTrace tailWord_3088343 prefixEnd_3088343 1585804384948515577509475 := by
  unfold tailWord_3088343
  simp only [CollatzResearch.WordTrace]
  refine ⟨112641123050468232837309683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75094082033645488558206455 112641123050468232837309683)
  ·
    refine ⟨168961684575702349255964525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112641123050468232837309683 168961684575702349255964525)
    ·
      refine ⟨63360631715888380970986697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168961684575702349255964525 63360631715888380970986697)
      ·
        refine ⟨47520473786916285728240023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63360631715888380970986697 47520473786916285728240023)
        ·
          refine ⟨71280710680374428592360035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47520473786916285728240023 71280710680374428592360035)
          ·
            refine ⟨106921066020561642888540053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71280710680374428592360035 106921066020561642888540053)
            ·
              refine ⟨5011924969713827010400315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106921066020561642888540053 5011924969713827010400315)
              ·
                refine ⟨7517887454570740515600473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5011924969713827010400315 7517887454570740515600473)
                ·
                  refine ⟨5638415590928055386700355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7517887454570740515600473 5638415590928055386700355)
                  ·
                    refine ⟨8457623386392083080050533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5638415590928055386700355 8457623386392083080050533)
                    ·
                      refine ⟨1585804384948515577509475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8457623386392083080050533 1585804384948515577509475)
                      ·
                        rfl

theorem cell23_3088343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_3088343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088343 prefixEnd_3088343 := by exact prefixLift 3088343
  have htrace : WordTrace (prefixWord ++ tailWord_3088343) baseStart_3088343 baseEnd_3088343 := by
    simpa [prefixWord, tailWord_3088343, baseEnd_3088343] using wordTrace_append hprefix tailTrace_3088343
  have hstable : (prefixWord ++ tailWord_3088343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088343).length < 2 ^ (prefixWord ++ tailWord_3088343).sum := by decide
  have hdescent : baseEnd_3088343 < baseStart_3088343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088356 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_3088356 : Nat := 118140960795 + 3088356 * 2 ^ 59
def prefixEnd_3088356 : Nat := 4983230072969 + 3 ^ 40 * 3088356 * 2
def baseEnd_3088356 : Nat := 1585811060197024026646915

theorem tailTrace_3088356 : CollatzResearch.WordTrace tailWord_3088356 prefixEnd_3088356 1585811060197024026646915 := by
  unfold tailWord_3088356
  simp only [CollatzResearch.WordTrace]
  refine ⟨56320798599710568028766461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75094398132947424038355281 56320798599710568028766461)
  ·
    refine ⟨21120299474891463010787423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56320798599710568028766461 21120299474891463010787423)
    ·
      refine ⟨31680449212337194516181135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21120299474891463010787423 31680449212337194516181135)
      ·
        refine ⟨47520673818505791774271703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31680449212337194516181135 47520673818505791774271703)
        ·
          refine ⟨71281010727758687661407555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47520673818505791774271703 71281010727758687661407555)
          ·
            refine ⟨106921516091638031492111333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71281010727758687661407555 106921516091638031492111333)
            ·
              refine ⟨20047784267182130904770875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106921516091638031492111333 20047784267182130904770875)
              ·
                refine ⟨30071676400773196357156313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20047784267182130904770875 30071676400773196357156313)
                ·
                  refine ⟨22553757300579897267867235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30071676400773196357156313 22553757300579897267867235)
                  ·
                    refine ⟨33830635950869845901800853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22553757300579897267867235 33830635950869845901800853)
                    ·
                      refine ⟨1585811060197024026646915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33830635950869845901800853 1585811060197024026646915)
                      ·
                        rfl

theorem cell23_3088356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_3088356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088356 prefixEnd_3088356 := by exact prefixLift 3088356
  have htrace : WordTrace (prefixWord ++ tailWord_3088356) baseStart_3088356 baseEnd_3088356 := by
    simpa [prefixWord, tailWord_3088356, baseEnd_3088356] using wordTrace_append hprefix tailTrace_3088356
  have hstable : (prefixWord ++ tailWord_3088356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088356).length < 2 ^ (prefixWord ++ tailWord_3088356).sum := by decide
  have hdescent : baseEnd_3088356 < baseStart_3088356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088417 : List Nat := [1, 2, 3, 2, 5, 1, 1, 2, 6]
def baseStart_3088417 : Nat := 118140960795 + 3088417 * 2 ^ 59
def prefixEnd_3088417 : Nat := 4983230072969 + 3 ^ 40 * 3088417 * 2
def baseEnd_3088417 : Nat := 176204709168549809776015

theorem tailTrace_3088417 : CollatzResearch.WordTrace tailWord_3088417 prefixEnd_3088417 176204709168549809776015 := by
  unfold tailWord_3088417
  simp only [CollatzResearch.WordTrace]
  refine ⟨112643822052200143475503505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75095881368133428983669003 112643822052200143475503505)
  ·
    refine ⟨84482866539150107606627629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112643822052200143475503505 84482866539150107606627629)
    ·
      refine ⟨31681074952181290352485361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84482866539150107606627629 31681074952181290352485361)
      ·
        refine ⟨23760806214135967764364021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31681074952181290352485361 23760806214135967764364021)
        ·
          refine ⟨2227575582575246977909127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23760806214135967764364021 2227575582575246977909127)
          ·
            refine ⟨3341363373862870466863691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227575582575246977909127 3341363373862870466863691)
            ·
              refine ⟨5012045060794305700295537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341363373862870466863691 5012045060794305700295537)
              ·
                refine ⟨3759033795595729275221653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5012045060794305700295537 3759033795595729275221653)
                ·
                  refine ⟨176204709168549809776015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3759033795595729275221653 176204709168549809776015)
                  ·
                    rfl

theorem cell23_3088417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 6].length) (baseStart_3088417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088417 prefixEnd_3088417 := by exact prefixLift 3088417
  have htrace : WordTrace (prefixWord ++ tailWord_3088417) baseStart_3088417 baseEnd_3088417 := by
    simpa [prefixWord, tailWord_3088417, baseEnd_3088417] using wordTrace_append hprefix tailTrace_3088417
  have hstable : (prefixWord ++ tailWord_3088417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088417).length < 2 ^ (prefixWord ++ tailWord_3088417).sum := by decide
  have hdescent : baseEnd_3088417 < baseStart_3088417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088454 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_3088454 : Nat := 118140960795 + 3088454 * 2 ^ 59
def prefixEnd_3088454 : Nat := 4983230072969 + 3 ^ 40 * 3088454 * 2
def baseEnd_3088454 : Nat := 1585861381301164643221465

theorem tailTrace_3088454 : CollatzResearch.WordTrace tailWord_3088454 prefixEnd_3088454 1585861381301164643221465 := by
  unfold tailWord_3088454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3520161611033315587331263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75096781035377399196400277 3520161611033315587331263)
  ·
    refine ⟨5280242416549973380996895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3520161611033315587331263 5280242416549973380996895)
    ·
      refine ⟨7920363624824960071495343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5280242416549973380996895 7920363624824960071495343)
      ·
        refine ⟨11880545437237440107243015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7920363624824960071495343 11880545437237440107243015)
        ·
          refine ⟨17820818155856160160864523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11880545437237440107243015 17820818155856160160864523)
          ·
            refine ⟨26731227233784240241296785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17820818155856160160864523 26731227233784240241296785)
            ·
              refine ⟨20048420425338180180972589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26731227233784240241296785 20048420425338180180972589)
              ·
                refine ⟨7518157659501817567864721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20048420425338180180972589 7518157659501817567864721)
                ·
                  refine ⟨5638618244626363175898541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7518157659501817567864721 5638618244626363175898541)
                  ·
                    refine ⟨2114481841734886190961953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5638618244626363175898541 2114481841734886190961953)
                    ·
                      refine ⟨1585861381301164643221465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2114481841734886190961953 1585861381301164643221465)
                      ·
                        rfl

theorem cell23_3088454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_3088454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088454 prefixEnd_3088454 := by exact prefixLift 3088454
  have htrace : WordTrace (prefixWord ++ tailWord_3088454) baseStart_3088454 baseEnd_3088454 := by
    simpa [prefixWord, tailWord_3088454, baseEnd_3088454] using wordTrace_append hprefix tailTrace_3088454
  have hstable : (prefixWord ++ tailWord_3088454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088454).length < 2 ^ (prefixWord ++ tailWord_3088454).sum := by decide
  have hdescent : baseEnd_3088454 < baseStart_3088454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088477 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 4, 4]
def baseStart_3088477 : Nat := 118140960795 + 3088477 * 2 ^ 59
def prefixEnd_3088477 : Nat := 4983230072969 + 3 ^ 40 * 3088477 * 2
def baseEnd_3088477 : Nat := 528624397118739351077953

theorem tailTrace_3088477 : CollatzResearch.WordTrace tailWord_3088477 prefixEnd_3088477 528624397118739351077953 := by
  unfold tailWord_3088477
  simp only [CollatzResearch.WordTrace]
  refine ⟨112646010431982773722687685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75097340287988515815125123 112646010431982773722687685)
  ·
    refine ⟨21121126955996770073003941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112646010431982773722687685 21121126955996770073003941)
    ·
      refine ⟨3960211304249394388688239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21121126955996770073003941 3960211304249394388688239)
      ·
        refine ⟨5940316956374091583032359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3960211304249394388688239 5940316956374091583032359)
        ·
          refine ⟨8910475434561137374548539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5940316956374091583032359 8910475434561137374548539)
          ·
            refine ⟨13365713151841706061822809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8910475434561137374548539 13365713151841706061822809)
            ·
              refine ⟨10024284863881279546367107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13365713151841706061822809 10024284863881279546367107)
              ·
                refine ⟨15036427295821919319550661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10024284863881279546367107 15036427295821919319550661)
                ·
                  refine ⟨2819330117966609872415749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15036427295821919319550661 2819330117966609872415749)
                  ·
                    refine ⟨528624397118739351077953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2819330117966609872415749 528624397118739351077953)
                    ·
                      rfl

theorem cell23_3088477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_3088477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088477 prefixEnd_3088477 := by exact prefixLift 3088477
  have htrace : WordTrace (prefixWord ++ tailWord_3088477) baseStart_3088477 baseEnd_3088477 := by
    simpa [prefixWord, tailWord_3088477, baseEnd_3088477] using wordTrace_append hprefix tailTrace_3088477
  have hstable : (prefixWord ++ tailWord_3088477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088477).length < 2 ^ (prefixWord ++ tailWord_3088477).sum := by decide
  have hdescent : baseEnd_3088477 < baseStart_3088477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088478 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_3088478 : Nat := 118140960795 + 3088478 * 2 ^ 59
def prefixEnd_3088478 : Nat := 4983230072969 + 3 ^ 40 * 3088478 * 2
def baseEnd_3088478 : Nat := 1585873704836872549321355

theorem tailTrace_3088478 : CollatzResearch.WordTrace tailWord_3088478 prefixEnd_3088478 1585873704836872549321355 := by
  unfold tailWord_3088478
  simp only [CollatzResearch.WordTrace]
  refine ⟨14080755863122393861684261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75097364603319433928982725 14080755863122393861684261)
  ·
    refine ⟨2640141724335448849065799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14080755863122393861684261 2640141724335448849065799)
    ·
      refine ⟨3960212586503173273598699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2640141724335448849065799 3960212586503173273598699)
      ·
        refine ⟨5940318879754759910398049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3960212586503173273598699 5940318879754759910398049)
        ·
          refine ⟨4455239159816069932798537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5940318879754759910398049 4455239159816069932798537)
          ·
            refine ⟨3341429369862052449598903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4455239159816069932798537 3341429369862052449598903)
            ·
              refine ⟨5012144054793078674398355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341429369862052449598903 5012144054793078674398355)
              ·
                refine ⟨7518216082189618011597533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012144054793078674398355 7518216082189618011597533)
                ·
                  refine ⟨2819331030821106754349075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7518216082189618011597533 2819331030821106754349075)
                  ·
                    refine ⟨4228996546231660131523613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2819331030821106754349075 4228996546231660131523613)
                    ·
                      refine ⟨1585873704836872549321355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4228996546231660131523613 1585873704836872549321355)
                      ·
                        rfl

theorem cell23_3088478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_3088478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088478 prefixEnd_3088478 := by exact prefixLift 3088478
  have htrace : WordTrace (prefixWord ++ tailWord_3088478) baseStart_3088478 baseEnd_3088478 := by
    simpa [prefixWord, tailWord_3088478, baseEnd_3088478] using wordTrace_append hprefix tailTrace_3088478
  have hstable : (prefixWord ++ tailWord_3088478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088478).length < 2 ^ (prefixWord ++ tailWord_3088478).sum := by decide
  have hdescent : baseEnd_3088478 < baseStart_3088478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088484 : List Nat := [2, 3, 1, 1, 2, 1, 2, 6, 1, 2, 2]
def baseStart_3088484 : Nat := 118140960795 + 3088484 * 2 ^ 59
def prefixEnd_3088484 : Nat := 4983230072969 + 3 ^ 40 * 3088484 * 2
def baseEnd_3088484 : Nat := 1585876785720799525846327

theorem tailTrace_3088484 : CollatzResearch.WordTrace tailWord_3088484 prefixEnd_3088484 1585876785720799525846327 := by
  unfold tailWord_3088484
  simp only [CollatzResearch.WordTrace]
  refine ⟨56323132871478706959096253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75097510495304942612128337 56323132871478706959096253)
  ·
    refine ⟨21121174826804515109661095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56323132871478706959096253 21121174826804515109661095)
    ·
      refine ⟨31681762240206772664491643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21121174826804515109661095 31681762240206772664491643)
      ·
        refine ⟨47522643360310158996737465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31681762240206772664491643 47522643360310158996737465)
        ·
          refine ⟨35641982520232619247553099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47522643360310158996737465 35641982520232619247553099)
          ·
            refine ⟨53462973780348928871329649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35641982520232619247553099 53462973780348928871329649)
            ·
              refine ⟨40097230335261696653497237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53462973780348928871329649 40097230335261696653497237)
              ·
                refine ⟨1879557671965392030632683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40097230335261696653497237 1879557671965392030632683)
                ·
                  refine ⟨2819336507948088045949025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879557671965392030632683 2819336507948088045949025)
                  ·
                    refine ⟨2114502380961066034461769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2819336507948088045949025 2114502380961066034461769)
                    ·
                      refine ⟨1585876785720799525846327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2114502380961066034461769 1585876785720799525846327)
                      ·
                        rfl

theorem cell23_3088484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_3088484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088484 prefixEnd_3088484 := by exact prefixLift 3088484
  have htrace : WordTrace (prefixWord ++ tailWord_3088484) baseStart_3088484 baseEnd_3088484 := by
    simpa [prefixWord, tailWord_3088484, baseEnd_3088484] using wordTrace_append hprefix tailTrace_3088484
  have hstable : (prefixWord ++ tailWord_3088484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088484).length < 2 ^ (prefixWord ++ tailWord_3088484).sum := by decide
  have hdescent : baseEnd_3088484 < baseStart_3088484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088490 : List Nat := [3, 1, 3, 2, 3, 1, 2, 8]
def baseStart_3088490 : Nat := 118140960795 + 3088490 * 2 ^ 59
def prefixEnd_3088490 : Nat := 4983230072969 + 3 ^ 40 * 3088490 * 2
def baseEnd_3088490 : Nat := 58736291355730611198937

theorem tailTrace_3088490 : CollatzResearch.WordTrace tailWord_3088490 prefixEnd_3088490 58736291355730611198937 := by
  unfold tailWord_3088490
  simp only [CollatzResearch.WordTrace]
  refine ⟨28161621145233919235727731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75097656387290451295273949 28161621145233919235727731)
  ·
    refine ⟨42242431717850878853591597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28161621145233919235727731 42242431717850878853591597)
    ·
      refine ⟨15840911894194079570096849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42242431717850878853591597 15840911894194079570096849)
      ·
        refine ⟨11880683920645559677572637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15840911894194079570096849 11880683920645559677572637)
        ·
          refine ⟨4455256470242084879089739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11880683920645559677572637 4455256470242084879089739)
          ·
            refine ⟨6682884705363127318634609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455256470242084879089739 6682884705363127318634609)
            ·
              refine ⟨5012163529022345488975957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6682884705363127318634609 5012163529022345488975957)
              ·
                refine ⟨58736291355730611198937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5012163529022345488975957 58736291355730611198937)
                ·
                  rfl

theorem cell23_3088490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 8].length) (baseStart_3088490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088490 prefixEnd_3088490 := by exact prefixLift 3088490
  have htrace : WordTrace (prefixWord ++ tailWord_3088490) baseStart_3088490 baseEnd_3088490 := by
    simpa [prefixWord, tailWord_3088490, baseEnd_3088490] using wordTrace_append hprefix tailTrace_3088490
  have hstable : (prefixWord ++ tailWord_3088490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088490).length < 2 ^ (prefixWord ++ tailWord_3088490).sum := by decide
  have hdescent : baseEnd_3088490 < baseStart_3088490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088493 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3088493 : Nat := 118140960795 + 3088493 * 2 ^ 59
def prefixEnd_3088493 : Nat := 4983230072969 + 3 ^ 40 * 3088493 * 2
def baseEnd_3088493 : Nat := 1585881407046689990633785

theorem tailTrace_3088493 : CollatzResearch.WordTrace tailWord_3088493 prefixEnd_3088493 1585881407046689990633785 := by
  unfold tailWord_3088493
  simp only [CollatzResearch.WordTrace]
  refine ⟨112646593999924808455270133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75097729333283205636846755 112646593999924808455270133)
  ·
    refine ⟨10560618187492950792681575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112646593999924808455270133 10560618187492950792681575)
    ·
      refine ⟨15840927281239426189022363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10560618187492950792681575 15840927281239426189022363)
      ·
        refine ⟨23761390921859139283533545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15840927281239426189022363 23761390921859139283533545)
        ·
          refine ⟨17821043191394354462650159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23761390921859139283533545 17821043191394354462650159)
          ·
            refine ⟨26731564787091531693975239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17821043191394354462650159 26731564787091531693975239)
            ·
              refine ⟨40097347180637297540962859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26731564787091531693975239 40097347180637297540962859)
              ·
                refine ⟨60146020770955946311444289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40097347180637297540962859 60146020770955946311444289)
                ·
                  refine ⟨45109515578216959733583217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60146020770955946311444289 45109515578216959733583217)
                  ·
                    refine ⟨33832136683662719800187413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45109515578216959733583217 33832136683662719800187413)
                    ·
                      refine ⟨1585881407046689990633785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33832136683662719800187413 1585881407046689990633785)
                      ·
                        rfl

theorem cell23_3088493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3088493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088493 prefixEnd_3088493 := by exact prefixLift 3088493
  have htrace : WordTrace (prefixWord ++ tailWord_3088493) baseStart_3088493 baseEnd_3088493 := by
    simpa [prefixWord, tailWord_3088493, baseEnd_3088493] using wordTrace_append hprefix tailTrace_3088493
  have hstable : (prefixWord ++ tailWord_3088493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088493).length < 2 ^ (prefixWord ++ tailWord_3088493).sum := by decide
  have hdescent : baseEnd_3088493 < baseStart_3088493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088533 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 2, 6]
def baseStart_3088533 : Nat := 118140960795 + 3088533 * 2 ^ 59
def prefixEnd_3088533 : Nat := 4983230072969 + 3 ^ 40 * 3088533 * 2
def baseEnd_3088533 : Nat := 528633982090956611377867

theorem tailTrace_3088533 : CollatzResearch.WordTrace tailWord_3088533 prefixEnd_3088533 528633982090956611377867 := by
  unfold tailWord_3088533
  simp only [CollatzResearch.WordTrace]
  refine ⟨112648052919779895286726253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75098701946519930191150835 112648052919779895286726253)
  ·
    refine ⟨42243019844917460732522345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112648052919779895286726253 42243019844917460732522345)
    ·
      refine ⟨31682264883688095549391759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42243019844917460732522345 31682264883688095549391759)
      ·
        refine ⟨47523397325532143324087639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31682264883688095549391759 47523397325532143324087639)
        ·
          refine ⟨71285095988298214986131459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47523397325532143324087639 71285095988298214986131459)
          ·
            refine ⟨106927643982447322479197189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71285095988298214986131459 106927643982447322479197189)
            ·
              refine ⟨20048933246708872964849473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106927643982447322479197189 20048933246708872964849473)
              ·
                refine ⟨15036699935031654723637105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20048933246708872964849473 15036699935031654723637105)
                ·
                  refine ⟨11277524951273741042727829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15036699935031654723637105 11277524951273741042727829)
                  ·
                    refine ⟨528633982090956611377867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11277524951273741042727829 528633982090956611377867)
                    ·
                      rfl

theorem cell23_3088533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_3088533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088533 prefixEnd_3088533 := by exact prefixLift 3088533
  have htrace : WordTrace (prefixWord ++ tailWord_3088533) baseStart_3088533 baseEnd_3088533 := by
    simpa [prefixWord, tailWord_3088533, baseEnd_3088533] using wordTrace_append hprefix tailTrace_3088533
  have hstable : (prefixWord ++ tailWord_3088533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088533).length < 2 ^ (prefixWord ++ tailWord_3088533).sum := by decide
  have hdescent : baseEnd_3088533 < baseStart_3088533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088535 : List Nat := [1, 1, 3, 3, 5, 1, 2, 2, 1, 2, 2]
def baseStart_3088535 : Nat := 118140960795 + 3088535 * 2 ^ 59
def prefixEnd_3088535 : Nat := 4983230072969 + 3 ^ 40 * 3088535 * 2
def baseEnd_3088535 : Nat := 1585902973234178826308593

theorem tailTrace_3088535 : CollatzResearch.WordTrace tailWord_3088535 prefixEnd_3088535 1585902973234178826308593 := by
  unfold tailWord_3088535
  simp only [CollatzResearch.WordTrace]
  refine ⟨112648125865772649628299059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75098750577181766418866039 112648125865772649628299059)
  ·
    refine ⟨168972188798658974442448589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112648125865772649628299059 168972188798658974442448589)
    ·
      refine ⟨63364570799497115415918221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168972188798658974442448589 63364570799497115415918221)
      ·
        refine ⟨23761714049811418280969333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63364570799497115415918221 23761714049811418280969333)
        ·
          refine ⟨2227660692169820463840875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23761714049811418280969333 2227660692169820463840875)
          ·
            refine ⟨3341491038254730695761313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227660692169820463840875 3341491038254730695761313)
            ·
              refine ⟨2506118278691048021820985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3341491038254730695761313 2506118278691048021820985)
              ·
                refine ⟨1879588709018286016365739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2506118278691048021820985 1879588709018286016365739)
                ·
                  refine ⟨2819383063527429024548609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879588709018286016365739 2819383063527429024548609)
                  ·
                    refine ⟨2114537297645571768411457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2819383063527429024548609 2114537297645571768411457)
                    ·
                      refine ⟨1585902973234178826308593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2114537297645571768411457 1585902973234178826308593)
                      ·
                        rfl

theorem cell23_3088535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_3088535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088535 prefixEnd_3088535 := by exact prefixLift 3088535
  have htrace : WordTrace (prefixWord ++ tailWord_3088535) baseStart_3088535 baseEnd_3088535 := by
    simpa [prefixWord, tailWord_3088535, baseEnd_3088535] using wordTrace_append hprefix tailTrace_3088535
  have hstable : (prefixWord ++ tailWord_3088535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088535).length < 2 ^ (prefixWord ++ tailWord_3088535).sum := by decide
  have hdescent : baseEnd_3088535 < baseStart_3088535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088573 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_3088573 : Nat := 118140960795 + 3088573 * 2 ^ 59
def prefixEnd_3088573 : Nat := 4983230072969 + 3 ^ 40 * 3088573 * 2
def baseEnd_3088573 : Nat := 1585922485499049677633417

theorem tailTrace_3088573 : CollatzResearch.WordTrace tailWord_3088573 prefixEnd_3088573 1585922485499049677633417 := by
  unfold tailWord_3088573
  simp only [CollatzResearch.WordTrace]
  refine ⟨112649511839634982118182373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75099674559756654745454915 112649511839634982118182373)
  ·
    refine ⟨21121783469931559147159195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112649511839634982118182373 21121783469931559147159195)
    ·
      refine ⟨31682675204897338720738793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21121783469931559147159195 31682675204897338720738793)
      ·
        refine ⟨23762006403673004040554095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31682675204897338720738793 23762006403673004040554095)
        ·
          refine ⟨35643009605509506060831143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23762006403673004040554095 35643009605509506060831143)
          ·
            refine ⟨53464514408264259091246715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35643009605509506060831143 53464514408264259091246715)
            ·
              refine ⟨80196771612396388636870073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53464514408264259091246715 80196771612396388636870073)
              ·
                refine ⟨60147578709297291477652555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80196771612396388636870073 60147578709297291477652555)
                ·
                  refine ⟨90221368063945937216478833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60147578709297291477652555 90221368063945937216478833)
                  ·
                    refine ⟨67666026047959452912359125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90221368063945937216478833 67666026047959452912359125)
                    ·
                      refine ⟨1585922485499049677633417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67666026047959452912359125 1585922485499049677633417)
                      ·
                        rfl

theorem cell23_3088573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_3088573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088573 prefixEnd_3088573 := by exact prefixLift 3088573
  have htrace : WordTrace (prefixWord ++ tailWord_3088573) baseStart_3088573 baseEnd_3088573 := by
    simpa [prefixWord, tailWord_3088573, baseEnd_3088573] using wordTrace_append hprefix tailTrace_3088573
  have hstable : (prefixWord ++ tailWord_3088573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088573).length < 2 ^ (prefixWord ++ tailWord_3088573).sum := by decide
  have hdescent : baseEnd_3088573 < baseStart_3088573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088578 : List Nat := [3, 5, 1, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_3088578 : Nat := 118140960795 + 3088578 * 2 ^ 59
def prefixEnd_3088578 : Nat := 4983230072969 + 3 ^ 40 * 3088578 * 2
def baseEnd_3088578 : Nat := 1585925052902322158070895

theorem tailTrace_3088578 : CollatzResearch.WordTrace tailWord_3088578 prefixEnd_3088578 1585925052902322158070895 := by
  unfold tailWord_3088578
  simp only [CollatzResearch.WordTrace]
  refine ⟨28162423551154216993028597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75099796136411245314742925 28162423551154216993028597)
  ·
    refine ⟨2640227207920707843096431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28162423551154216993028597 2640227207920707843096431)
    ·
      refine ⟨3960340811881061764644647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2640227207920707843096431 3960340811881061764644647)
      ·
        refine ⟨5940511217821592646966971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3960340811881061764644647 5940511217821592646966971)
        ·
          refine ⟨8910766826732388970450457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5940511217821592646966971 8910766826732388970450457)
          ·
            refine ⟨6683075120049291727837843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8910766826732388970450457 6683075120049291727837843)
            ·
              refine ⟨10024612680073937591756765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6683075120049291727837843 10024612680073937591756765)
              ·
                refine ⟨3759229755027726596908787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10024612680073937591756765 3759229755027726596908787)
                ·
                  refine ⟨5638844632541589895363181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759229755027726596908787 5638844632541589895363181)
                  ·
                    refine ⟨2114566737203096210761193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5638844632541589895363181 2114566737203096210761193)
                    ·
                      refine ⟨1585925052902322158070895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2114566737203096210761193 1585925052902322158070895)
                      ·
                        rfl

theorem cell23_3088578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_3088578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088578 prefixEnd_3088578 := by exact prefixLift 3088578
  have htrace : WordTrace (prefixWord ++ tailWord_3088578) baseStart_3088578 baseEnd_3088578 := by
    simpa [prefixWord, tailWord_3088578, baseEnd_3088578] using wordTrace_append hprefix tailTrace_3088578
  have hstable : (prefixWord ++ tailWord_3088578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088578).length < 2 ^ (prefixWord ++ tailWord_3088578).sum := by decide
  have hdescent : baseEnd_3088578 < baseStart_3088578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088597 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 7]
def baseStart_3088597 : Nat := 118140960795 + 3088597 * 2 ^ 59
def prefixEnd_3088597 : Nat := 4983230072969 + 3 ^ 40 * 3088597 * 2
def baseEnd_3088597 : Nat := 176214978781639731525923

theorem tailTrace_3088597 : CollatzResearch.WordTrace tailWord_3088597 prefixEnd_3088597 176214978781639731525923 := by
  unfold tailWord_3088597
  simp only [CollatzResearch.WordTrace]
  refine ⟨112650387191548034217056045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75100258127698689478037363 112650387191548034217056045)
  ·
    refine ⟨42243895196830512831396017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112650387191548034217056045 42243895196830512831396017)
    ·
      refine ⟨31682921397622884623547013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42243895196830512831396017 31682921397622884623547013)
      ·
        refine ⟨5940547762054290866915065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31682921397622884623547013 5940547762054290866915065)
        ·
          refine ⟨4455410821540718150186299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5940547762054290866915065 4455410821540718150186299)
          ·
            refine ⟨6683116232311077225279449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455410821540718150186299 6683116232311077225279449)
            ·
              refine ⟨5012337174233307918959587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6683116232311077225279449 5012337174233307918959587)
              ·
                refine ⟨7518505761349961878439381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012337174233307918959587 7518505761349961878439381)
                ·
                  refine ⟨176214978781639731525923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7518505761349961878439381 176214978781639731525923)
                  ·
                    rfl

theorem cell23_3088597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 7].length) (baseStart_3088597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088597 prefixEnd_3088597 := by exact prefixLift 3088597
  have htrace : WordTrace (prefixWord ++ tailWord_3088597) baseStart_3088597 baseEnd_3088597 := by
    simpa [prefixWord, tailWord_3088597, baseEnd_3088597] using wordTrace_append hprefix tailTrace_3088597
  have hstable : (prefixWord ++ tailWord_3088597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088597).length < 2 ^ (prefixWord ++ tailWord_3088597).sum := by decide
  have hdescent : baseEnd_3088597 < baseStart_3088597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088640 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 5, 4]
def baseStart_3088640 : Nat := 118140960795 + 3088640 * 2 ^ 59
def prefixEnd_3088640 : Nat := 4983230072969 + 3 ^ 40 * 3088640 * 2
def baseEnd_3088640 : Nat := 528652296234300305165203

theorem tailTrace_3088640 : CollatzResearch.WordTrace tailWord_3088640 prefixEnd_3088640 528652296234300305165203 := by
  unfold tailWord_3088640
  simp only [CollatzResearch.WordTrace]
  refine ⟨56325977765196126280435687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75101303686928168373914249 56325977765196126280435687)
  ·
    refine ⟨84488966647794189420653531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56325977765196126280435687 84488966647794189420653531)
    ·
      refine ⟨126733449971691284130980297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84488966647794189420653531 126733449971691284130980297)
      ·
        refine ⟨95050087478768463098235223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126733449971691284130980297 95050087478768463098235223)
        ·
          refine ⟨142575131218152694647352835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95050087478768463098235223 142575131218152694647352835)
          ·
            refine ⟨213862696827229041971029253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142575131218152694647352835 213862696827229041971029253)
            ·
              refine ⟨40099255655105445369567985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213862696827229041971029253 40099255655105445369567985)
              ·
                refine ⟨30074441741329084027175989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40099255655105445369567985 30074441741329084027175989)
                ·
                  refine ⟨2819478913249601627547749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30074441741329084027175989 2819478913249601627547749)
                  ·
                    refine ⟨528652296234300305165203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2819478913249601627547749 528652296234300305165203)
                    ·
                      rfl

theorem cell23_3088640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 5, 4].length) (baseStart_3088640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088640 prefixEnd_3088640 := by exact prefixLift 3088640
  have htrace : WordTrace (prefixWord ++ tailWord_3088640) baseStart_3088640 baseEnd_3088640 := by
    simpa [prefixWord, tailWord_3088640, baseEnd_3088640] using wordTrace_append hprefix tailTrace_3088640
  have hstable : (prefixWord ++ tailWord_3088640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088640).length < 2 ^ (prefixWord ++ tailWord_3088640).sum := by decide
  have hdescent : baseEnd_3088640 < baseStart_3088640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088657 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 3, 4]
def baseStart_3088657 : Nat := 118140960795 + 3088657 * 2 ^ 59
def prefixEnd_3088657 : Nat := 4983230072969 + 3 ^ 40 * 3088657 * 2
def baseEnd_3088657 : Nat := 528655205958009116327677

theorem tailTrace_3088657 : CollatzResearch.WordTrace tailWord_3088657 prefixEnd_3088657 528655205958009116327677 := by
  unfold tailWord_3088657
  simp only [CollatzResearch.WordTrace]
  refine ⟨112652575571330664464240225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75101717047553776309493483 112652575571330664464240225)
  ·
    refine ⟨84489431678497998348180169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112652575571330664464240225 84489431678497998348180169)
    ·
      refine ⟨63367073758873498761135127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84489431678497998348180169 63367073758873498761135127)
      ·
        refine ⟨95050610638310248141702691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63367073758873498761135127 95050610638310248141702691)
        ·
          refine ⟨142575915957465372212554037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95050610638310248141702691 142575915957465372212554037)
          ·
            refine ⟨13366492121012378644926941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142575915957465372212554037 13366492121012378644926941)
            ·
              refine ⟨5012434545379641991847603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13366492121012378644926941 5012434545379641991847603)
              ·
                refine ⟨7518651818069462987771405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012434545379641991847603 7518651818069462987771405)
                ·
                  refine ⟨2819494431776048620414277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7518651818069462987771405 2819494431776048620414277)
                  ·
                    refine ⟨528655205958009116327677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2819494431776048620414277 528655205958009116327677)
                    ·
                      rfl

theorem cell23_3088657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_3088657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088657 prefixEnd_3088657 := by exact prefixLift 3088657
  have htrace : WordTrace (prefixWord ++ tailWord_3088657) baseStart_3088657 baseEnd_3088657 := by
    simpa [prefixWord, tailWord_3088657, baseEnd_3088657] using wordTrace_append hprefix tailTrace_3088657
  have hstable : (prefixWord ++ tailWord_3088657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088657).length < 2 ^ (prefixWord ++ tailWord_3088657).sum := by decide
  have hdescent : baseEnd_3088657 < baseStart_3088657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088708 : List Nat := [2, 3, 4, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3088708 : Nat := 118140960795 + 3088708 * 2 ^ 59
def prefixEnd_3088708 : Nat := 4983230072969 + 3 ^ 40 * 3088708 * 2
def baseEnd_3088708 : Nat := 528663935129135549815099

theorem tailTrace_3088708 : CollatzResearch.WordTrace tailWord_3088708 prefixEnd_3088708 528663935129135549815099 := by
  unfold tailWord_3088708
  simp only [CollatzResearch.WordTrace]
  refine ⟨56327217847072950087173389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75102957129430600116231185 56327217847072950087173389)
  ·
    refine ⟨21122706692652356282690021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56327217847072950087173389 21122706692652356282690021)
    ·
      refine ⟨3960507504872316803004379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21122706692652356282690021 3960507504872316803004379)
      ·
        refine ⟨5940761257308475204506569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3960507504872316803004379 5940761257308475204506569)
        ·
          refine ⟨4455570942981356403379927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5940761257308475204506569 4455570942981356403379927)
          ·
            refine ⟨6683356414472034605069891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455570942981356403379927 6683356414472034605069891)
            ·
              refine ⟨10025034621708051907604837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6683356414472034605069891 10025034621708051907604837)
              ·
                refine ⟨1879693991570259732675907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10025034621708051907604837 1879693991570259732675907)
                ·
                  refine ⟨2819540987355389599013861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879693991570259732675907 2819540987355389599013861)
                  ·
                    refine ⟨528663935129135549815099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2819540987355389599013861 528663935129135549815099)
                    ·
                      rfl

theorem cell23_3088708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3088708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088708 prefixEnd_3088708 := by exact prefixLift 3088708
  have htrace : WordTrace (prefixWord ++ tailWord_3088708) baseStart_3088708 baseEnd_3088708 := by
    simpa [prefixWord, tailWord_3088708, baseEnd_3088708] using wordTrace_append hprefix tailTrace_3088708
  have hstable : (prefixWord ++ tailWord_3088708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088708).length < 2 ^ (prefixWord ++ tailWord_3088708).sum := by decide
  have hdescent : baseEnd_3088708 < baseStart_3088708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088741 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 2, 3, 2]
def baseStart_3088741 : Nat := 118140960795 + 3088741 * 2 ^ 59
def prefixEnd_3088741 : Nat := 4983230072969 + 3 ^ 40 * 3088741 * 2
def baseEnd_3088741 : Nat := 1586008750249005020332645

theorem tailTrace_3088741 : CollatzResearch.WordTrace tailWord_3088741 prefixEnd_3088741 1586008750249005020332645 := by
  unfold tailWord_3088741
  simp only [CollatzResearch.WordTrace]
  refine ⟨112655639303026346810298077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75103759535350897873532051 112655639303026346810298077)
  ·
    refine ⟨42245864738634880053861779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112655639303026346810298077 42245864738634880053861779)
    ·
      refine ⟨63368797107952320080792669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42245864738634880053861779 63368797107952320080792669)
      ·
        refine ⟨23763298915482120030297251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63368797107952320080792669 23763298915482120030297251)
        ·
          refine ⟨35644948373223180045445877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23763298915482120030297251 35644948373223180045445877)
          ·
            refine ⟨3341713909989673129260551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35644948373223180045445877 3341713909989673129260551)
            ·
              refine ⟨5012570864984509693890827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341713909989673129260551 5012570864984509693890827)
              ·
                refine ⟨7518856297476764540836241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012570864984509693890827 7518856297476764540836241)
                ·
                  refine ⟨5639142223107573405627181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7518856297476764540836241 5639142223107573405627181)
                  ·
                    refine ⟨2114678333665340027110193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5639142223107573405627181 2114678333665340027110193)
                    ·
                      refine ⟨1586008750249005020332645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2114678333665340027110193 1586008750249005020332645)
                      ·
                        rfl

theorem cell23_3088741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_3088741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088741 prefixEnd_3088741 := by exact prefixLift 3088741
  have htrace : WordTrace (prefixWord ++ tailWord_3088741) baseStart_3088741 baseEnd_3088741 := by
    simpa [prefixWord, tailWord_3088741, baseEnd_3088741] using wordTrace_append hprefix tailTrace_3088741
  have hstable : (prefixWord ++ tailWord_3088741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088741).length < 2 ^ (prefixWord ++ tailWord_3088741).sum := by decide
  have hdescent : baseEnd_3088741 < baseStart_3088741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088748 : List Nat := [2, 2, 1, 1, 6, 1, 2, 3, 1, 1, 3]
def baseStart_3088748 : Nat := 118140960795 + 3088748 * 2 ^ 59
def prefixEnd_3088748 : Nat := 4983230072969 + 3 ^ 40 * 3088748 * 2
def baseEnd_3088748 : Nat := 1586012344613586492945113

theorem tailTrace_3088748 : CollatzResearch.WordTrace tailWord_3088748 prefixEnd_3088748 1586012344613586492945113 := by
  unfold tailWord_3088748
  simp only [CollatzResearch.WordTrace]
  refine ⟨56327947307000493502901449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75103929742667324670535265 56327947307000493502901449)
  ·
    refine ⟨42245960480250370127176087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56327947307000493502901449 42245960480250370127176087)
    ·
      refine ⟨63368940720375555190764131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42245960480250370127176087 63368940720375555190764131)
      ·
        refine ⟨95053411080563332786146197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63368940720375555190764131 95053411080563332786146197)
        ·
          refine ⟨4455628644401406224350603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95053411080563332786146197 4455628644401406224350603)
          ·
            refine ⟨6683442966602109336525905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455628644401406224350603 6683442966602109336525905)
            ·
              refine ⟨5012582224951582002394429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6683442966602109336525905 5012582224951582002394429)
              ·
                refine ⟨1879718334356843250897911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5012582224951582002394429 1879718334356843250897911)
                ·
                  refine ⟨2819577501535264876346867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879718334356843250897911 2819577501535264876346867)
                  ·
                    refine ⟨4229366252302897314520301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2819577501535264876346867 4229366252302897314520301)
                    ·
                      refine ⟨1586012344613586492945113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4229366252302897314520301 1586012344613586492945113)
                      ·
                        rfl

theorem cell23_3088748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 1, 1, 3].length) (baseStart_3088748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088748 prefixEnd_3088748 := by exact prefixLift 3088748
  have htrace : WordTrace (prefixWord ++ tailWord_3088748) baseStart_3088748 baseEnd_3088748 := by
    simpa [prefixWord, tailWord_3088748, baseEnd_3088748] using wordTrace_append hprefix tailTrace_3088748
  have hstable : (prefixWord ++ tailWord_3088748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088748).length < 2 ^ (prefixWord ++ tailWord_3088748).sum := by decide
  have hdescent : baseEnd_3088748 < baseStart_3088748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088754 : List Nat := [3, 2, 1, 2, 1, 4, 1, 3, 1, 1, 4]
def baseStart_3088754 : Nat := 118140960795 + 3088754 * 2 ^ 59
def prefixEnd_3088754 : Nat := 4983230072969 + 3 ^ 40 * 3088754 * 2
def baseEnd_3088754 : Nat := 1586015425497513469470085

theorem tailTrace_3088754 : CollatzResearch.WordTrace tailWord_3088754 prefixEnd_3088754 1586015425497513469470085 := by
  unfold tailWord_3088754
  simp only [CollatzResearch.WordTrace]
  refine ⟨28164028362994812507630329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75104075634652833353680877 28164028362994812507630329)
  ·
    refine ⟨21123021272246109380722747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28164028362994812507630329 21123021272246109380722747)
    ·
      refine ⟨31684531908369164071084121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21123021272246109380722747 31684531908369164071084121)
      ·
        refine ⟨23763398931276873053313091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31684531908369164071084121 23763398931276873053313091)
        ·
          refine ⟨35645098396915309579969637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23763398931276873053313091 35645098396915309579969637)
          ·
            refine ⟨6683455949421620546244307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35645098396915309579969637 6683455949421620546244307)
            ·
              refine ⟨10025183924132430819366461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6683455949421620546244307 10025183924132430819366461)
              ·
                refine ⟨3759443971549661557262423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10025183924132430819366461 3759443971549661557262423)
                ·
                  refine ⟨5639165957324492335893635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759443971549661557262423 5639165957324492335893635)
                  ·
                    refine ⟨8458748935986738503840453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5639165957324492335893635 8458748935986738503840453)
                    ·
                      refine ⟨1586015425497513469470085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8458748935986738503840453 1586015425497513469470085)
                      ·
                        rfl

theorem cell23_3088754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_3088754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088754 prefixEnd_3088754 := by exact prefixLift 3088754
  have htrace : WordTrace (prefixWord ++ tailWord_3088754) baseStart_3088754 baseEnd_3088754 := by
    simpa [prefixWord, tailWord_3088754, baseEnd_3088754] using wordTrace_append hprefix tailTrace_3088754
  have hstable : (prefixWord ++ tailWord_3088754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088754).length < 2 ^ (prefixWord ++ tailWord_3088754).sum := by decide
  have hdescent : baseEnd_3088754 < baseStart_3088754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088794 : List Nat := [3, 1, 1, 4, 1, 4, 2, 7]
def baseStart_3088794 : Nat := 118140960795 + 3088794 * 2 ^ 59
def prefixEnd_3088794 : Nat := 4983230072969 + 3 ^ 40 * 3088794 * 2
def baseEnd_3088794 : Nat := 58742072767544196776663

theorem tailTrace_3088794 : CollatzResearch.WordTrace tailWord_3088794 prefixEnd_3088794 58742072767544196776663 := by
  unfold tailWord_3088794
  simp only [CollatzResearch.WordTrace]
  refine ⟨28164393092958584215494359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75105048247889557907984957 28164393092958584215494359)
  ·
    refine ⟨42246589639437876323241539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28164393092958584215494359 42246589639437876323241539)
    ·
      refine ⟨63369884459156814484862309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42246589639437876323241539 63369884459156814484862309)
      ·
        refine ⟨11881853336091902715911683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63369884459156814484862309 11881853336091902715911683)
        ·
          refine ⟨17822780004137854073867525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11881853336091902715911683 17822780004137854073867525)
          ·
            refine ⟨3341771250775847638850161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17822780004137854073867525 3341771250775847638850161)
            ·
              refine ⟨2506328438081885729137621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3341771250775847638850161 2506328438081885729137621)
              ·
                refine ⟨58742072767544196776663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2506328438081885729137621 58742072767544196776663)
                ·
                  rfl

theorem cell23_3088794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 7].length) (baseStart_3088794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088794 prefixEnd_3088794 := by exact prefixLift 3088794
  have htrace : WordTrace (prefixWord ++ tailWord_3088794) baseStart_3088794 baseEnd_3088794 := by
    simpa [prefixWord, tailWord_3088794, baseEnd_3088794] using wordTrace_append hprefix tailTrace_3088794
  have hstable : (prefixWord ++ tailWord_3088794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088794).length < 2 ^ (prefixWord ++ tailWord_3088794).sum := by decide
  have hdescent : baseEnd_3088794 < baseStart_3088794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088804 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 4, 1, 3]
def baseStart_3088804 : Nat := 118140960795 + 3088804 * 2 ^ 59
def prefixEnd_3088804 : Nat := 4983230072969 + 3 ^ 40 * 3088804 * 2
def baseEnd_3088804 : Nat := 1586041099530238273844855

theorem tailTrace_3088804 : CollatzResearch.WordTrace tailWord_3088804 prefixEnd_3088804 1586041099530238273844855 := by
  unfold tailWord_3088804
  simp only [CollatzResearch.WordTrace]
  refine ⟨56328968550899054284920733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75105291401198739046560977 56328968550899054284920733)
  ·
    refine ⟨21123363206587145356845275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56328968550899054284920733 21123363206587145356845275)
    ·
      refine ⟨31685044809880718035267913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21123363206587145356845275 31685044809880718035267913)
      ·
        refine ⟨23763783607410538526450935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31685044809880718035267913 23763783607410538526450935)
        ·
          refine ⟨35645675411115807789676403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23763783607410538526450935 35645675411115807789676403)
          ·
            refine ⟨53468513116673711684514605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35645675411115807789676403 53468513116673711684514605)
            ·
              refine ⟨20050692418752641881692977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53468513116673711684514605 20050692418752641881692977)
              ·
                refine ⟨15038019314064481411269733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20050692418752641881692977 15038019314064481411269733)
                ·
                  refine ⟨2819628621387090264613075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15038019314064481411269733 2819628621387090264613075)
                  ·
                    refine ⟨4229442932080635396919613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2819628621387090264613075 4229442932080635396919613)
                    ·
                      refine ⟨1586041099530238273844855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4229442932080635396919613 1586041099530238273844855)
                      ·
                        rfl

theorem cell23_3088804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_3088804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088804 prefixEnd_3088804 := by exact prefixLift 3088804
  have htrace : WordTrace (prefixWord ++ tailWord_3088804) baseStart_3088804 baseEnd_3088804 := by
    simpa [prefixWord, tailWord_3088804, baseEnd_3088804] using wordTrace_append hprefix tailTrace_3088804
  have hstable : (prefixWord ++ tailWord_3088804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088804).length < 2 ^ (prefixWord ++ tailWord_3088804).sum := by decide
  have hdescent : baseEnd_3088804 < baseStart_3088804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088861 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_3088861 : Nat := 118140960795 + 3088861 * 2 ^ 59
def prefixEnd_3088861 : Nat := 4983230072969 + 3 ^ 40 * 3088861 * 2
def baseEnd_3088861 : Nat := 1586070367927544550832093

theorem tailTrace_3088861 : CollatzResearch.WordTrace tailWord_3088861 prefixEnd_3088861 1586070367927544550832093 := by
  unfold tailWord_3088861
  simp only [CollatzResearch.WordTrace]
  refine ⟨112660016062591607304666437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75106677375061071536444291 112660016062591607304666437)
  ·
    refine ⟨21123753011735926369624957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112660016062591607304666437 21123753011735926369624957)
    ·
      refine ⟨7921407379400972388609359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21123753011735926369624957 7921407379400972388609359)
      ·
        refine ⟨11882111069101458582914039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7921407379400972388609359 11882111069101458582914039)
        ·
          refine ⟨17823166603652187874371059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11882111069101458582914039 17823166603652187874371059)
          ·
            refine ⟨26734749905478281811556589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17823166603652187874371059 26734749905478281811556589)
            ·
              refine ⟨10025531214554355679333721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26734749905478281811556589 10025531214554355679333721)
              ·
                refine ⟨7519148410915766759500291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10025531214554355679333721 7519148410915766759500291)
                ·
                  refine ⟨11278722616373650139250437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7519148410915766759500291 11278722616373650139250437)
                  ·
                    refine ⟨2114760490570059401109457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11278722616373650139250437 2114760490570059401109457)
                    ·
                      refine ⟨1586070367927544550832093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2114760490570059401109457 1586070367927544550832093)
                      ·
                        rfl

theorem cell23_3088861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_3088861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088861 prefixEnd_3088861 := by exact prefixLift 3088861
  have htrace : WordTrace (prefixWord ++ tailWord_3088861) baseStart_3088861 baseEnd_3088861 := by
    simpa [prefixWord, tailWord_3088861, baseEnd_3088861] using wordTrace_append hprefix tailTrace_3088861
  have hstable : (prefixWord ++ tailWord_3088861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088861).length < 2 ^ (prefixWord ++ tailWord_3088861).sum := by decide
  have hdescent : baseEnd_3088861 < baseStart_3088861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088878 : List Nat := [4, 1, 2, 1, 2, 2, 1, 4, 2, 2, 2]
def baseStart_3088878 : Nat := 118140960795 + 3088878 * 2 ^ 59
def prefixEnd_3088878 : Nat := 4983230072969 + 3 ^ 40 * 3088878 * 2
def baseEnd_3088878 : Nat := 1586079097098670984319515

theorem tailTrace_3088878 : CollatzResearch.WordTrace tailWord_3088878 prefixEnd_3088878 1586079097098670984319515 := by
  unfold tailWord_3088878
  simp only [CollatzResearch.WordTrace]
  refine ⟨14082579512941252401004411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75107090735686679472023525 14082579512941252401004411)
  ·
    refine ⟨21123869269411878601506617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14082579512941252401004411 21123869269411878601506617)
    ·
      refine ⟨15842901952058908951129963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21123869269411878601506617 15842901952058908951129963)
      ·
        refine ⟨23764352928088363426694945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15842901952058908951129963 23764352928088363426694945)
        ·
          refine ⟨17823264696066272570021209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23764352928088363426694945 17823264696066272570021209)
          ·
            refine ⟨13367448522049704427515907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17823264696066272570021209 13367448522049704427515907)
            ·
              refine ⟨20051172783074556641273861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13367448522049704427515907 20051172783074556641273861)
              ·
                refine ⟨3759594896826479370238849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20051172783074556641273861 3759594896826479370238849)
                ·
                  refine ⟨2819696172619859527679137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3759594896826479370238849 2819696172619859527679137)
                  ·
                    refine ⟨2114772129464894645759353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2819696172619859527679137 2114772129464894645759353)
                    ·
                      refine ⟨1586079097098670984319515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2114772129464894645759353 1586079097098670984319515)
                      ·
                        rfl

theorem cell23_3088878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_3088878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088878 prefixEnd_3088878 := by exact prefixLift 3088878
  have htrace : WordTrace (prefixWord ++ tailWord_3088878) baseStart_3088878 baseEnd_3088878 := by
    simpa [prefixWord, tailWord_3088878, baseEnd_3088878] using wordTrace_append hprefix tailTrace_3088878
  have hstable : (prefixWord ++ tailWord_3088878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088878).length < 2 ^ (prefixWord ++ tailWord_3088878).sum := by decide
  have hdescent : baseEnd_3088878 < baseStart_3088878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088904 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 4, 5, 2]
def baseStart_3088904 : Nat := 118140960795 + 3088904 * 2 ^ 59
def prefixEnd_3088904 : Nat := 4983230072969 + 3 ^ 40 * 3088904 * 2
def baseEnd_3088904 : Nat := 1586092447595687882594395

theorem tailTrace_3088904 : CollatzResearch.WordTrace tailWord_3088904 prefixEnd_3088904 1586092447595687882594395 := by
  unfold tailWord_3088904
  simp only [CollatzResearch.WordTrace]
  refine ⟨56330792200717912824240883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75107722934290550432321177 56330792200717912824240883)
  ·
    refine ⟨84496188301076869236361325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56330792200717912824240883 84496188301076869236361325)
    ·
      refine ⟨31686070612903825963635497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84496188301076869236361325 31686070612903825963635497)
      ·
        refine ⟨23764552959677869472726623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31686070612903825963635497 23764552959677869472726623)
        ·
          refine ⟨35646829439516804209089935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23764552959677869472726623 35646829439516804209089935)
          ·
            refine ⟨53470244159275206313634903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35646829439516804209089935 53470244159275206313634903)
            ·
              refine ⟨80205366238912809470452355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53470244159275206313634903 80205366238912809470452355)
              ·
                refine ⟨120308049358369214205678533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80205366238912809470452355 120308049358369214205678533)
                ·
                  refine ⟨22557759254694227663564725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120308049358369214205678533 22557759254694227663564725)
                  ·
                    refine ⟨2114789930127583843459193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22557759254694227663564725 2114789930127583843459193)
                    ·
                      refine ⟨1586092447595687882594395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2114789930127583843459193 1586092447595687882594395)
                      ·
                        rfl

theorem cell23_3088904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_3088904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088904 prefixEnd_3088904 := by exact prefixLift 3088904
  have htrace : WordTrace (prefixWord ++ tailWord_3088904) baseStart_3088904 baseEnd_3088904 := by
    simpa [prefixWord, tailWord_3088904, baseEnd_3088904] using wordTrace_append hprefix tailTrace_3088904
  have hstable : (prefixWord ++ tailWord_3088904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088904).length < 2 ^ (prefixWord ++ tailWord_3088904).sum := by decide
  have hdescent : baseEnd_3088904 < baseStart_3088904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088944 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 3, 4]
def baseStart_3088944 : Nat := 118140960795 + 3088944 * 2 ^ 59
def prefixEnd_3088944 : Nat := 4983230072969 + 3 ^ 40 * 3088944 * 2
def baseEnd_3088944 : Nat := 528704328940622575364737

theorem tailTrace_3088944 : CollatzResearch.WordTrace tailWord_3088944 prefixEnd_3088944 528704328940622575364737 := by
  unfold tailWord_3088944
  simp only [CollatzResearch.WordTrace]
  refine ⟨56331521660645456239968943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75108695547527274986625257 56331521660645456239968943)
  ·
    refine ⟨84497282490968184359953415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56331521660645456239968943 84497282490968184359953415)
    ·
      refine ⟨126745923736452276539930123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84497282490968184359953415 126745923736452276539930123)
      ·
        refine ⟨190118885604678414809895185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126745923736452276539930123 190118885604678414809895185)
        ·
          refine ⟨142589164203508811107421389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190118885604678414809895185 142589164203508811107421389)
          ·
            refine ⟨53470936576315804165283021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142589164203508811107421389 53470936576315804165283021)
            ·
              refine ⟨20051601216118426561981133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53470936576315804165283021 20051601216118426561981133)
              ·
                refine ⟨7519350456044409960742925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20051601216118426561981133 7519350456044409960742925)
                ·
                  refine ⟨2819756421016653735278597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7519350456044409960742925 2819756421016653735278597)
                  ·
                    refine ⟨528704328940622575364737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2819756421016653735278597 528704328940622575364737)
                    ·
                      rfl

theorem cell23_3088944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 3, 4].length) (baseStart_3088944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088944 prefixEnd_3088944 := by exact prefixLift 3088944
  have htrace : WordTrace (prefixWord ++ tailWord_3088944) baseStart_3088944 baseEnd_3088944 := by
    simpa [prefixWord, tailWord_3088944, baseEnd_3088944] using wordTrace_append hprefix tailTrace_3088944
  have hstable : (prefixWord ++ tailWord_3088944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088944).length < 2 ^ (prefixWord ++ tailWord_3088944).sum := by decide
  have hdescent : baseEnd_3088944 < baseStart_3088944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088947 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 6]
def baseStart_3088947 : Nat := 118140960795 + 3088947 * 2 ^ 59
def prefixEnd_3088947 : Nat := 4983230072969 + 3 ^ 40 * 3088947 * 2
def baseEnd_3088947 : Nat := 1586114527263831214356697

theorem tailTrace_3088947 : CollatzResearch.WordTrace tailWord_3088947 prefixEnd_3088947 1586114527263831214356697 := by
  unfold tailWord_3088947
  simp only [CollatzResearch.WordTrace]
  refine ⟨112663152740280043992297095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75108768493520029328198063 112663152740280043992297095)
  ·
    refine ⟨168994729110420065988445643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112663152740280043992297095 168994729110420065988445643)
    ·
      refine ⟨253492093665630098982668465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168994729110420065988445643 253492093665630098982668465)
      ·
        refine ⟨190119070249222574237001349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253492093665630098982668465 190119070249222574237001349)
        ·
          refine ⟨35647325671729232669437753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190119070249222574237001349 35647325671729232669437753)
          ·
            refine ⟨26735494253796924502078315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35647325671729232669437753 26735494253796924502078315)
            ·
              refine ⟨40103241380695386753117473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26735494253796924502078315 40103241380695386753117473)
              ·
                refine ⟨30077431035521540064838105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40103241380695386753117473 30077431035521540064838105)
                ·
                  refine ⟨22558073276641155048628579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30077431035521540064838105 22558073276641155048628579)
                  ·
                    refine ⟨33837109914961732572942869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22558073276641155048628579 33837109914961732572942869)
                    ·
                      refine ⟨1586114527263831214356697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33837109914961732572942869 1586114527263831214356697)
                      ·
                        rfl

theorem cell23_3088947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_3088947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088947 prefixEnd_3088947 := by exact prefixLift 3088947
  have htrace : WordTrace (prefixWord ++ tailWord_3088947) baseStart_3088947 baseEnd_3088947 := by
    simpa [prefixWord, tailWord_3088947, baseEnd_3088947] using wordTrace_append hprefix tailTrace_3088947
  have hstable : (prefixWord ++ tailWord_3088947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088947).length < 2 ^ (prefixWord ++ tailWord_3088947).sum := by decide
  have hdescent : baseEnd_3088947 < baseStart_3088947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088954 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3]
def baseStart_3088954 : Nat := 118140960795 + 3088954 * 2 ^ 59
def prefixEnd_3088954 : Nat := 4983230072969 + 3 ^ 40 * 3088954 * 2
def baseEnd_3088954 : Nat := 1586118121628412686969165

theorem tailTrace_3088954 : CollatzResearch.WordTrace tailWord_3088954 prefixEnd_3088954 1586118121628412686969165 := by
  unfold tailWord_3088954
  simp only [CollatzResearch.WordTrace]
  refine ⟨28165852012813671046950479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75108938700836456125201277 28165852012813671046950479)
  ·
    refine ⟨42248778019220506570425719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28165852012813671046950479 42248778019220506570425719)
    ·
      refine ⟨63373167028830759855638579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42248778019220506570425719 63373167028830759855638579)
      ·
        refine ⟨95059750543246139783457869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63373167028830759855638579 95059750543246139783457869)
        ·
          refine ⟨35647406453717302418796701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95059750543246139783457869 35647406453717302418796701)
          ·
            refine ⟨13367777420143988407048763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35647406453717302418796701 13367777420143988407048763)
            ·
              refine ⟨20051666130215982610573145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13367777420143988407048763 20051666130215982610573145)
              ·
                refine ⟨15038749597661986957929859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20051666130215982610573145 15038749597661986957929859)
                ·
                  refine ⟨22558124396492980436894789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15038749597661986957929859 22558124396492980436894789)
                  ·
                    refine ⟨4229648324342433831917773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22558124396492980436894789 4229648324342433831917773)
                    ·
                      refine ⟨1586118121628412686969165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4229648324342433831917773 1586118121628412686969165)
                      ·
                        rfl

theorem cell23_3088954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_3088954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088954 prefixEnd_3088954 := by exact prefixLift 3088954
  have htrace : WordTrace (prefixWord ++ tailWord_3088954) baseStart_3088954 baseEnd_3088954 := by
    simpa [prefixWord, tailWord_3088954, baseEnd_3088954] using wordTrace_append hprefix tailTrace_3088954
  have hstable : (prefixWord ++ tailWord_3088954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088954).length < 2 ^ (prefixWord ++ tailWord_3088954).sum := by decide
  have hdescent : baseEnd_3088954 < baseStart_3088954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088961 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 3, 4]
def baseStart_3088961 : Nat := 118140960795 + 3088961 * 2 ^ 59
def prefixEnd_3088961 : Nat := 4983230072969 + 3 ^ 40 * 3088961 * 2
def baseEnd_3088961 : Nat := 528707238664331386527211

theorem tailTrace_3088961 : CollatzResearch.WordTrace tailWord_3088961 prefixEnd_3088961 528707238664331386527211 := by
  unfold tailWord_3088961
  simp only [CollatzResearch.WordTrace]
  refine ⟨112663663362229324383306737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75109108908152882922204491 112663663362229324383306737)
  ·
    refine ⟨84497747521671993287480053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112663663362229324383306737 84497747521671993287480053)
    ·
      refine ⟨7921663830156749370701255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84497747521671993287480053 7921663830156749370701255)
      ·
        refine ⟨11882495745235124056051883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7921663830156749370701255 11882495745235124056051883)
        ·
          refine ⟨17823743617852686084077825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11882495745235124056051883 17823743617852686084077825)
          ·
            refine ⟨13367807713389514563058369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17823743617852686084077825 13367807713389514563058369)
            ·
              refine ⟨10025855785042135922293777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13367807713389514563058369 10025855785042135922293777)
              ·
                refine ⟨7519391838781601941720333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10025855785042135922293777 7519391838781601941720333)
                ·
                  refine ⟨2819771939543100728145125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7519391838781601941720333 2819771939543100728145125)
                  ·
                    refine ⟨528707238664331386527211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2819771939543100728145125 528707238664331386527211)
                    ·
                      rfl

theorem cell23_3088961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_3088961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088961 prefixEnd_3088961 := by exact prefixLift 3088961
  have htrace : WordTrace (prefixWord ++ tailWord_3088961) baseStart_3088961 baseEnd_3088961 := by
    simpa [prefixWord, tailWord_3088961, baseEnd_3088961] using wordTrace_append hprefix tailTrace_3088961
  have hstable : (prefixWord ++ tailWord_3088961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088961).length < 2 ^ (prefixWord ++ tailWord_3088961).sum := by decide
  have hdescent : baseEnd_3088961 < baseStart_3088961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088988 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_3088988 : Nat := 118140960795 + 3088988 * 2 ^ 59
def prefixEnd_3088988 : Nat := 4983230072969 + 3 ^ 40 * 3088988 * 2
def baseEnd_3088988 : Nat := 1586135579970665553944009

theorem tailTrace_3088988 : CollatzResearch.WordTrace tailWord_3088988 prefixEnd_3088988 1586135579970665553944009 := by
  unfold tailWord_3088988
  simp only [CollatzResearch.WordTrace]
  refine ⟨56332324066565753997269809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75109765422087671996359745 56332324066565753997269809)
  ·
    refine ⟨42249243049924315497952357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56332324066565753997269809 42249243049924315497952357)
    ·
      refine ⟨7921733071860809155866067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42249243049924315497952357 7921733071860809155866067)
      ·
        refine ⟨11882599607791213733799101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7921733071860809155866067 11882599607791213733799101)
        ·
          refine ⟨4455974852921705150174663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11882599607791213733799101 4455974852921705150174663)
          ·
            refine ⟨6683962279382557725261995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455974852921705150174663 6683962279382557725261995)
            ·
              refine ⟨10025943419073836587892993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6683962279382557725261995 10025943419073836587892993)
              ·
                refine ⟨7519457564305377440919745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10025943419073836587892993 7519457564305377440919745)
                ·
                  refine ⟨5639593173229033080689809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7519457564305377440919745 5639593173229033080689809)
                  ·
                    refine ⟨4229694879921774810517357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5639593173229033080689809 4229694879921774810517357)
                    ·
                      refine ⟨1586135579970665553944009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4229694879921774810517357 1586135579970665553944009)
                      ·
                        rfl

theorem cell23_3088988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_3088988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3088988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3088988 prefixEnd_3088988 := by exact prefixLift 3088988
  have htrace : WordTrace (prefixWord ++ tailWord_3088988) baseStart_3088988 baseEnd_3088988 := by
    simpa [prefixWord, tailWord_3088988, baseEnd_3088988] using wordTrace_append hprefix tailTrace_3088988
  have hstable : (prefixWord ++ tailWord_3088988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088988).length < 2 ^ (prefixWord ++ tailWord_3088988).sum := by decide
  have hdescent : baseEnd_3088988 < baseStart_3088988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089008 : List Nat := [2, 1, 1, 1, 7, 2, 2, 1, 6]
def baseStart_3089008 : Nat := 118140960795 + 3089008 * 2 ^ 59
def prefixEnd_3089008 : Nat := 4983230072969 + 3 ^ 40 * 3089008 * 2
def baseEnd_3089008 : Nat := 176238427731528386188213

theorem tailTrace_3089008 : CollatzResearch.WordTrace tailWord_3089008 prefixEnd_3089008 176238427731528386188213 := by
  unfold tailWord_3089008
  simp only [CollatzResearch.WordTrace]
  refine ⟨56332688796529525705133839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75110251728706034273511785 56332688796529525705133839)
  ·
    refine ⟨84499033194794288557700759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56332688796529525705133839 84499033194794288557700759)
    ·
      refine ⟨126748549792191432836551139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84499033194794288557700759 126748549792191432836551139)
      ·
        refine ⟨190122824688287149254826709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126748549792191432836551139 190122824688287149254826709)
        ·
          refine ⟨4456003703631730060660001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 190122824688287149254826709 4456003703631730060660001)
          ·
            refine ⟨3342002777723797545495001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4456003703631730060660001 3342002777723797545495001)
            ·
              refine ⟨2506502083292848159121251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3342002777723797545495001 2506502083292848159121251)
              ·
                refine ⟨3759753124939272238681877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2506502083292848159121251 3759753124939272238681877)
                ·
                  refine ⟨176238427731528386188213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3759753124939272238681877 176238427731528386188213)
                  ·
                    rfl

theorem cell23_3089008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 6].length) (baseStart_3089008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089008 prefixEnd_3089008 := by exact prefixLift 3089008
  have htrace : WordTrace (prefixWord ++ tailWord_3089008) baseStart_3089008 baseEnd_3089008 := by
    simpa [prefixWord, tailWord_3089008, baseEnd_3089008] using wordTrace_append hprefix tailTrace_3089008
  have hstable : (prefixWord ++ tailWord_3089008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089008).length < 2 ^ (prefixWord ++ tailWord_3089008).sum := by decide
  have hdescent : baseEnd_3089008 < baseStart_3089008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089021 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 3, 5]
def baseStart_3089021 : Nat := 118140960795 + 3089021 * 2 ^ 59
def prefixEnd_3089021 : Nat := 4983230072969 + 3 ^ 40 * 3089021 * 2
def baseEnd_3089021 : Nat := 528717508277421308277119

theorem tailTrace_3089021 : CollatzResearch.WordTrace tailWord_3089021 prefixEnd_3089021 528717508277421308277119 := by
  unfold tailWord_3089021
  simp only [CollatzResearch.WordTrace]
  refine ⟨112665851742011954630490917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75110567828007969753660611 112665851742011954630490917)
  ·
    refine ⟨21124847201627241493217047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112665851742011954630490917 21124847201627241493217047)
    ·
      refine ⟨31687270802440862239825571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21124847201627241493217047 31687270802440862239825571)
      ·
        refine ⟨47530906203661293359738357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31687270802440862239825571 47530906203661293359738357)
        ·
          refine ⟨4456022456593246252475471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47530906203661293359738357 4456022456593246252475471)
          ·
            refine ⟨6684033684889869378713207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4456022456593246252475471 6684033684889869378713207)
            ·
              refine ⟨10026050527334804068069811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6684033684889869378713207 10026050527334804068069811)
              ·
                refine ⟨15039075791002206102104717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10026050527334804068069811 15039075791002206102104717)
                ·
                  refine ⟨5639653421625827288289269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15039075791002206102104717 5639653421625827288289269)
                  ·
                    refine ⟨528717508277421308277119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5639653421625827288289269 528717508277421308277119)
                    ·
                      rfl

theorem cell23_3089021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_3089021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089021 prefixEnd_3089021 := by exact prefixLift 3089021
  have htrace : WordTrace (prefixWord ++ tailWord_3089021) baseStart_3089021 baseEnd_3089021 := by
    simpa [prefixWord, tailWord_3089021, baseEnd_3089021] using wordTrace_append hprefix tailTrace_3089021
  have hstable : (prefixWord ++ tailWord_3089021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089021).length < 2 ^ (prefixWord ++ tailWord_3089021).sum := by decide
  have hdescent : baseEnd_3089021 < baseStart_3089021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089028 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 2, 3, 2]
def baseStart_3089028 : Nat := 118140960795 + 3089028 * 2 ^ 59
def prefixEnd_3089028 : Nat := 4983230072969 + 3 ^ 40 * 3089028 * 2
def baseEnd_3089028 : Nat := 1586156119196845397443825

theorem tailTrace_3089028 : CollatzResearch.WordTrace tailWord_3089028 prefixEnd_3089028 1586156119196845397443825 := by
  unfold tailWord_3089028
  simp only [CollatzResearch.WordTrace]
  refine ⟨56333053526493297412997869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75110738035324396550663825 56333053526493297412997869)
  ·
    refine ⟨21124895072434986529874201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56333053526493297412997869 21124895072434986529874201)
    ·
      refine ⟨15843671304326239897405651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21124895072434986529874201 15843671304326239897405651)
      ·
        refine ⟨23765506956489359846108477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15843671304326239897405651 23765506956489359846108477)
        ·
          refine ⟨8912065108683509942290679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23765506956489359846108477 8912065108683509942290679)
          ·
            refine ⟨13368097663025264913436019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8912065108683509942290679 13368097663025264913436019)
            ·
              refine ⟨20052146494537897370154029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13368097663025264913436019 20052146494537897370154029)
              ·
                refine ⟨7519554935451711513807761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20052146494537897370154029 7519554935451711513807761)
                ·
                  refine ⟨5639666201588783635355821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7519554935451711513807761 5639666201588783635355821)
                  ·
                    refine ⟨2114874825595793863258433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5639666201588783635355821 2114874825595793863258433)
                    ·
                      refine ⟨1586156119196845397443825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2114874825595793863258433 1586156119196845397443825)
                      ·
                        rfl

theorem cell23_3089028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_3089028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089028 prefixEnd_3089028 := by exact prefixLift 3089028
  have htrace : WordTrace (prefixWord ++ tailWord_3089028) baseStart_3089028 baseEnd_3089028 := by
    simpa [prefixWord, tailWord_3089028, baseEnd_3089028] using wordTrace_append hprefix tailTrace_3089028
  have hstable : (prefixWord ++ tailWord_3089028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089028).length < 2 ^ (prefixWord ++ tailWord_3089028).sum := by decide
  have hdescent : baseEnd_3089028 < baseStart_3089028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089038 : List Nat := [4, 1, 1, 3, 1, 1, 5, 1, 1, 5]
def baseStart_3089038 : Nat := 118140960795 + 3089038 * 2 ^ 59
def prefixEnd_3089038 : Nat := 4983230072969 + 3 ^ 40 * 3089038 * 2
def baseEnd_3089038 : Nat := 528720418001130119439593

theorem tailTrace_3089038 : CollatzResearch.WordTrace tailWord_3089038 prefixEnd_3089038 528720418001130119439593 := by
  unfold tailWord_3089038
  simp only [CollatzResearch.WordTrace]
  refine ⟨14083308972868795816732471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75110981188633577689239845 14083308972868795816732471)
  ·
    refine ⟨21124963459303193725098707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14083308972868795816732471 21124963459303193725098707)
    ·
      refine ⟨31687445188954790587648061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21124963459303193725098707 31687445188954790587648061)
      ·
        refine ⟨11882791945858046470368023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31687445188954790587648061 11882791945858046470368023)
        ·
          refine ⟨17824187918787069705552035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11882791945858046470368023 17824187918787069705552035)
          ·
            refine ⟨26736281878180604558328053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17824187918787069705552035 26736281878180604558328053)
            ·
              refine ⟨2506526426079431677343255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26736281878180604558328053 2506526426079431677343255)
              ·
                refine ⟨3759789639119147516014883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2506526426079431677343255 3759789639119147516014883)
                ·
                  refine ⟨5639684458678721274022325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759789639119147516014883 5639684458678721274022325)
                  ·
                    refine ⟨528720418001130119439593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5639684458678721274022325 528720418001130119439593)
                    ·
                      rfl

theorem cell23_3089038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_3089038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089038 prefixEnd_3089038 := by exact prefixLift 3089038
  have htrace : WordTrace (prefixWord ++ tailWord_3089038) baseStart_3089038 baseEnd_3089038 := by
    simpa [prefixWord, tailWord_3089038, baseEnd_3089038] using wordTrace_append hprefix tailTrace_3089038
  have hstable : (prefixWord ++ tailWord_3089038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089038).length < 2 ^ (prefixWord ++ tailWord_3089038).sum := by decide
  have hdescent : baseEnd_3089038 < baseStart_3089038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089052 : List Nat := [2, 2, 3, 2, 2, 1, 4, 2, 1, 1, 3]
def baseStart_3089052 : Nat := 118140960795 + 3089052 * 2 ^ 59
def prefixEnd_3089052 : Nat := 4983230072969 + 3 ^ 40 * 3089052 * 2
def baseEnd_3089052 : Nat := 1586168442732553303543715

theorem tailTrace_3089052 : CollatzResearch.WordTrace tailWord_3089052 prefixEnd_3089052 1586168442732553303543715 := by
  unfold tailWord_3089052
  simp only [CollatzResearch.WordTrace]
  refine ⟨56333491202449823462434705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75111321603266431283246273 56333491202449823462434705)
  ·
    refine ⟨42250118401837367596826029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56333491202449823462434705 42250118401837367596826029)
    ·
      refine ⟨15843794400689012848809761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42250118401837367596826029 15843794400689012848809761)
      ·
        refine ⟨11882845800516759636607321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15843794400689012848809761 11882845800516759636607321)
        ·
          refine ⟨8912134350387569727455491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11882845800516759636607321 8912134350387569727455491)
          ·
            refine ⟨13368201525581354591183237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8912134350387569727455491 13368201525581354591183237)
            ·
              refine ⟨2506537786046503985846857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13368201525581354591183237 2506537786046503985846857)
              ·
                refine ⟨1879903339534877989385143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2506537786046503985846857 1879903339534877989385143)
                ·
                  refine ⟨2819855009302316984077715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879903339534877989385143 2819855009302316984077715)
                  ·
                    refine ⟨4229782513953475476116573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2819855009302316984077715 4229782513953475476116573)
                    ·
                      refine ⟨1586168442732553303543715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4229782513953475476116573 1586168442732553303543715)
                      ·
                        rfl

theorem cell23_3089052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_3089052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089052 prefixEnd_3089052 := by exact prefixLift 3089052
  have htrace : WordTrace (prefixWord ++ tailWord_3089052) baseStart_3089052 baseEnd_3089052 := by
    simpa [prefixWord, tailWord_3089052, baseEnd_3089052] using wordTrace_append hprefix tailTrace_3089052
  have hstable : (prefixWord ++ tailWord_3089052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089052).length < 2 ^ (prefixWord ++ tailWord_3089052).sum := by decide
  have hdescent : baseEnd_3089052 < baseStart_3089052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089071 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 4]
def baseStart_3089071 : Nat := 118140960795 + 3089071 * 2 ^ 59
def prefixEnd_3089071 : Nat := 4983230072969 + 3 ^ 40 * 3089071 * 2
def baseEnd_3089071 : Nat := 1586178198864988729206127

theorem tailTrace_3089071 : CollatzResearch.WordTrace tailWord_3089071 prefixEnd_3089071 1586178198864988729206127 := by
  unfold tailWord_3089071
  simp only [CollatzResearch.WordTrace]
  refine ⟨112667675391830813169811067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75111783594553875446540711 112667675391830813169811067)
  ·
    refine ⟨169001513087746219754716601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112667675391830813169811067 169001513087746219754716601)
    ·
      refine ⟨126751134815809664816037451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169001513087746219754716601 126751134815809664816037451)
      ·
        refine ⟨190126702223714497224056177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126751134815809664816037451 190126702223714497224056177)
        ·
          refine ⟨142595026667785872918042133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190126702223714497224056177 142595026667785872918042133)
          ·
            refine ⟨6684141875052462793033225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142595026667785872918042133 6684141875052462793033225)
            ·
              refine ⟨5013106406289347094774919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6684141875052462793033225 5013106406289347094774919)
              ·
                refine ⟨7519659609434020642162379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5013106406289347094774919 7519659609434020642162379)
                ·
                  refine ⟨11279489414151030963243569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7519659609434020642162379 11279489414151030963243569)
                  ·
                    refine ⟨8459617060613273222432677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11279489414151030963243569 8459617060613273222432677)
                    ·
                      refine ⟨1586178198864988729206127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8459617060613273222432677 1586178198864988729206127)
                      ·
                        rfl

theorem cell23_3089071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 4].length) (baseStart_3089071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089071 prefixEnd_3089071 := by exact prefixLift 3089071
  have htrace : WordTrace (prefixWord ++ tailWord_3089071) baseStart_3089071 baseEnd_3089071 := by
    simpa [prefixWord, tailWord_3089071, baseEnd_3089071] using wordTrace_append hprefix tailTrace_3089071
  have hstable : (prefixWord ++ tailWord_3089071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089071).length < 2 ^ (prefixWord ++ tailWord_3089071).sum := by decide
  have hdescent : baseEnd_3089071 < baseStart_3089071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089089 : List Nat := [1, 2, 6, 2, 2, 1, 2, 1, 1, 5]
def baseStart_3089089 : Nat := 118140960795 + 3089089 * 2 ^ 59
def prefixEnd_3089089 : Nat := 4983230072969 + 3 ^ 40 * 3089089 * 2
def baseEnd_3089089 : Nat := 528729147172256552927015

theorem tailTrace_3089089 : CollatzResearch.WordTrace tailWord_3089089 prefixEnd_3089089 528729147172256552927015 := by
  unfold tailWord_3089089
  simp only [CollatzResearch.WordTrace]
  refine ⟨112668331905765602243966321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75112221270510401495977547 112668331905765602243966321)
  ·
    refine ⟨84501248929324201682974741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112668331905765602243966321 84501248929324201682974741)
    ·
      refine ⟨3960996043562071953889441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 84501248929324201682974741 3960996043562071953889441)
      ·
        refine ⟨2970747032671553965417081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3960996043562071953889441 2970747032671553965417081)
        ·
          refine ⟨2228060274503665474062811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2970747032671553965417081 2228060274503665474062811)
          ·
            refine ⟨3342090411755498211094217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2228060274503665474062811 3342090411755498211094217)
            ·
              refine ⟨2506567808816623658320663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3342090411755498211094217 2506567808816623658320663)
              ·
                refine ⟨3759851713224935487480995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2506567808816623658320663 3759851713224935487480995)
                ·
                  refine ⟨5639777569837403231221493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759851713224935487480995 5639777569837403231221493)
                  ·
                    refine ⟨528729147172256552927015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5639777569837403231221493 528729147172256552927015)
                    ·
                      rfl

theorem cell23_3089089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_3089089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089089 prefixEnd_3089089 := by exact prefixLift 3089089
  have htrace : WordTrace (prefixWord ++ tailWord_3089089) baseStart_3089089 baseEnd_3089089 := by
    simpa [prefixWord, tailWord_3089089, baseEnd_3089089] using wordTrace_append hprefix tailTrace_3089089
  have hstable : (prefixWord ++ tailWord_3089089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089089).length < 2 ^ (prefixWord ++ tailWord_3089089).sum := by decide
  have hdescent : baseEnd_3089089 < baseStart_3089089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089092 : List Nat := [2, 3, 3, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_3089092 : Nat := 118140960795 + 3089092 * 2 ^ 59
def prefixEnd_3089092 : Nat := 4983230072969 + 3 ^ 40 * 3089092 * 2
def baseEnd_3089092 : Nat := 1586188981958733147043531

theorem tailTrace_3089092 : CollatzResearch.WordTrace tailWord_3089092 prefixEnd_3089092 1586188981958733147043531 := by
  unfold tailWord_3089092
  simp only [CollatzResearch.WordTrace]
  refine ⟨56334220662377366878162765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75112294216503155837550353 56334220662377366878162765)
  ·
    refine ⟨21125332748391512579311037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56334220662377366878162765 21125332748391512579311037)
    ·
      refine ⟨7921999780646817217241639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21125332748391512579311037 7921999780646817217241639)
      ·
        refine ⟨11882999670970225825862459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7921999780646817217241639 11882999670970225825862459)
        ·
          refine ⟨17824499506455338738793689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11882999670970225825862459 17824499506455338738793689)
          ·
            refine ⟨13368374629841504054095267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17824499506455338738793689 13368374629841504054095267)
            ·
              refine ⟨20052561944762256081142901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13368374629841504054095267 20052561944762256081142901)
              ·
                refine ⟨1879927682321461507607147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20052561944762256081142901 1879927682321461507607147)
                ·
                  refine ⟨2819891523482192261410721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879927682321461507607147 2819891523482192261410721)
                  ·
                    refine ⟨2114918642611644196058041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2819891523482192261410721 2114918642611644196058041)
                    ·
                      refine ⟨1586188981958733147043531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2114918642611644196058041 1586188981958733147043531)
                      ·
                        rfl

theorem cell23_3089092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_3089092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089092 prefixEnd_3089092 := by exact prefixLift 3089092
  have htrace : WordTrace (prefixWord ++ tailWord_3089092) baseStart_3089092 baseEnd_3089092 := by
    simpa [prefixWord, tailWord_3089092, baseEnd_3089092] using wordTrace_append hprefix tailTrace_3089092
  have hstable : (prefixWord ++ tailWord_3089092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089092).length < 2 ^ (prefixWord ++ tailWord_3089092).sum := by decide
  have hdescent : baseEnd_3089092 < baseStart_3089092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089135 : List Nat := [1, 1, 2, 1, 5, 3, 2, 2, 1, 3, 2]
def baseStart_3089135 : Nat := 118140960795 + 3089135 * 2 ^ 59
def prefixEnd_3089135 : Nat := 4983230072969 + 3 ^ 40 * 3089135 * 2
def baseEnd_3089135 : Nat := 1586211061626876478805833

theorem tailTrace_3089135 : CollatzResearch.WordTrace tailWord_3089135 prefixEnd_3089135 1586211061626876478805833 := by
  unfold tailWord_3089135
  simp only [CollatzResearch.WordTrace]
  refine ⟨112670009663598952100140859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75113339775732634733427239 112670009663598952100140859)
  ·
    refine ⟨169005014495398428150211289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112670009663598952100140859 169005014495398428150211289)
    ·
      refine ⟨126753760871548821112658467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169005014495398428150211289 126753760871548821112658467)
      ·
        refine ⟨190130641307323231668987701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126753760871548821112658467 190130641307323231668987701)
        ·
          refine ⟨17824747622561552968967597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190130641307323231668987701 17824747622561552968967597)
          ·
            refine ⟨6684280358460582363362849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17824747622561552968967597 6684280358460582363362849)
            ·
              refine ⟨5013210268845436772522137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6684280358460582363362849 5013210268845436772522137)
              ·
                refine ⟨3759907701634077579391603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5013210268845436772522137 3759907701634077579391603)
                ·
                  refine ⟨5639861552451116369087405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759907701634077579391603 5639861552451116369087405)
                  ·
                    refine ⟨2114948082169168638407777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5639861552451116369087405 2114948082169168638407777)
                    ·
                      refine ⟨1586211061626876478805833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2114948082169168638407777 1586211061626876478805833)
                      ·
                        rfl

theorem cell23_3089135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 3, 2].length) (baseStart_3089135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089135 prefixEnd_3089135 := by exact prefixLift 3089135
  have htrace : WordTrace (prefixWord ++ tailWord_3089135) baseStart_3089135 baseEnd_3089135 := by
    simpa [prefixWord, tailWord_3089135, baseEnd_3089135] using wordTrace_append hprefix tailTrace_3089135
  have hstable : (prefixWord ++ tailWord_3089135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089135).length < 2 ^ (prefixWord ++ tailWord_3089135).sum := by decide
  have hdescent : baseEnd_3089135 < baseStart_3089135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089164 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_3089164 : Nat := 118140960795 + 3089164 * 2 ^ 59
def prefixEnd_3089164 : Nat := 4983230072969 + 3 ^ 40 * 3089164 * 2
def baseEnd_3089164 : Nat := 1586225952565856865343199

theorem tailTrace_3089164 : CollatzResearch.WordTrace tailWord_3089164 prefixEnd_3089164 1586225952565856865343199 := by
  unfold tailWord_3089164
  simp only [CollatzResearch.WordTrace]
  refine ⟨56335533690246945026473273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75114044920329260035297697 56335533690246945026473273)
  ·
    refine ⟨42251650267685208769854955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56335533690246945026473273 42251650267685208769854955)
    ·
      refine ⟨63377475401527813154782433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42251650267685208769854955 63377475401527813154782433)
      ·
        refine ⟨47533106551145859866086825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63377475401527813154782433 47533106551145859866086825)
        ·
          refine ⟨35649829913359394899565119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47533106551145859866086825 35649829913359394899565119)
          ·
            refine ⟨53474744870039092349347679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35649829913359394899565119 53474744870039092349347679)
            ·
              refine ⟨80212117305058638524021519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53474744870039092349347679 80212117305058638524021519)
              ·
                refine ⟨120318175957587957786032279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80212117305058638524021519 120318175957587957786032279)
                ·
                  refine ⟨180477263936381936679048419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120318175957587957786032279 180477263936381936679048419)
                  ·
                    refine ⟨270715895904572905018572629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 180477263936381936679048419 270715895904572905018572629)
                    ·
                      refine ⟨1586225952565856865343199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 270715895904572905018572629 1586225952565856865343199)
                      ·
                        rfl

theorem cell23_3089164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_3089164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089164 prefixEnd_3089164 := by exact prefixLift 3089164
  have htrace : WordTrace (prefixWord ++ tailWord_3089164) baseStart_3089164 baseEnd_3089164 := by
    simpa [prefixWord, tailWord_3089164, baseEnd_3089164] using wordTrace_append hprefix tailTrace_3089164
  have hstable : (prefixWord ++ tailWord_3089164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089164).length < 2 ^ (prefixWord ++ tailWord_3089164).sum := by decide
  have hdescent : baseEnd_3089164 < baseStart_3089164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089221 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 4, 1, 4]
def baseStart_3089221 : Nat := 118140960795 + 3089221 * 2 ^ 59
def prefixEnd_3089221 : Nat := 4983230072969 + 3 ^ 40 * 3089221 * 2
def baseEnd_3089221 : Nat := 1586255220963163142330437

theorem tailTrace_3089221 : CollatzResearch.WordTrace tailWord_3089221 prefixEnd_3089221 1586255220963163142330437 := by
  unfold tailWord_3089221
  simp only [CollatzResearch.WordTrace]
  refine ⟨112673146341287388787771517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75115430894191592525181011 112673146341287388787771517)
  ·
    refine ⟨42252429877982770795414319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112673146341287388787771517 42252429877982770795414319)
    ·
      refine ⟨63378644816974156193121479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42252429877982770795414319 63378644816974156193121479)
      ·
        refine ⟨95067967225461234289682219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63378644816974156193121479 95067967225461234289682219)
        ·
          refine ⟨142601950838191851434523329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95067967225461234289682219 142601950838191851434523329)
          ·
            refine ⟨106951463128643888575892497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142601950838191851434523329 106951463128643888575892497)
            ·
              refine ⟨80213597346482916431919373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106951463128643888575892497 80213597346482916431919373)
              ·
                refine ⟨30080099004931093661969765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80213597346482916431919373 30080099004931093661969765)
                ·
                  refine ⟨5640018563424580061619331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30080099004931093661969765 5640018563424580061619331)
                  ·
                    refine ⟨8460027845136870092428997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5640018563424580061619331 8460027845136870092428997)
                    ·
                      refine ⟨1586255220963163142330437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8460027845136870092428997 1586255220963163142330437)
                      ·
                        rfl

theorem cell23_3089221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_3089221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089221 prefixEnd_3089221 := by exact prefixLift 3089221
  have htrace : WordTrace (prefixWord ++ tailWord_3089221) baseStart_3089221 baseEnd_3089221 := by
    simpa [prefixWord, tailWord_3089221, baseEnd_3089221] using wordTrace_append hprefix tailTrace_3089221
  have hstable : (prefixWord ++ tailWord_3089221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089221).length < 2 ^ (prefixWord ++ tailWord_3089221).sum := by decide
  have hdescent : baseEnd_3089221 < baseStart_3089221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089231 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 9, 4]
def baseStart_3089231 : Nat := 118140960795 + 3089231 * 2 ^ 59
def prefixEnd_3089231 : Nat := 4983230072969 + 3 ^ 40 * 3089231 * 2
def baseEnd_3089231 : Nat := 528753451923236034401797

theorem tailTrace_3089231 : CollatzResearch.WordTrace tailWord_3089231 prefixEnd_3089231 528753451923236034401797 := by
  unfold tailWord_3089231
  simp only [CollatzResearch.WordTrace]
  refine ⟨112673511071251160495635547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75115674047500773663757031 112673511071251160495635547)
  ·
    refine ⟨169010266606876740743453321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112673511071251160495635547 169010266606876740743453321)
    ·
      refine ⟨126757699955157555557589991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169010266606876740743453321 126757699955157555557589991)
      ·
        refine ⟨190136549932736333336384987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126757699955157555557589991 190136549932736333336384987)
        ·
          refine ⟨285204824899104500004577481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190136549932736333336384987 285204824899104500004577481)
          ·
            refine ⟨213903618674328375003433111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285204824899104500004577481 213903618674328375003433111)
            ·
              refine ⟨320855428011492562505149667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213903618674328375003433111 320855428011492562505149667)
              ·
                refine ⟨481283142017238843757724501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320855428011492562505149667 481283142017238843757724501)
                ·
                  refine ⟨2820018410257258850142917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 481283142017238843757724501 2820018410257258850142917)
                  ·
                    refine ⟨528753451923236034401797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2820018410257258850142917 528753451923236034401797)
                    ·
                      rfl

theorem cell23_3089231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 4].length) (baseStart_3089231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089231 prefixEnd_3089231 := by exact prefixLift 3089231
  have htrace : WordTrace (prefixWord ++ tailWord_3089231) baseStart_3089231 baseEnd_3089231 := by
    simpa [prefixWord, tailWord_3089231, baseEnd_3089231] using wordTrace_append hprefix tailTrace_3089231
  have hstable : (prefixWord ++ tailWord_3089231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089231).length < 2 ^ (prefixWord ++ tailWord_3089231).sum := by decide
  have hdescent : baseEnd_3089231 < baseStart_3089231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089248 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 3, 4]
def baseStart_3089248 : Nat := 118140960795 + 3089248 * 2 ^ 59
def prefixEnd_3089248 : Nat := 4983230072969 + 3 ^ 40 * 3089248 * 2
def baseEnd_3089248 : Nat := 528756361646944845564271

theorem tailTrace_3089248 : CollatzResearch.WordTrace tailWord_3089248 prefixEnd_3089248 528756361646944845564271 := by
  unfold tailWord_3089248
  simp only [CollatzResearch.WordTrace]
  refine ⟨56337065556094786199502199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75116087408126381599336265 56337065556094786199502199)
  ·
    refine ⟨84505598334142179299253299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56337065556094786199502199 84505598334142179299253299)
    ·
      refine ⟨126758397501213268948879949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84505598334142179299253299 126758397501213268948879949)
      ·
        refine ⟨47534399062954975855829981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126758397501213268948879949 47534399062954975855829981)
        ·
          refine ⟨17825399648608115945936243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47534399062954975855829981 17825399648608115945936243)
          ·
            refine ⟨26738099472912173918904365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17825399648608115945936243 26738099472912173918904365)
            ·
              refine ⟨10026787302342065219589137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26738099472912173918904365 10026787302342065219589137)
              ·
                refine ⟨7520090476756548914691853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10026787302342065219589137 7520090476756548914691853)
                ·
                  refine ⟨2820033928783705843009445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7520090476756548914691853 2820033928783705843009445)
                  ·
                    refine ⟨528756361646944845564271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2820033928783705843009445 528756361646944845564271)
                    ·
                      rfl

theorem cell23_3089248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 3, 4].length) (baseStart_3089248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089248 prefixEnd_3089248 := by exact prefixLift 3089248
  have htrace : WordTrace (prefixWord ++ tailWord_3089248) baseStart_3089248 baseEnd_3089248 := by
    simpa [prefixWord, tailWord_3089248, baseEnd_3089248] using wordTrace_append hprefix tailTrace_3089248
  have hstable : (prefixWord ++ tailWord_3089248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089248).length < 2 ^ (prefixWord ++ tailWord_3089248).sum := by decide
  have hdescent : baseEnd_3089248 < baseStart_3089248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089255 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_3089255 : Nat := 118140960795 + 3089255 * 2 ^ 59
def prefixEnd_3089255 : Nat := 4983230072969 + 3 ^ 40 * 3089255 * 2
def baseEnd_3089255 : Nat := 1586272679305416009305281

theorem tailTrace_3089255 : CollatzResearch.WordTrace tailWord_3089255 prefixEnd_3089255 1586272679305416009305281 := by
  unfold tailWord_3089255
  simp only [CollatzResearch.WordTrace]
  refine ⟨112674386423164212594509219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75116257615442808396339479 112674386423164212594509219)
  ·
    refine ⟨169011579634746318891763829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112674386423164212594509219 169011579634746318891763829)
    ·
      refine ⟨15844835590757467396102859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169011579634746318891763829 15844835590757467396102859)
      ·
        refine ⟨23767253386136201094154289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15844835590757467396102859 23767253386136201094154289)
        ·
          refine ⟨17825440039602150820615717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23767253386136201094154289 17825440039602150820615717)
          ·
            refine ⟨3342270007425403278865447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17825440039602150820615717 3342270007425403278865447)
            ·
              refine ⟨5013405011138104918298171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3342270007425403278865447 5013405011138104918298171)
              ·
                refine ⟨7520107516707157377447257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5013405011138104918298171 7520107516707157377447257)
                ·
                  refine ⟨5640080637530368033085443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7520107516707157377447257 5640080637530368033085443)
                  ·
                    refine ⟨8460120956295552049628165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5640080637530368033085443 8460120956295552049628165)
                    ·
                      refine ⟨1586272679305416009305281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8460120956295552049628165 1586272679305416009305281)
                      ·
                        rfl

theorem cell23_3089255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_3089255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089255 prefixEnd_3089255 := by exact prefixLift 3089255
  have htrace : WordTrace (prefixWord ++ tailWord_3089255) baseStart_3089255 baseEnd_3089255 := by
    simpa [prefixWord, tailWord_3089255, baseEnd_3089255] using wordTrace_append hprefix tailTrace_3089255
  have hstable : (prefixWord ++ tailWord_3089255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089255).length < 2 ^ (prefixWord ++ tailWord_3089255).sum := by decide
  have hdescent : baseEnd_3089255 < baseStart_3089255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089261 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 8]
def baseStart_3089261 : Nat := 118140960795 + 3089261 * 2 ^ 59
def prefixEnd_3089261 : Nat := 4983230072969 + 3 ^ 40 * 3089261 * 2
def baseEnd_3089261 : Nat := 176252862243260331758917

theorem tailTrace_3089261 : CollatzResearch.WordTrace tailWord_3089261 prefixEnd_3089261 176252862243260331758917 := by
  unfold tailWord_3089261
  simp only [CollatzResearch.WordTrace]
  refine ⟨112674605261142475619227637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75116403507428317079485091 112674605261142475619227637)
  ·
    refine ⟨10563244243232107089302591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112674605261142475619227637 10563244243232107089302591)
    ·
      refine ⟨15844866364848160633953887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10563244243232107089302591 15844866364848160633953887)
      ·
        refine ⟨23767299547272240950930831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15844866364848160633953887 23767299547272240950930831)
        ·
          refine ⟨35650949320908361426396247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23767299547272240950930831 35650949320908361426396247)
          ·
            refine ⟨53476423981362542139594371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35650949320908361426396247 53476423981362542139594371)
            ·
              refine ⟨80214635972043813209391557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53476423981362542139594371 80214635972043813209391557)
              ·
                refine ⟨15040244244758214976760917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80214635972043813209391557 15040244244758214976760917)
                ·
                  refine ⟨176252862243260331758917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15040244244758214976760917 176252862243260331758917)
                  ·
                    rfl

theorem cell23_3089261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_3089261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089261 prefixEnd_3089261 := by exact prefixLift 3089261
  have htrace : WordTrace (prefixWord ++ tailWord_3089261) baseStart_3089261 baseEnd_3089261 := by
    simpa [prefixWord, tailWord_3089261, baseEnd_3089261] using wordTrace_append hprefix tailTrace_3089261
  have hstable : (prefixWord ++ tailWord_3089261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089261).length < 2 ^ (prefixWord ++ tailWord_3089261).sum := by decide
  have hdescent : baseEnd_3089261 < baseStart_3089261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089265 : List Nat := [1, 2, 2, 2, 1, 4, 1, 5, 1, 4]
def baseStart_3089265 : Nat := 118140960795 + 3089265 * 2 ^ 59
def prefixEnd_3089265 : Nat := 4983230072969 + 3 ^ 40 * 3089265 * 2
def baseEnd_3089265 : Nat := 528759271370653656726745

theorem tailTrace_3089265 : CollatzResearch.WordTrace tailWord_3089265 prefixEnd_3089265 528759271370653656726745 := by
  unfold tailWord_3089265
  simp only [CollatzResearch.WordTrace]
  refine ⟨112674751153127984302373249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75116500768751989534915499 112674751153127984302373249)
  ·
    refine ⟨84506063364845988226779937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112674751153127984302373249 84506063364845988226779937)
    ·
      refine ⟨63379547523634491170084953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84506063364845988226779937 63379547523634491170084953)
      ·
        refine ⟨47534660642725868377563715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63379547523634491170084953 47534660642725868377563715)
        ·
          refine ⟨71301990964088802566345573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47534660642725868377563715 71301990964088802566345573)
          ·
            refine ⟨13369123305766650481189795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71301990964088802566345573 13369123305766650481189795)
            ·
              refine ⟨20053684958649975721784693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13369123305766650481189795 20053684958649975721784693)
              ·
                refine ⟨1880032964873435223917315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20053684958649975721784693 1880032964873435223917315)
                ·
                  refine ⟨2820049447310152835875973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880032964873435223917315 2820049447310152835875973)
                  ·
                    refine ⟨528759271370653656726745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2820049447310152835875973 528759271370653656726745)
                    ·
                      rfl

theorem cell23_3089265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_3089265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089265 prefixEnd_3089265 := by exact prefixLift 3089265
  have htrace : WordTrace (prefixWord ++ tailWord_3089265) baseStart_3089265 baseEnd_3089265 := by
    simpa [prefixWord, tailWord_3089265, baseEnd_3089265] using wordTrace_append hprefix tailTrace_3089265
  have hstable : (prefixWord ++ tailWord_3089265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089265).length < 2 ^ (prefixWord ++ tailWord_3089265).sum := by decide
  have hdescent : baseEnd_3089265 < baseStart_3089265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089271 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 3]
def baseStart_3089271 : Nat := 118140960795 + 3089271 * 2 ^ 59
def prefixEnd_3089271 : Nat := 4983230072969 + 3 ^ 40 * 3089271 * 2
def baseEnd_3089271 : Nat := 1586280894995887946705207

theorem tailTrace_3089271 : CollatzResearch.WordTrace tailWord_3089271 prefixEnd_3089271 1586280894995887946705207 := by
  unfold tailWord_3089271
  simp only [CollatzResearch.WordTrace]
  refine ⟨112674969991106247327091667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75116646660737498218061111 112674969991106247327091667)
  ·
    refine ⟨169012454986659370990637501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112674969991106247327091667 169012454986659370990637501)
    ·
      refine ⟨63379670619997264121489063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169012454986659370990637501 63379670619997264121489063)
      ·
        refine ⟨95069505929995896182233595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63379670619997264121489063 95069505929995896182233595)
        ·
          refine ⟨142604258894993844273350393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95069505929995896182233595 142604258894993844273350393)
          ·
            refine ⟨106953194171245383205012795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142604258894993844273350393 106953194171245383205012795)
            ·
              refine ⟨160429791256868074807519193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106953194171245383205012795 160429791256868074807519193)
              ·
                refine ⟨120322343442651056105639395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160429791256868074807519193 120322343442651056105639395)
                ·
                  refine ⟨180483515163976584158459093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120322343442651056105639395 180483515163976584158459093)
                  ·
                    refine ⟨4230082386655701191213885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 180483515163976584158459093 4230082386655701191213885)
                    ·
                      refine ⟨1586280894995887946705207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4230082386655701191213885 1586280894995887946705207)
                      ·
                        rfl

theorem cell23_3089271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_3089271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089271 prefixEnd_3089271 := by exact prefixLift 3089271
  have htrace : WordTrace (prefixWord ++ tailWord_3089271) baseStart_3089271 baseEnd_3089271 := by
    simpa [prefixWord, tailWord_3089271, baseEnd_3089271] using wordTrace_append hprefix tailTrace_3089271
  have hstable : (prefixWord ++ tailWord_3089271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089271).length < 2 ^ (prefixWord ++ tailWord_3089271).sum := by decide
  have hdescent : baseEnd_3089271 < baseStart_3089271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089291 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 5, 5]
def baseStart_3089291 : Nat := 118140960795 + 3089291 * 2 ^ 59
def prefixEnd_3089291 : Nat := 4983230072969 + 3 ^ 40 * 3089291 * 2
def baseEnd_3089291 : Nat := 528763721536325956151705

theorem tailTrace_3089291 : CollatzResearch.WordTrace tailWord_3089291 prefixEnd_3089291 528763721536325956151705 := by
  unfold tailWord_3089291
  simp only [CollatzResearch.WordTrace]
  refine ⟨112675699451033790742819727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75117132967355860495213151 112675699451033790742819727)
  ·
    refine ⟨169013549176550686114229591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112675699451033790742819727 169013549176550686114229591)
    ·
      refine ⟨253520323764826029171344387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169013549176550686114229591 253520323764826029171344387)
      ·
        refine ⟨380280485647239043757016581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253520323764826029171344387 380280485647239043757016581)
        ·
          refine ⟨71302591058857320704440609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 380280485647239043757016581 71302591058857320704440609)
          ·
            refine ⟨53476943294142990528330457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71302591058857320704440609 53476943294142990528330457)
            ·
              refine ⟨40107707470607242896247843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53476943294142990528330457 40107707470607242896247843)
              ·
                refine ⟨60161561205910864344371765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40107707470607242896247843 60161561205910864344371765)
                ·
                  refine ⟨5640146363054143532284853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60161561205910864344371765 5640146363054143532284853)
                  ·
                    refine ⟨528763721536325956151705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5640146363054143532284853 528763721536325956151705)
                    ·
                      rfl

theorem cell23_3089291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 5].length) (baseStart_3089291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089291 prefixEnd_3089291 := by exact prefixLift 3089291
  have htrace : WordTrace (prefixWord ++ tailWord_3089291) baseStart_3089291 baseEnd_3089291 := by
    simpa [prefixWord, tailWord_3089291, baseEnd_3089291] using wordTrace_append hprefix tailTrace_3089291
  have hstable : (prefixWord ++ tailWord_3089291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089291).length < 2 ^ (prefixWord ++ tailWord_3089291).sum := by decide
  have hdescent : baseEnd_3089291 < baseStart_3089291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089321 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 3, 6]
def baseStart_3089321 : Nat := 118140960795 + 3089321 * 2 ^ 59
def prefixEnd_3089321 : Nat := 4983230072969 + 3 ^ 40 * 3089321 * 2
def baseEnd_3089321 : Nat := 528768856342870917026659

theorem tailTrace_3089321 : CollatzResearch.WordTrace tailWord_3089321 prefixEnd_3089321 528768856342870917026659 := by
  unfold tailWord_3089321
  simp only [CollatzResearch.WordTrace]
  refine ⟨112676793640925105866411817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75117862427283403910941211 112676793640925105866411817)
  ·
    refine ⟨84507595230693829399808863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112676793640925105866411817 84507595230693829399808863)
    ·
      refine ⟨126761392846040744099713295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84507595230693829399808863 126761392846040744099713295)
      ·
        refine ⟨190142089269061116149569943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126761392846040744099713295 190142089269061116149569943)
        ·
          refine ⟨285213133903591674224354915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190142089269061116149569943 285213133903591674224354915)
          ·
            refine ⟨427819700855387511336532373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285213133903591674224354915 427819700855387511336532373)
            ·
              refine ⟨20054048477596289593899955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 427819700855387511336532373 20054048477596289593899955)
              ·
                refine ⟨30081072716394434390849933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20054048477596289593899955 30081072716394434390849933)
                ·
                  refine ⟨11280402268647912896568725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30081072716394434390849933 11280402268647912896568725)
                  ·
                    refine ⟨528768856342870917026659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11280402268647912896568725 528768856342870917026659)
                    ·
                      rfl

theorem cell23_3089321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 6].length) (baseStart_3089321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089321 prefixEnd_3089321 := by exact prefixLift 3089321
  have htrace : WordTrace (prefixWord ++ tailWord_3089321) baseStart_3089321 baseEnd_3089321 := by
    simpa [prefixWord, tailWord_3089321, baseEnd_3089321] using wordTrace_append hprefix tailTrace_3089321
  have hstable : (prefixWord ++ tailWord_3089321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089321).length < 2 ^ (prefixWord ++ tailWord_3089321).sum := by decide
  have hdescent : baseEnd_3089321 < baseStart_3089321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089338 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 4, 4]
def baseStart_3089338 : Nat := 118140960795 + 3089338 * 2 ^ 59
def prefixEnd_3089338 : Nat := 4983230072969 + 3 ^ 40 * 3089338 * 2
def baseEnd_3089338 : Nat := 528771766066579728189133

theorem tailTrace_3089338 : CollatzResearch.WordTrace tailWord_3089338 prefixEnd_3089338 528771766066579728189133 := by
  unfold tailWord_3089338
  simp only [CollatzResearch.WordTrace]
  refine ⟨28169353420465879442445167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75118275787909011846520445 28169353420465879442445167)
  ·
    refine ⟨42254030130698819163667751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28169353420465879442445167 42254030130698819163667751)
    ·
      refine ⟨63381045196048228745501627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42254030130698819163667751 63381045196048228745501627)
      ·
        refine ⟨95071567794072343118252441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63381045196048228745501627 95071567794072343118252441)
        ·
          refine ⟨71303675845554257338689331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95071567794072343118252441 71303675845554257338689331)
          ·
            refine ⟨106955513768331386008033997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71303675845554257338689331 106955513768331386008033997)
            ·
              refine ⟨40108317663124269753012749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106955513768331386008033997 40108317663124269753012749)
              ·
                refine ⟨15040619123671601157379781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40108317663124269753012749 15040619123671601157379781)
                ·
                  refine ⟨2820116085688425217008709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15040619123671601157379781 2820116085688425217008709)
                  ·
                    refine ⟨528771766066579728189133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2820116085688425217008709 528771766066579728189133)
                    ·
                      rfl

theorem cell23_3089338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_3089338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089338 prefixEnd_3089338 := by exact prefixLift 3089338
  have htrace : WordTrace (prefixWord ++ tailWord_3089338) baseStart_3089338 baseEnd_3089338 := by
    simpa [prefixWord, tailWord_3089338, baseEnd_3089338] using wordTrace_append hprefix tailTrace_3089338
  have hstable : (prefixWord ++ tailWord_3089338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089338).length < 2 ^ (prefixWord ++ tailWord_3089338).sum := by decide
  have hdescent : baseEnd_3089338 < baseStart_3089338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089351 : List Nat := [1, 1, 4, 1, 1, 2, 3, 10]
def baseStart_3089351 : Nat := 118140960795 + 3089351 * 2 ^ 59
def prefixEnd_3089351 : Nat := 4983230072969 + 3 ^ 40 * 3089351 * 2
def baseEnd_3089351 : Nat := 58752665683268430877957

theorem tailTrace_3089351 : CollatzResearch.WordTrace tailWord_3089351 prefixEnd_3089351 58752665683268430877957 := by
  unfold tailWord_3089351
  simp only [CollatzResearch.WordTrace]
  refine ⟨112677887830816420990003907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75118591887210947326669271 112677887830816420990003907)
  ·
    refine ⟨169016831746224631485005861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112677887830816420990003907 169016831746224631485005861)
    ·
      refine ⟨31690655952417118403438599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169016831746224631485005861 31690655952417118403438599)
      ·
        refine ⟨47535983928625677605157899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31690655952417118403438599 47535983928625677605157899)
        ·
          refine ⟨71303975892938516407736849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47535983928625677605157899 71303975892938516407736849)
          ·
            refine ⟨53477981919703887305802637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71303975892938516407736849 53477981919703887305802637)
            ·
              refine ⟨20054243219888957739675989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53477981919703887305802637 20054243219888957739675989)
              ·
                refine ⟨58752665683268430877957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20054243219888957739675989 58752665683268430877957)
                ·
                  rfl

theorem cell23_3089351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 10].length) (baseStart_3089351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089351 prefixEnd_3089351 := by exact prefixLift 3089351
  have htrace : WordTrace (prefixWord ++ tailWord_3089351) baseStart_3089351 baseEnd_3089351 := by
    simpa [prefixWord, tailWord_3089351, baseEnd_3089351] using wordTrace_append hprefix tailTrace_3089351
  have hstable : (prefixWord ++ tailWord_3089351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089351).length < 2 ^ (prefixWord ++ tailWord_3089351).sum := by decide
  have hdescent : baseEnd_3089351 < baseStart_3089351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089355 : List Nat := [1, 1, 1, 1, 3, 6, 1, 3, 2, 4]
def baseStart_3089355 : Nat := 118140960795 + 3089355 * 2 ^ 59
def prefixEnd_3089355 : Nat := 4983230072969 + 3 ^ 40 * 3089355 * 2
def baseEnd_3089355 : Nat := 528774675790288539351607

theorem tailTrace_3089355 : CollatzResearch.WordTrace tailWord_3089355 prefixEnd_3089355 528774675790288539351607 := by
  unfold tailWord_3089355
  simp only [CollatzResearch.WordTrace]
  refine ⟨112678033722801929673149519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75118689148534619782099679 112678033722801929673149519)
  ·
    refine ⟨169017050584202894509724279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112678033722801929673149519 169017050584202894509724279)
    ·
      refine ⟨253525575876304341764586419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169017050584202894509724279 253525575876304341764586419)
      ·
        refine ⟨380288363814456512646879629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253525575876304341764586419 380288363814456512646879629)
        ·
          refine ⟨142608136430421192242579861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380288363814456512646879629 142608136430421192242579861)
          ·
            refine ⟨6684756395175993386370931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142608136430421192242579861 6684756395175993386370931)
            ·
              refine ⟨10027134592763990079556397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6684756395175993386370931 10027134592763990079556397)
              ·
                refine ⟨3760175472286496279833649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10027134592763990079556397 3760175472286496279833649)
                ·
                  refine ⟨2820131604214872209875237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3760175472286496279833649 2820131604214872209875237)
                  ·
                    refine ⟨528774675790288539351607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2820131604214872209875237 528774675790288539351607)
                    ·
                      rfl

theorem cell23_3089355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 4].length) (baseStart_3089355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089355 prefixEnd_3089355 := by exact prefixLift 3089355
  have htrace : WordTrace (prefixWord ++ tailWord_3089355) baseStart_3089355 baseEnd_3089355 := by
    simpa [prefixWord, tailWord_3089355, baseEnd_3089355] using wordTrace_append hprefix tailTrace_3089355
  have hstable : (prefixWord ++ tailWord_3089355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089355).length < 2 ^ (prefixWord ++ tailWord_3089355).sum := by decide
  have hdescent : baseEnd_3089355 < baseStart_3089355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089358 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_3089358 : Nat := 118140960795 + 3089358 * 2 ^ 59
def prefixEnd_3089358 : Nat := 4983230072969 + 3 ^ 40 * 3089358 * 2
def baseEnd_3089358 : Nat := 1586325567812829106317307

theorem tailTrace_3089358 : CollatzResearch.WordTrace tailWord_3089358 prefixEnd_3089358 1586325567812829106317307 := by
  unfold tailWord_3089358
  simp only [CollatzResearch.WordTrace]
  refine ⟨14084767892723882648188591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75118762094527374123672485 14084767892723882648188591)
  ·
    refine ⟨21127151839085823972282887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14084767892723882648188591 21127151839085823972282887)
    ·
      refine ⟨31690727758628735958424331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21127151839085823972282887 31690727758628735958424331)
      ·
        refine ⟨47536091637943103937636497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31690727758628735958424331 47536091637943103937636497)
        ·
          refine ⟨35652068728457327953227373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47536091637943103937636497 35652068728457327953227373)
          ·
            refine ⟨13369525773171497982460265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35652068728457327953227373 13369525773171497982460265)
            ·
              refine ⟨10027144329878623486845199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13369525773171497982460265 10027144329878623486845199)
              ·
                refine ⟨15040716494817935230267799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10027144329878623486845199 15040716494817935230267799)
                ·
                  refine ⟨22561074742226902845401699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15040716494817935230267799 22561074742226902845401699)
                  ·
                    refine ⟨33841612113340354268102549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22561074742226902845401699 33841612113340354268102549)
                    ·
                      refine ⟨1586325567812829106317307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33841612113340354268102549 1586325567812829106317307)
                      ·
                        rfl

theorem cell23_3089358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_3089358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089358 prefixEnd_3089358 := by exact prefixLift 3089358
  have htrace : WordTrace (prefixWord ++ tailWord_3089358) baseStart_3089358 baseEnd_3089358 := by
    simpa [prefixWord, tailWord_3089358, baseEnd_3089358] using wordTrace_append hprefix tailTrace_3089358
  have hstable : (prefixWord ++ tailWord_3089358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089358).length < 2 ^ (prefixWord ++ tailWord_3089358).sum := by decide
  have hdescent : baseEnd_3089358 < baseStart_3089358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089362 : List Nat := [3, 2, 2, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_3089362 : Nat := 118140960795 + 3089362 * 2 ^ 59
def prefixEnd_3089362 : Nat := 4983230072969 + 3 ^ 40 * 3089362 * 2
def baseEnd_3089362 : Nat := 1586327621735447090667289

theorem tailTrace_3089362 : CollatzResearch.WordTrace tailWord_3089362 prefixEnd_3089362 1586327621735447090667289 := by
  unfold tailWord_3089362
  simp only [CollatzResearch.WordTrace]
  refine ⟨28169572258444142467163585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75118859355851046579102893 28169572258444142467163585)
  ·
    refine ⟨21127179193833106850372689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28169572258444142467163585 21127179193833106850372689)
    ·
      refine ⟨15845384395374830137779517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21127179193833106850372689 15845384395374830137779517)
      ·
        refine ⟨5942019148265561301667319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15845384395374830137779517 5942019148265561301667319)
        ·
          refine ⟨8913028722398341952500979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5942019148265561301667319 8913028722398341952500979)
          ·
            refine ⟨13369543083597512928751469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8913028722398341952500979 13369543083597512928751469)
            ·
              refine ⟨5013578656349067348281801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13369543083597512928751469 5013578656349067348281801)
              ·
                refine ⟨3760183992261800511211351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5013578656349067348281801 3760183992261800511211351)
                ·
                  refine ⟨5640275988392700766817027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3760183992261800511211351 5640275988392700766817027)
                  ·
                    refine ⟨8460413982589051150225541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5640275988392700766817027 8460413982589051150225541)
                    ·
                      refine ⟨1586327621735447090667289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8460413982589051150225541 1586327621735447090667289)
                      ·
                        rfl

theorem cell23_3089362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_3089362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089362 prefixEnd_3089362 := by exact prefixLift 3089362
  have htrace : WordTrace (prefixWord ++ tailWord_3089362) baseStart_3089362 baseEnd_3089362 := by
    simpa [prefixWord, tailWord_3089362, baseEnd_3089362] using wordTrace_append hprefix tailTrace_3089362
  have hstable : (prefixWord ++ tailWord_3089362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089362).length < 2 ^ (prefixWord ++ tailWord_3089362).sum := by decide
  have hdescent : baseEnd_3089362 < baseStart_3089362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089375 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 4]
def baseStart_3089375 : Nat := 118140960795 + 3089375 * 2 ^ 59
def prefixEnd_3089375 : Nat := 4983230072969 + 3 ^ 40 * 3089375 * 2
def baseEnd_3089375 : Nat := 1586334296983955539804729

theorem tailTrace_3089375 : CollatzResearch.WordTrace tailWord_3089375 prefixEnd_3089375 1586334296983955539804729 := by
  unfold tailWord_3089375
  simp only [CollatzResearch.WordTrace]
  refine ⟨112678763182729473088877579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75119175455152982059251719 112678763182729473088877579)
  ·
    refine ⟨169018144774094209633316369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112678763182729473088877579 169018144774094209633316369)
    ·
      refine ⟨126763608580570657224987277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169018144774094209633316369 126763608580570657224987277)
      ·
        refine ⟨47536353217713996459370229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126763608580570657224987277 47536353217713996459370229)
        ·
          refine ⟨4456533114160687168065959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47536353217713996459370229 4456533114160687168065959)
          ·
            refine ⟨6684799671241030752098939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4456533114160687168065959 6684799671241030752098939)
            ·
              refine ⟨10027199506861546128148409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6684799671241030752098939 10027199506861546128148409)
              ·
                refine ⟨7520399630146159596111307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10027199506861546128148409 7520399630146159596111307)
                ·
                  refine ⟨11280599445219239394166961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7520399630146159596111307 11280599445219239394166961)
                  ·
                    refine ⟨8460449583914429545625221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11280599445219239394166961 8460449583914429545625221)
                    ·
                      refine ⟨1586334296983955539804729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8460449583914429545625221 1586334296983955539804729)
                      ·
                        rfl

theorem cell23_3089375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_3089375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089375 prefixEnd_3089375 := by exact prefixLift 3089375
  have htrace : WordTrace (prefixWord ++ tailWord_3089375) baseStart_3089375 baseEnd_3089375 := by
    simpa [prefixWord, tailWord_3089375, baseEnd_3089375] using wordTrace_append hprefix tailTrace_3089375
  have hstable : (prefixWord ++ tailWord_3089375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089375).length < 2 ^ (prefixWord ++ tailWord_3089375).sum := by decide
  have hdescent : baseEnd_3089375 < baseStart_3089375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089379 : List Nat := [1, 1, 1, 6, 1, 1, 2, 5, 1, 2, 2]
def baseStart_3089379 : Nat := 118140960795 + 3089379 * 2 ^ 59
def prefixEnd_3089379 : Nat := 4983230072969 + 3 ^ 40 * 3089379 * 2
def baseEnd_3089379 : Nat := 1586336350906573524154711

theorem tailTrace_3089379 : CollatzResearch.WordTrace tailWord_3089379 prefixEnd_3089379 1586336350906573524154711 := by
  unfold tailWord_3089379
  simp only [CollatzResearch.WordTrace]
  refine ⟨112678909074714981772023191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75119272716476654514682127 112678909074714981772023191)
  ·
    refine ⟨169018363612072472658034787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112678909074714981772023191 169018363612072472658034787)
    ·
      refine ⟨253527545418108708987052181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169018363612072472658034787 253527545418108708987052181)
      ·
        refine ⟨11884103691473845733768071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 253527545418108708987052181 11884103691473845733768071)
        ·
          refine ⟨17826155537210768600652107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11884103691473845733768071 17826155537210768600652107)
          ·
            refine ⟨26739233305816152900978161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17826155537210768600652107 26739233305816152900978161)
            ·
              refine ⟨20054424979362114675733621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26739233305816152900978161 20054424979362114675733621)
              ·
                refine ⟨1880102341815198250850027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20054424979362114675733621 1880102341815198250850027)
                ·
                  refine ⟨2820153512722797376275041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880102341815198250850027 2820153512722797376275041)
                  ·
                    refine ⟨2115115134542098032206281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2820153512722797376275041 2115115134542098032206281)
                    ·
                      refine ⟨1586336350906573524154711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115115134542098032206281 1586336350906573524154711)
                      ·
                        rfl

theorem cell23_3089379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_3089379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089379 prefixEnd_3089379 := by exact prefixLift 3089379
  have htrace : WordTrace (prefixWord ++ tailWord_3089379) baseStart_3089379 baseEnd_3089379 := by
    simpa [prefixWord, tailWord_3089379, baseEnd_3089379] using wordTrace_append hprefix tailTrace_3089379
  have hstable : (prefixWord ++ tailWord_3089379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089379).length < 2 ^ (prefixWord ++ tailWord_3089379).sum := by decide
  have hdescent : baseEnd_3089379 < baseStart_3089379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089422 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2]
def baseStart_3089422 : Nat := 118140960795 + 3089422 * 2 ^ 59
def prefixEnd_3089422 : Nat := 4983230072969 + 3 ^ 40 * 3089422 * 2
def baseEnd_3089422 : Nat := 1586358430574716855917013

theorem tailTrace_3089422 : CollatzResearch.WordTrace tailWord_3089422 prefixEnd_3089422 1586358430574716855917013 := by
  unfold tailWord_3089422
  simp only [CollatzResearch.WordTrace]
  refine ⟨14085059676694900014479815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75120318275706133410559013 14085059676694900014479815)
  ·
    refine ⟨21127589515042350021719723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14085059676694900014479815 21127589515042350021719723)
    ·
      refine ⟨31691384272563525032579585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21127589515042350021719723 31691384272563525032579585)
      ·
        refine ⟨23768538204422643774434689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31691384272563525032579585 23768538204422643774434689)
        ·
          refine ⟨17826403653316982830826017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23768538204422643774434689 17826403653316982830826017)
          ·
            refine ⟨13369802739987737123119513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17826403653316982830826017 13369802739987737123119513)
            ·
              refine ⟨10027352054990802842339635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13369802739987737123119513 10027352054990802842339635)
              ·
                refine ⟨15041028082486204263509453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10027352054990802842339635 15041028082486204263509453)
                ·
                  refine ⟨5640385530932326598816045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15041028082486204263509453 5640385530932326598816045)
                  ·
                    refine ⟨2115144574099622474556017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5640385530932326598816045 2115144574099622474556017)
                    ·
                      refine ⟨1586358430574716855917013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115144574099622474556017 1586358430574716855917013)
                      ·
                        rfl

theorem cell23_3089422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_3089422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089422 prefixEnd_3089422 := by exact prefixLift 3089422
  have htrace : WordTrace (prefixWord ++ tailWord_3089422) baseStart_3089422 baseEnd_3089422 := by
    simpa [prefixWord, tailWord_3089422, baseEnd_3089422] using wordTrace_append hprefix tailTrace_3089422
  have hstable : (prefixWord ++ tailWord_3089422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089422).length < 2 ^ (prefixWord ++ tailWord_3089422).sum := by decide
  have hdescent : baseEnd_3089422 < baseStart_3089422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089439 : List Nat := [1, 1, 2, 4, 1, 3, 4, 1, 1, 3, 2]
def baseStart_3089439 : Nat := 118140960795 + 3089439 * 2 ^ 59
def prefixEnd_3089439 : Nat := 4983230072969 + 3 ^ 40 * 3089439 * 2
def baseEnd_3089439 : Nat := 1586367159745843289404435

theorem tailTrace_3089439 : CollatzResearch.WordTrace tailWord_3089439 prefixEnd_3089439 1586367159745843289404435 := by
  unfold tailWord_3089439
  simp only [CollatzResearch.WordTrace]
  refine ⟨112681097454497612019207371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75120731636331741346138247 112681097454497612019207371)
  ·
    refine ⟨169021646181746418028811057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112681097454497612019207371 169021646181746418028811057)
    ·
      refine ⟨126766234636309813521608293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169021646181746418028811057 126766234636309813521608293)
      ·
        refine ⟨23768668994308090035301555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126766234636309813521608293 23768668994308090035301555)
        ·
          refine ⟨35653003491462135052952333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23768668994308090035301555 35653003491462135052952333)
          ·
            refine ⟨13369876309298300644857125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35653003491462135052952333 13369876309298300644857125)
            ·
              refine ⟨2506851807993431370910711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13369876309298300644857125 2506851807993431370910711)
              ·
                refine ⟨3760277711990147056366067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2506851807993431370910711 3760277711990147056366067)
                ·
                  refine ⟨5640416567985220584549101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3760277711990147056366067 5640416567985220584549101)
                  ·
                    refine ⟨2115156212994457719205913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5640416567985220584549101 2115156212994457719205913)
                    ·
                      refine ⟨1586367159745843289404435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115156212994457719205913 1586367159745843289404435)
                      ·
                        rfl

theorem cell23_3089439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_3089439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089439 prefixEnd_3089439 := by exact prefixLift 3089439
  have htrace : WordTrace (prefixWord ++ tailWord_3089439) baseStart_3089439 baseEnd_3089439 := by
    simpa [prefixWord, tailWord_3089439, baseEnd_3089439] using wordTrace_append hprefix tailTrace_3089439
  have hstable : (prefixWord ++ tailWord_3089439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089439).length < 2 ^ (prefixWord ++ tailWord_3089439).sum := by decide
  have hdescent : baseEnd_3089439 < baseStart_3089439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089452 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 4, 2, 2]
def baseStart_3089452 : Nat := 118140960795 + 3089452 * 2 ^ 59
def prefixEnd_3089452 : Nat := 4983230072969 + 3 ^ 40 * 3089452 * 2
def baseEnd_3089452 : Nat := 1586373834994351738541875

theorem tailTrace_3089452 : CollatzResearch.WordTrace tailWord_3089452 prefixEnd_3089452 1586373834994351738541875 := by
  unfold tailWord_3089452
  simp only [CollatzResearch.WordTrace]
  refine ⟨56340785801725257619715305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75121047735633676826287073 56340785801725257619715305)
  ·
    refine ⟨42255589351293943214786479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56340785801725257619715305 42255589351293943214786479)
    ·
      refine ⟨63383384026940914822179719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42255589351293943214786479 63383384026940914822179719)
      ·
        refine ⟨95075076040411372233269579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63383384026940914822179719 95075076040411372233269579)
        ·
          refine ⟨142612614060617058349904369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95075076040411372233269579 142612614060617058349904369)
          ·
            refine ⟨106959460545462793762428277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142612614060617058349904369 106959460545462793762428277)
            ·
              refine ⟨10027449426137136915227651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106959460545462793762428277 10027449426137136915227651)
              ·
                refine ⟨15041174139205705372841477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10027449426137136915227651 15041174139205705372841477)
                ·
                  refine ⟨2820220151101069757407777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15041174139205705372841477 2820220151101069757407777)
                  ·
                    refine ⟨2115165113325802318055833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2820220151101069757407777 2115165113325802318055833)
                    ·
                      refine ⟨1586373834994351738541875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115165113325802318055833 1586373834994351738541875)
                      ·
                        rfl

theorem cell23_3089452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 2, 2].length) (baseStart_3089452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089452 prefixEnd_3089452 := by exact prefixLift 3089452
  have htrace : WordTrace (prefixWord ++ tailWord_3089452) baseStart_3089452 baseEnd_3089452 := by
    simpa [prefixWord, tailWord_3089452, baseEnd_3089452] using wordTrace_append hprefix tailTrace_3089452
  have hstable : (prefixWord ++ tailWord_3089452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089452).length < 2 ^ (prefixWord ++ tailWord_3089452).sum := by decide
  have hdescent : baseEnd_3089452 < baseStart_3089452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089465 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3089465 : Nat := 118140960795 + 3089465 * 2 ^ 59
def prefixEnd_3089465 : Nat := 4983230072969 + 3 ^ 40 * 3089465 * 2
def baseEnd_3089465 : Nat := 1586380510242860187679315

theorem tailTrace_3089465 : CollatzResearch.WordTrace tailWord_3089465 prefixEnd_3089465 1586380510242860187679315 := by
  unfold tailWord_3089465
  simp only [CollatzResearch.WordTrace]
  refine ⟨112682045752403418459653849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75121363834935612306435899 112682045752403418459653849)
  ·
    refine ⟨84511534314302563844740387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112682045752403418459653849 84511534314302563844740387)
    ·
      refine ⟨126767301471453845767110581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84511534314302563844740387 126767301471453845767110581)
      ·
        refine ⟨11884434512948798040666617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126767301471453845767110581 11884434512948798040666617)
        ·
          refine ⟨8913325884711598530499963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11884434512948798040666617 8913325884711598530499963)
          ·
            refine ⟨13369988827067397795749945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8913325884711598530499963 13369988827067397795749945)
            ·
              refine ⟨10027491620300548346812459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13369988827067397795749945 10027491620300548346812459)
              ·
                refine ⟨15041237430450822520218689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10027491620300548346812459 15041237430450822520218689)
                ·
                  refine ⟨11280928072838116890164017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15041237430450822520218689 11280928072838116890164017)
                  ·
                    refine ⟨8460696054628587667623013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11280928072838116890164017 8460696054628587667623013)
                    ·
                      refine ⟨1586380510242860187679315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8460696054628587667623013 1586380510242860187679315)
                      ·
                        rfl

theorem cell23_3089465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3089465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089465 prefixEnd_3089465 := by exact prefixLift 3089465
  have htrace : WordTrace (prefixWord ++ tailWord_3089465) baseStart_3089465 baseEnd_3089465 := by
    simpa [prefixWord, tailWord_3089465, baseEnd_3089465] using wordTrace_append hprefix tailTrace_3089465
  have hstable : (prefixWord ++ tailWord_3089465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089465).length < 2 ^ (prefixWord ++ tailWord_3089465).sum := by decide
  have hdescent : baseEnd_3089465 < baseStart_3089465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089469 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 1, 4, 2]
def baseStart_3089469 : Nat := 118140960795 + 3089469 * 2 ^ 59
def prefixEnd_3089469 : Nat := 4983230072969 + 3 ^ 40 * 3089469 * 2
def baseEnd_3089469 : Nat := 1586382564165478172029297

theorem tailTrace_3089469 : CollatzResearch.WordTrace tailWord_3089469 prefixEnd_3089469 1586382564165478172029297 := by
  unfold tailWord_3089469
  simp only [CollatzResearch.WordTrace]
  refine ⟨112682191644388927142799461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75121461096259284761866307 112682191644388927142799461)
  ·
    refine ⟨21127910933322923839274899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112682191644388927142799461 21127910933322923839274899)
    ·
      refine ⟨31691866399984385758912349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21127910933322923839274899 31691866399984385758912349)
      ·
        refine ⟨11884449899994144659592131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31691866399984385758912349 11884449899994144659592131)
        ·
          refine ⟨17826674849991216989388197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11884449899994144659592131 17826674849991216989388197)
          ·
            refine ⟨3342501534373353185510287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17826674849991216989388197 3342501534373353185510287)
            ·
              refine ⟨5013752301560029778265431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3342501534373353185510287 5013752301560029778265431)
              ·
                refine ⟨7520628452340044667398147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5013752301560029778265431 7520628452340044667398147)
                ·
                  refine ⟨11280942678510067001097221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7520628452340044667398147 11280942678510067001097221)
                  ·
                    refine ⟨2115176752220637562705729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11280942678510067001097221 2115176752220637562705729)
                    ·
                      refine ⟨1586382564165478172029297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115176752220637562705729 1586382564165478172029297)
                      ·
                        rfl

theorem cell23_3089469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_3089469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089469 prefixEnd_3089469 := by exact prefixLift 3089469
  have htrace : WordTrace (prefixWord ++ tailWord_3089469) baseStart_3089469 baseEnd_3089469 := by
    simpa [prefixWord, tailWord_3089469, baseEnd_3089469] using wordTrace_append hprefix tailTrace_3089469
  have hstable : (prefixWord ++ tailWord_3089469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089469).length < 2 ^ (prefixWord ++ tailWord_3089469).sum := by decide
  have hdescent : baseEnd_3089469 < baseStart_3089469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089488 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 6, 5]
def baseStart_3089488 : Nat := 118140960795 + 3089488 * 2 ^ 59
def prefixEnd_3089488 : Nat := 4983230072969 + 3 ^ 40 * 3089488 * 2
def baseEnd_3089488 : Nat := 528797440099304532563903

theorem tailTrace_3089488 : CollatzResearch.WordTrace tailWord_3089488 prefixEnd_3089488 528797440099304532563903 := by
  unfold tailWord_3089488
  simp only [CollatzResearch.WordTrace]
  refine ⟨56341442315660046693870559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75121923087546728925160745 56341442315660046693870559)
  ·
    refine ⟨84512163473490070040805839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56341442315660046693870559 84512163473490070040805839)
    ·
      refine ⟨126768245210235105061208759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84512163473490070040805839 126768245210235105061208759)
      ·
        refine ⟨190152367815352657591813139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126768245210235105061208759 190152367815352657591813139)
        ·
          refine ⟨285228551723028986387719709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190152367815352657591813139 285228551723028986387719709)
          ·
            refine ⟨106960706896135869895394891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285228551723028986387719709 106960706896135869895394891)
            ·
              refine ⟨160441060344203804843092337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106960706896135869895394891 160441060344203804843092337)
              ·
                refine ⟨120330795258152853632319253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160441060344203804843092337 120330795258152853632319253)
                ·
                  refine ⟨5640506027725915014014965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120330795258152853632319253 5640506027725915014014965)
                  ·
                    refine ⟨528797440099304532563903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5640506027725915014014965 528797440099304532563903)
                    ·
                      rfl

theorem cell23_3089488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 6, 5].length) (baseStart_3089488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089488 prefixEnd_3089488 := by exact prefixLift 3089488
  have htrace : WordTrace (prefixWord ++ tailWord_3089488) baseStart_3089488 baseEnd_3089488 := by
    simpa [prefixWord, tailWord_3089488, baseEnd_3089488] using wordTrace_append hprefix tailTrace_3089488
  have hstable : (prefixWord ++ tailWord_3089488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089488).length < 2 ^ (prefixWord ++ tailWord_3089488).sum := by decide
  have hdescent : baseEnd_3089488 < baseStart_3089488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089492 : List Nat := [2, 4, 1, 1, 1, 1, 5, 3, 5]
def baseStart_3089492 : Nat := 118140960795 + 3089492 * 2 ^ 59
def prefixEnd_3089492 : Nat := 4983230072969 + 3 ^ 40 * 3089492 * 2
def baseEnd_3089492 : Nat := 176266041580059064671299

theorem tailTrace_3089492 : CollatzResearch.WordTrace tailWord_3089492 prefixEnd_3089492 176266041580059064671299 := by
  unfold tailWord_3089492
  simp only [CollatzResearch.WordTrace]
  refine ⟨56341515261652801035443365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75122020348870401380591153 56341515261652801035443365)
  ·
    refine ⟨10564034111559900194145631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56341515261652801035443365 10564034111559900194145631)
    ·
      refine ⟨15846051167339850291218447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10564034111559900194145631 15846051167339850291218447)
      ·
        refine ⟨23769076751009775436827671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15846051167339850291218447 23769076751009775436827671)
        ·
          refine ⟨35653615126514663155241507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23769076751009775436827671 35653615126514663155241507)
          ·
            refine ⟨53480422689771994732862261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35653615126514663155241507 53480422689771994732862261)
            ·
              refine ⟨5013789627166124506205837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53480422689771994732862261 5013789627166124506205837)
              ·
                refine ⟨1880171110187296689827189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5013789627166124506205837 1880171110187296689827189)
                ·
                  refine ⟨176266041580059064671299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1880171110187296689827189 176266041580059064671299)
                  ·
                    rfl

theorem cell23_3089492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_3089492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089492 prefixEnd_3089492 := by exact prefixLift 3089492
  have htrace : WordTrace (prefixWord ++ tailWord_3089492) baseStart_3089492 baseEnd_3089492 := by
    simpa [prefixWord, tailWord_3089492, baseEnd_3089492] using wordTrace_append hprefix tailTrace_3089492
  have hstable : (prefixWord ++ tailWord_3089492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089492).length < 2 ^ (prefixWord ++ tailWord_3089492).sum := by decide
  have hdescent : baseEnd_3089492 < baseStart_3089492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089495 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 1, 7, 2]
def baseStart_3089495 : Nat := 118140960795 + 3089495 * 2 ^ 59
def prefixEnd_3089495 : Nat := 4983230072969 + 3 ^ 40 * 3089495 * 2
def baseEnd_3089495 : Nat := 1586395914662495070304177

theorem tailTrace_3089495 : CollatzResearch.WordTrace tailWord_3089495 prefixEnd_3089495 1586395914662495070304177 := by
  unfold tailWord_3089495
  simp only [CollatzResearch.WordTrace]
  refine ⟨112683139942294733583245939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75122093294863155722163959 112683139942294733583245939)
  ·
    refine ⟨169024709913442100374868909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112683139942294733583245939 169024709913442100374868909)
    ·
      refine ⟨63384266217540787640575841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169024709913442100374868909 63384266217540787640575841)
      ·
        refine ⟨47538199663155590730431881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63384266217540787640575841 47538199663155590730431881)
        ·
          refine ⟨35653649747366693047823911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47538199663155590730431881 35653649747366693047823911)
          ·
            refine ⟨53480474621050039571735867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35653649747366693047823911 53480474621050039571735867)
            ·
              refine ⟨80220711931575059357603801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53480474621050039571735867 80220711931575059357603801)
              ·
                refine ⟨60165533948681294518202851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80220711931575059357603801 60165533948681294518202851)
                ·
                  refine ⟨90248300923021941777304277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60165533948681294518202851 90248300923021941777304277)
                  ·
                    refine ⟨2115194552883326760405569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 90248300923021941777304277 2115194552883326760405569)
                    ·
                      refine ⟨1586395914662495070304177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115194552883326760405569 1586395914662495070304177)
                      ·
                        rfl

theorem cell23_3089495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_3089495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089495 prefixEnd_3089495 := by exact prefixLift 3089495
  have htrace : WordTrace (prefixWord ++ tailWord_3089495) baseStart_3089495 baseEnd_3089495 := by
    simpa [prefixWord, tailWord_3089495, baseEnd_3089495] using wordTrace_append hprefix tailTrace_3089495
  have hstable : (prefixWord ++ tailWord_3089495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089495).length < 2 ^ (prefixWord ++ tailWord_3089495).sum := by decide
  have hdescent : baseEnd_3089495 < baseStart_3089495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089548 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 10]
def baseStart_3089548 : Nat := 118140960795 + 3089548 * 2 ^ 59
def prefixEnd_3089548 : Nat := 4983230072969 + 3 ^ 40 * 3089548 * 2
def baseEnd_3089548 : Nat := 176269236570798151437937

theorem tailTrace_3089548 : CollatzResearch.WordTrace tailWord_3089548 prefixEnd_3089548 176269236570798151437937 := by
  unfold tailWord_3089548
  simp only [CollatzResearch.WordTrace]
  refine ⟨56342536505551361817462649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75123382007401815756616865 56342536505551361817462649)
  ·
    refine ⟨42256902379163521363096987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56342536505551361817462649 42256902379163521363096987)
    ·
      refine ⟨63385353568745282044645481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42256902379163521363096987 63385353568745282044645481)
      ·
        refine ⟨47539015176558961533484111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63385353568745282044645481 47539015176558961533484111)
        ·
          refine ⟨71308522764838442300226167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47539015176558961533484111 71308522764838442300226167)
          ·
            refine ⟨106962784147257663450339251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71308522764838442300226167 106962784147257663450339251)
            ·
              refine ⟨160444176220886495175508877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106962784147257663450339251 160444176220886495175508877)
              ·
                refine ⟨60166566082832435690815829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160444176220886495175508877 60166566082832435690815829)
                ·
                  refine ⟨176269236570798151437937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 60166566082832435690815829 176269236570798151437937)
                  ·
                    rfl

theorem cell23_3089548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 10].length) (baseStart_3089548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089548 prefixEnd_3089548 := by exact prefixLift 3089548
  have htrace : WordTrace (prefixWord ++ tailWord_3089548) baseStart_3089548 baseEnd_3089548 := by
    simpa [prefixWord, tailWord_3089548, baseEnd_3089548] using wordTrace_append hprefix tailTrace_3089548
  have hstable : (prefixWord ++ tailWord_3089548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089548).length < 2 ^ (prefixWord ++ tailWord_3089548).sum := by decide
  have hdescent : baseEnd_3089548 < baseStart_3089548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089569 : List Nat := [1, 2, 3, 3, 1, 1, 3, 4, 1, 4]
def baseStart_3089569 : Nat := 118140960795 + 3089569 * 2 ^ 59
def prefixEnd_3089569 : Nat := 4983230072969 + 3 ^ 40 * 3089569 * 2
def baseEnd_3089569 : Nat := 528811304076975926926279

theorem tailTrace_3089569 : CollatzResearch.WordTrace tailWord_3089569 prefixEnd_3089569 528811304076975926926279 := by
  unfold tailWord_3089569
  simp only [CollatzResearch.WordTrace]
  refine ⟨112685838944026644221439761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75123892629351096147626507 112685838944026644221439761)
  ·
    refine ⟨84514379208019983166079821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112685838944026644221439761 84514379208019983166079821)
    ·
      refine ⟨31692892203007493687279933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84514379208019983166079821 31692892203007493687279933)
      ·
        refine ⟨11884834576127810132729975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31692892203007493687279933 11884834576127810132729975)
        ·
          refine ⟨17827251864191715199094963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11884834576127810132729975 17827251864191715199094963)
          ·
            refine ⟨26740877796287572798642445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17827251864191715199094963 26740877796287572798642445)
            ·
              refine ⟨10027829173607839799490917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26740877796287572798642445 10027829173607839799490917)
              ·
                refine ⟨1880217970051469962404547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10027829173607839799490917 1880217970051469962404547)
                ·
                  refine ⟨2820326955077204943606821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880217970051469962404547 2820326955077204943606821)
                  ·
                    refine ⟨528811304076975926926279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2820326955077204943606821 528811304076975926926279)
                    ·
                      rfl

theorem cell23_3089569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_3089569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089569 prefixEnd_3089569 := by exact prefixLift 3089569
  have htrace : WordTrace (prefixWord ++ tailWord_3089569) baseStart_3089569 baseEnd_3089569 := by
    simpa [prefixWord, tailWord_3089569, baseEnd_3089569] using wordTrace_append hprefix tailTrace_3089569
  have hstable : (prefixWord ++ tailWord_3089569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089569).length < 2 ^ (prefixWord ++ tailWord_3089569).sum := by decide
  have hdescent : baseEnd_3089569 < baseStart_3089569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089615 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 4]
def baseStart_3089615 : Nat := 118140960795 + 3089615 * 2 ^ 59
def prefixEnd_3089615 : Nat := 4983230072969 + 3 ^ 40 * 3089615 * 2
def baseEnd_3089615 : Nat := 1586457532341034600803625

theorem tailTrace_3089615 : CollatzResearch.WordTrace tailWord_3089615 prefixEnd_3089615 1586457532341034600803625 := by
  unfold tailWord_3089615
  simp only [CollatzResearch.WordTrace]
  refine ⟨112687516701859994077614299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75125011134573329385076199 112687516701859994077614299)
  ·
    refine ⟨169031275052789991116421449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112687516701859994077614299 169031275052789991116421449)
    ·
      refine ⟨126773456289592493337316087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169031275052789991116421449 126773456289592493337316087)
      ·
        refine ⟨190160184434388740005974131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126773456289592493337316087 190160184434388740005974131)
        ·
          refine ⟨285240276651583110008961197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190160184434388740005974131 285240276651583110008961197)
          ·
            refine ⟨106965103744343666253360449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285240276651583110008961197 106965103744343666253360449)
            ·
              refine ⟨80223827808257749690020337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106965103744343666253360449 80223827808257749690020337)
              ·
                refine ⟨60167870856193312267515253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80223827808257749690020337 60167870856193312267515253)
                ·
                  refine ⟨5640737892768123025079555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60167870856193312267515253 5640737892768123025079555)
                  ·
                    refine ⟨8461106839152184537619333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5640737892768123025079555 8461106839152184537619333)
                    ·
                      refine ⟨1586457532341034600803625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8461106839152184537619333 1586457532341034600803625)
                      ·
                        rfl

theorem cell23_3089615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_3089615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089615 prefixEnd_3089615 := by exact prefixLift 3089615
  have htrace : WordTrace (prefixWord ++ tailWord_3089615) baseStart_3089615 baseEnd_3089615 := by
    simpa [prefixWord, tailWord_3089615, baseEnd_3089615] using wordTrace_append hprefix tailTrace_3089615
  have hstable : (prefixWord ++ tailWord_3089615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089615).length < 2 ^ (prefixWord ++ tailWord_3089615).sum := by decide
  have hdescent : baseEnd_3089615 < baseStart_3089615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089642 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 1, 6]
def baseStart_3089642 : Nat := 118140960795 + 3089642 * 2 ^ 59
def prefixEnd_3089642 : Nat := 4983230072969 + 3 ^ 40 * 3089642 * 2
def baseEnd_3089642 : Nat := 528823798772901998388667

theorem tailTrace_3089642 : CollatzResearch.WordTrace tailWord_3089642 prefixEnd_3089642 528823798772901998388667 := by
  unfold tailWord_3089642
  simp only [CollatzResearch.WordTrace]
  refine ⟨28172125368190544422211795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75125667648508118459231453 28172125368190544422211795)
  ·
    refine ⟨42258188052285816633317693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28172125368190544422211795 42258188052285816633317693)
    ·
      refine ⟨15846820519607181237494135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42258188052285816633317693 15846820519607181237494135)
      ·
        refine ⟨23770230779410771856241203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15846820519607181237494135 23770230779410771856241203)
        ·
          refine ⟨35655346169116157784361805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23770230779410771856241203 35655346169116157784361805)
          ·
            refine ⟨13370754813418559169135677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35655346169116157784361805 13370754813418559169135677)
            ·
              refine ⟨5014033055031959688425879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13370754813418559169135677 5014033055031959688425879)
              ·
                refine ⟨7521049582547939532638819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5014033055031959688425879 7521049582547939532638819)
                ·
                  refine ⟨11281574373821909298958229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7521049582547939532638819 11281574373821909298958229)
                  ·
                    refine ⟨528823798772901998388667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11281574373821909298958229 528823798772901998388667)
                    ·
                      rfl

theorem cell23_3089642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_3089642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089642 prefixEnd_3089642 := by exact prefixLift 3089642
  have htrace : WordTrace (prefixWord ++ tailWord_3089642) baseStart_3089642 baseEnd_3089642 := by
    simpa [prefixWord, tailWord_3089642, baseEnd_3089642] using wordTrace_append hprefix tailTrace_3089642
  have hstable : (prefixWord ++ tailWord_3089642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089642).length < 2 ^ (prefixWord ++ tailWord_3089642).sum := by decide
  have hdescent : baseEnd_3089642 < baseStart_3089642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089660 : List Nat := [2, 2, 2, 1, 6, 1, 1, 3, 1, 1, 3]
def baseStart_3089660 : Nat := 118140960795 + 3089660 * 2 ^ 59
def prefixEnd_3089660 : Nat := 4983230072969 + 3 ^ 40 * 3089660 * 2
def baseEnd_3089660 : Nat := 1586480638970486924740919

theorem tailTrace_3089660 : CollatzResearch.WordTrace tailWord_3089660 prefixEnd_3089660 1586480638970486924740919 := by
  unfold tailWord_3089660
  simp only [CollatzResearch.WordTrace]
  refine ⟨56344578993348483381501217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75126105324464644508668289 56344578993348483381501217)
  ·
    refine ⟨42258434245011362536125913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56344578993348483381501217 42258434245011362536125913)
    ·
      refine ⟨31693825683758521902094435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42258434245011362536125913 31693825683758521902094435)
      ·
        refine ⟨47540738525637782853141653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31693825683758521902094435 47540738525637782853141653)
        ·
          refine ⟨2228472118389271071241015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47540738525637782853141653 2228472118389271071241015)
          ·
            refine ⟨3342708177583906606861523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2228472118389271071241015 3342708177583906606861523)
            ·
              refine ⟨5014062266375859910292285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3342708177583906606861523 5014062266375859910292285)
              ·
                refine ⟨1880273349890947466359607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5014062266375859910292285 1880273349890947466359607)
                ·
                  refine ⟨2820410024836421199539411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880273349890947466359607 2820410024836421199539411)
                  ·
                    refine ⟨4230615037254631799309117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2820410024836421199539411 4230615037254631799309117)
                    ·
                      refine ⟨1586480638970486924740919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4230615037254631799309117 1586480638970486924740919)
                      ·
                        rfl

theorem cell23_3089660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_3089660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089660 prefixEnd_3089660 := by exact prefixLift 3089660
  have htrace : WordTrace (prefixWord ++ tailWord_3089660) baseStart_3089660 baseEnd_3089660 := by
    simpa [prefixWord, tailWord_3089660, baseEnd_3089660] using wordTrace_append hprefix tailTrace_3089660
  have hstable : (prefixWord ++ tailWord_3089660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089660).length < 2 ^ (prefixWord ++ tailWord_3089660).sum := by decide
  have hdescent : baseEnd_3089660 < baseStart_3089660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089672 : List Nat := [2, 1, 3, 2, 4, 2, 9]
def baseStart_3089672 : Nat := 118140960795 + 3089672 * 2 ^ 59
def prefixEnd_3089672 : Nat := 4983230072969 + 3 ^ 40 * 3089672 * 2
def baseEnd_3089672 : Nat := 19586256799238776269023

theorem tailTrace_3089672 : CollatzResearch.WordTrace tailWord_3089672 prefixEnd_3089672 19586256799238776269023 := by
  unfold tailWord_3089672
  simp only [CollatzResearch.WordTrace]
  refine ⟨56344797831326746406219635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75126397108435661874959513 56344797831326746406219635)
  ·
    refine ⟨84517196746990119609329453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56344797831326746406219635 84517196746990119609329453)
    ·
      refine ⟨31693948780121294853498545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84517196746990119609329453 31693948780121294853498545)
      ·
        refine ⟨23770461585090971140123909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31693948780121294853498545 23770461585090971140123909)
        ·
          refine ⟨4456961547204557088773233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23770461585090971140123909 4456961547204557088773233)
          ·
            refine ⟨3342721160403417816579925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4456961547204557088773233 3342721160403417816579925)
            ·
              refine ⟨19586256799238776269023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3342721160403417816579925 19586256799238776269023)
              ·
                rfl

theorem cell23_3089672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 9].length) (baseStart_3089672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089672 prefixEnd_3089672 := by exact prefixLift 3089672
  have htrace : WordTrace (prefixWord ++ tailWord_3089672) baseStart_3089672 baseEnd_3089672 := by
    simpa [prefixWord, tailWord_3089672, baseEnd_3089672] using wordTrace_append hprefix tailTrace_3089672
  have hstable : (prefixWord ++ tailWord_3089672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089672).length < 2 ^ (prefixWord ++ tailWord_3089672).sum := by decide
  have hdescent : baseEnd_3089672 < baseStart_3089672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089685 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 2, 7]
def baseStart_3089685 : Nat := 118140960795 + 3089685 * 2 ^ 59
def prefixEnd_3089685 : Nat := 4983230072969 + 3 ^ 40 * 3089685 * 2
def baseEnd_3089685 : Nat := 528831158662283108976101

theorem tailTrace_3089685 : CollatzResearch.WordTrace tailWord_3089685 prefixEnd_3089685 528831158662283108976101 := by
  unfold tailWord_3089685
  simp only [CollatzResearch.WordTrace]
  refine ⟨112690069811606396032662509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75126713207737597355108339 112690069811606396032662509)
  ·
    refine ⟨42258776179352398512248441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112690069811606396032662509 42258776179352398512248441)
    ·
      refine ⟨31694082134514298884186331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42258776179352398512248441 31694082134514298884186331)
      ·
        refine ⟨47541123201771448326279497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31694082134514298884186331 47541123201771448326279497)
        ·
          refine ⟨35655842401328586244709623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47541123201771448326279497 35655842401328586244709623)
          ·
            refine ⟨53483763601992879367064435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35655842401328586244709623 53483763601992879367064435)
            ·
              refine ⟨80225645402989319050596653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53483763601992879367064435 80225645402989319050596653)
              ·
                refine ⟨30084617026120994643973745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80225645402989319050596653 30084617026120994643973745)
                ·
                  refine ⟨22563462769590745982980309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30084617026120994643973745 22563462769590745982980309)
                  ·
                    refine ⟨528831158662283108976101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22563462769590745982980309 528831158662283108976101)
                    ·
                      rfl

theorem cell23_3089685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_3089685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089685 prefixEnd_3089685 := by exact prefixLift 3089685
  have htrace : WordTrace (prefixWord ++ tailWord_3089685) baseStart_3089685 baseEnd_3089685 := by
    simpa [prefixWord, tailWord_3089685, baseEnd_3089685] using wordTrace_append hprefix tailTrace_3089685
  have hstable : (prefixWord ++ tailWord_3089685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089685).length < 2 ^ (prefixWord ++ tailWord_3089685).sum := by decide
  have hdescent : baseEnd_3089685 < baseStart_3089685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089693 : List Nat := [1, 4, 2, 3, 1, 3, 2, 1, 2, 4]
def baseStart_3089693 : Nat := 118140960795 + 3089693 * 2 ^ 59
def prefixEnd_3089693 : Nat := 4983230072969 + 3 ^ 40 * 3089693 * 2
def baseEnd_3089693 : Nat := 528832527944028431876089

theorem tailTrace_3089693 : CollatzResearch.WordTrace tailWord_3089693 prefixEnd_3089693 528832527944028431876089 := by
  unfold tailWord_3089693
  simp only [CollatzResearch.WordTrace]
  refine ⟨112690361595577413398953733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75126907730384942265969155 112690361595577413398953733)
  ·
    refine ⟨21129442799170765012303825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112690361595577413398953733 21129442799170765012303825)
    ·
      refine ⟨15847082099378073759227869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21129442799170765012303825 15847082099378073759227869)
      ·
        refine ⟨5942655787266777659710451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15847082099378073759227869 5942655787266777659710451)
        ·
          refine ⟨8913983680900166489565677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5942655787266777659710451 8913983680900166489565677)
          ·
            refine ⟨3342743880337562433587129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8913983680900166489565677 3342743880337562433587129)
            ·
              refine ⟨2507057910253171825190347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3342743880337562433587129 2507057910253171825190347)
              ·
                refine ⟨3760586865379757737785521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507057910253171825190347 3760586865379757737785521)
                ·
                  refine ⟨2820440149034818303339141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3760586865379757737785521 2820440149034818303339141)
                  ·
                    refine ⟨528832527944028431876089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2820440149034818303339141 528832527944028431876089)
                    ·
                      rfl

theorem cell23_3089693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_3089693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089693 prefixEnd_3089693 := by exact prefixLift 3089693
  have htrace : WordTrace (prefixWord ++ tailWord_3089693) baseStart_3089693 baseEnd_3089693 := by
    simpa [prefixWord, tailWord_3089693, baseEnd_3089693] using wordTrace_append hprefix tailTrace_3089693
  have hstable : (prefixWord ++ tailWord_3089693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089693).length < 2 ^ (prefixWord ++ tailWord_3089693).sum := by decide
  have hdescent : baseEnd_3089693 < baseStart_3089693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089734 : List Nat := [6, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3089734 : Nat := 118140960795 + 3089734 * 2 ^ 59
def prefixEnd_3089734 : Nat := 4983230072969 + 3 ^ 40 * 3089734 * 2
def baseEnd_3089734 : Nat := 1586518636538919635215579

theorem tailTrace_3089734 : CollatzResearch.WordTrace tailWord_3089734 prefixEnd_3089734 1586518636538919635215579 := by
  unfold tailWord_3089734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3521620530888402418787383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75127904658952584934130837 3521620530888402418787383)
  ·
    refine ⟨5282430796332603628181075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3521620530888402418787383 5282430796332603628181075)
    ·
      refine ⟨7923646194498905442271613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5282430796332603628181075 7923646194498905442271613)
      ·
        refine ⟨2971367322937089540851855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7923646194498905442271613 2971367322937089540851855)
        ·
          refine ⟨4457050984405634311277783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2971367322937089540851855 4457050984405634311277783)
          ·
            refine ⟨6685576476608451466916675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4457050984405634311277783 6685576476608451466916675)
            ·
              refine ⟨10028364714912677200375013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6685576476608451466916675 10028364714912677200375013)
              ·
                refine ⟨1880318384046126975070315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10028364714912677200375013 1880318384046126975070315)
                ·
                  refine ⟨2820477576069190462605473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880318384046126975070315 2820477576069190462605473)
                  ·
                    refine ⟨2115358182051892846954105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2820477576069190462605473 2115358182051892846954105)
                    ·
                      refine ⟨1586518636538919635215579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115358182051892846954105 1586518636538919635215579)
                      ·
                        rfl

theorem cell23_3089734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3089734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089734 prefixEnd_3089734 := by exact prefixLift 3089734
  have htrace : WordTrace (prefixWord ++ tailWord_3089734) baseStart_3089734 baseEnd_3089734 := by
    simpa [prefixWord, tailWord_3089734, baseEnd_3089734] using wordTrace_append hprefix tailTrace_3089734
  have hstable : (prefixWord ++ tailWord_3089734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089734).length < 2 ^ (prefixWord ++ tailWord_3089734).sum := by decide
  have hdescent : baseEnd_3089734 < baseStart_3089734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089739 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 8, 2, 2]
def baseStart_3089739 : Nat := 118140960795 + 3089739 * 2 ^ 59
def prefixEnd_3089739 : Nat := 4983230072969 + 3 ^ 40 * 3089739 * 2
def baseEnd_3089739 : Nat := 1586521203942192115653055

theorem tailTrace_3089739 : CollatzResearch.WordTrace tailWord_3089739 prefixEnd_3089739 1586521203942192115653055 := by
  unfold tailWord_3089739
  simp only [CollatzResearch.WordTrace]
  refine ⟨112692039353410763255128271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75128026235607175503418847 112692039353410763255128271)
  ·
    refine ⟨169038059030116144882692407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112692039353410763255128271 169038059030116144882692407)
    ·
      refine ⟨253557088545174217324038611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169038059030116144882692407 253557088545174217324038611)
      ·
        refine ⟨380335632817761325986057917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253557088545174217324038611 380335632817761325986057917)
        ·
          refine ⟨142625862306660497244771719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380335632817761325986057917 142625862306660497244771719)
          ·
            refine ⟨213938793459990745867157579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142625862306660497244771719 213938793459990745867157579)
            ·
              refine ⟨320908190189986118800736369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213938793459990745867157579 320908190189986118800736369)
              ·
                refine ⟨240681142642489589100552277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320908190189986118800736369 240681142642489589100552277)
                ·
                  refine ⟨2820482140341674872272097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 240681142642489589100552277 2820482140341674872272097)
                  ·
                    refine ⟨2115361605256256154204073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2820482140341674872272097 2115361605256256154204073)
                    ·
                      refine ⟨1586521203942192115653055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115361605256256154204073 1586521203942192115653055)
                      ·
                        rfl

theorem cell23_3089739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 2, 2].length) (baseStart_3089739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089739 prefixEnd_3089739 := by exact prefixLift 3089739
  have htrace : WordTrace (prefixWord ++ tailWord_3089739) baseStart_3089739 baseEnd_3089739 := by
    simpa [prefixWord, tailWord_3089739, baseEnd_3089739] using wordTrace_append hprefix tailTrace_3089739
  have hstable : (prefixWord ++ tailWord_3089739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089739).length < 2 ^ (prefixWord ++ tailWord_3089739).sum := by decide
  have hdescent : baseEnd_3089739 < baseStart_3089739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089742 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3]
def baseStart_3089742 : Nat := 118140960795 + 3089742 * 2 ^ 59
def prefixEnd_3089742 : Nat := 4983230072969 + 3 ^ 40 * 3089742 * 2
def baseEnd_3089742 : Nat := 1586522744384155603915541

theorem tailTrace_3089742 : CollatzResearch.WordTrace tailWord_3089742 prefixEnd_3089742 1586522744384155603915541 := by
  unfold tailWord_3089742
  simp only [CollatzResearch.WordTrace]
  refine ⟨14086518596549986845935935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75128099181599929844991653 14086518596549986845935935)
  ·
    refine ⟨21129777894824980268903903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14086518596549986845935935 21129777894824980268903903)
    ·
      refine ⟨31694666842237470403355855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21129777894824980268903903 31694666842237470403355855)
      ·
        refine ⟨47542000263356205605033783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31694666842237470403355855 47542000263356205605033783)
        ·
          refine ⟨71313000395034308407550675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47542000263356205605033783 71313000395034308407550675)
          ·
            refine ⟨106969500592551462611326013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71313000395034308407550675 106969500592551462611326013)
            ·
              refine ⟨40113562722206798479247255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106969500592551462611326013 40113562722206798479247255)
              ·
                refine ⟨60170344083310197718870883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40113562722206798479247255 60170344083310197718870883)
                ·
                  refine ⟨90255516124965296578306325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60170344083310197718870883 90255516124965296578306325)
                  ·
                    refine ⟨4230727318357748277108109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90255516124965296578306325 4230727318357748277108109)
                    ·
                      refine ⟨1586522744384155603915541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4230727318357748277108109 1586522744384155603915541)
                      ·
                        rfl

theorem cell23_3089742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_3089742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089742 prefixEnd_3089742 := by exact prefixLift 3089742
  have htrace : WordTrace (prefixWord ++ tailWord_3089742) baseStart_3089742 baseEnd_3089742 := by
    simpa [prefixWord, tailWord_3089742, baseEnd_3089742] using wordTrace_append hprefix tailTrace_3089742
  have hstable : (prefixWord ++ tailWord_3089742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089742).length < 2 ^ (prefixWord ++ tailWord_3089742).sum := by decide
  have hdescent : baseEnd_3089742 < baseStart_3089742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089752 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 2, 2, 4]
def baseStart_3089752 : Nat := 118140960795 + 3089752 * 2 ^ 59
def prefixEnd_3089752 : Nat := 4983230072969 + 3 ^ 40 * 3089752 * 2
def baseEnd_3089752 : Nat := 1586527879190700564790495

theorem tailTrace_3089752 : CollatzResearch.WordTrace tailWord_3089752 prefixEnd_3089752 1586527879190700564790495 := by
  unfold tailWord_3089752
  simp only [CollatzResearch.WordTrace]
  refine ⟨56346256751181833237675755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75128342334909110983567673 56346256751181833237675755)
  ·
    refine ⟨84519385126772749856513633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56346256751181833237675755 84519385126772749856513633)
    ·
      refine ⟨63389538845079562392385225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84519385126772749856513633 63389538845079562392385225)
      ·
        refine ⟨47542154133809671794288919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63389538845079562392385225 47542154133809671794288919)
        ·
          refine ⟨71313231200714507691433379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47542154133809671794288919 71313231200714507691433379)
          ·
            refine ⟨106969846801071761537150069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71313231200714507691433379 106969846801071761537150069)
            ·
              refine ⟨10028423137600477644107819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106969846801071761537150069 10028423137600477644107819)
              ·
                refine ⟨15042634706400716466161729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10028423137600477644107819 15042634706400716466161729)
                ·
                  refine ⟨11281976029800537349621297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15042634706400716466161729 11281976029800537349621297)
                  ·
                    refine ⟨8461482022350403012215973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11281976029800537349621297 8461482022350403012215973)
                    ·
                      refine ⟨1586527879190700564790495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8461482022350403012215973 1586527879190700564790495)
                      ·
                        rfl

theorem cell23_3089752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_3089752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089752 prefixEnd_3089752 := by exact prefixLift 3089752
  have htrace : WordTrace (prefixWord ++ tailWord_3089752) baseStart_3089752 baseEnd_3089752 := by
    simpa [prefixWord, tailWord_3089752, baseEnd_3089752] using wordTrace_append hprefix tailTrace_3089752
  have hstable : (prefixWord ++ tailWord_3089752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089752).length < 2 ^ (prefixWord ++ tailWord_3089752).sum := by decide
  have hdescent : baseEnd_3089752 < baseStart_3089752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089792 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 2, 5]
def baseStart_3089792 : Nat := 118140960795 + 3089792 * 2 ^ 59
def prefixEnd_3089792 : Nat := 4983230072969 + 3 ^ 40 * 3089792 * 2
def baseEnd_3089792 : Nat := 528849472805626802763437

theorem tailTrace_3089792 : CollatzResearch.WordTrace tailWord_3089792 prefixEnd_3089792 528849472805626802763437 := by
  unfold tailWord_3089792
  simp only [CollatzResearch.WordTrace]
  refine ⟨56346986211109376653403815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75129314948145835537871753 56346986211109376653403815)
  ·
    refine ⟨84520479316664064980105723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56346986211109376653403815 84520479316664064980105723)
    ·
      refine ⟨126780718974996097470158585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84520479316664064980105723 126780718974996097470158585)
      ·
        refine ⟨95085539231247073102618939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126780718974996097470158585 95085539231247073102618939)
        ·
          refine ⟨142628308846870609653928409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95085539231247073102618939 142628308846870609653928409)
          ·
            refine ⟨106971231635152957240446307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142628308846870609653928409 106971231635152957240446307)
            ·
              refine ⟨160456847452729435860669461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106971231635152957240446307 160456847452729435860669461)
              ·
                refine ⟨7521414724346692305968881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160456847452729435860669461 7521414724346692305968881)
                ·
                  refine ⟨5641061043260019229476661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7521414724346692305968881 5641061043260019229476661)
                  ·
                    refine ⟨528849472805626802763437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5641061043260019229476661 528849472805626802763437)
                    ·
                      rfl

theorem cell23_3089792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 2, 5].length) (baseStart_3089792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089792 prefixEnd_3089792 := by exact prefixLift 3089792
  have htrace : WordTrace (prefixWord ++ tailWord_3089792) baseStart_3089792 baseEnd_3089792 := by
    simpa [prefixWord, tailWord_3089792, baseEnd_3089792] using wordTrace_append hprefix tailTrace_3089792
  have hstable : (prefixWord ++ tailWord_3089792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089792).length < 2 ^ (prefixWord ++ tailWord_3089792).sum := by decide
  have hdescent : baseEnd_3089792 < baseStart_3089792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089829 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 4, 4, 2]
def baseStart_3089829 : Nat := 118140960795 + 3089829 * 2 ^ 59
def prefixEnd_3089829 : Nat := 4983230072969 + 3 ^ 40 * 3089829 * 2
def baseEnd_3089829 : Nat := 1586567417201096763527641

theorem tailTrace_3089829 : CollatzResearch.WordTrace tailWord_3089829 prefixEnd_3089829 1586567417201096763527641 := by
  unfold tailWord_3089829
  simp only [CollatzResearch.WordTrace]
  refine ⟨112695321923084708625904541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75130214615389805750603027 112695321923084708625904541)
  ·
    refine ⟨42260745721156765734714203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112695321923084708625904541 42260745721156765734714203)
    ·
      refine ⟨63391118581735148602071305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42260745721156765734714203 63391118581735148602071305)
      ·
        refine ⟨47543338936301361451553479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63391118581735148602071305 47543338936301361451553479)
        ·
          refine ⟨71315008404452042177330219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47543338936301361451553479 71315008404452042177330219)
          ·
            refine ⟨106972512606678063265995329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71315008404452042177330219 106972512606678063265995329)
            ·
              refine ⟨80229384455008547449496497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106972512606678063265995329 80229384455008547449496497)
              ·
                refine ⟨60172038341256410587122373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80229384455008547449496497 60172038341256410587122373)
                ·
                  refine ⟨11282257188985576985085445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60172038341256410587122373 11282257188985576985085445)
                  ·
                    refine ⟨2115423222934795684703521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11282257188985576985085445 2115423222934795684703521)
                    ·
                      refine ⟨1586567417201096763527641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115423222934795684703521 1586567417201096763527641)
                      ·
                        rfl

theorem cell23_3089829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_3089829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089829 prefixEnd_3089829 := by exact prefixLift 3089829
  have htrace : WordTrace (prefixWord ++ tailWord_3089829) baseStart_3089829 baseEnd_3089829 := by
    simpa [prefixWord, tailWord_3089829, baseEnd_3089829] using wordTrace_append hprefix tailTrace_3089829
  have hstable : (prefixWord ++ tailWord_3089829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089829).length < 2 ^ (prefixWord ++ tailWord_3089829).sum := by decide
  have hdescent : baseEnd_3089829 < baseStart_3089829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089842 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_3089842 : Nat := 118140960795 + 3089842 * 2 ^ 59
def prefixEnd_3089842 : Nat := 4983230072969 + 3 ^ 40 * 3089842 * 2
def baseEnd_3089842 : Nat := 1586574092449605212665081

theorem tailTrace_3089842 : CollatzResearch.WordTrace tailWord_3089842 prefixEnd_3089842 1586574092449605212665081 := by
  unfold tailWord_3089842
  simp only [CollatzResearch.WordTrace]
  refine ⟨28173949018009402961531945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75130530714691741230751853 28173949018009402961531945)
  ·
    refine ⟨21130461763507052221148959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28173949018009402961531945 21130461763507052221148959)
    ·
      refine ⟨31695692645260578331723439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21130461763507052221148959 31695692645260578331723439)
      ·
        refine ⟨47543538967890867497585159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31695692645260578331723439 47543538967890867497585159)
        ·
          refine ⟨71315308451836301246377739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47543538967890867497585159 71315308451836301246377739)
          ·
            refine ⟨106972962677754451869566609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71315308451836301246377739 106972962677754451869566609)
            ·
              refine ⟨80229722008315838902174957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106972962677754451869566609 80229722008315838902174957)
              ·
                refine ⟨30086145753118439588315609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80229722008315838902174957 30086145753118439588315609)
                ·
                  refine ⟨22564609314838829691236707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30086145753118439588315609 22564609314838829691236707)
                  ·
                    refine ⟨33846913972258244536855061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22564609314838829691236707 33846913972258244536855061)
                    ·
                      refine ⟨1586574092449605212665081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33846913972258244536855061 1586574092449605212665081)
                      ·
                        rfl

theorem cell23_3089842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_3089842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089842 prefixEnd_3089842 := by exact prefixLift 3089842
  have htrace : WordTrace (prefixWord ++ tailWord_3089842) baseStart_3089842 baseEnd_3089842 := by
    simpa [prefixWord, tailWord_3089842, baseEnd_3089842] using wordTrace_append hprefix tailTrace_3089842
  have hstable : (prefixWord ++ tailWord_3089842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089842).length < 2 ^ (prefixWord ++ tailWord_3089842).sum := by decide
  have hdescent : baseEnd_3089842 < baseStart_3089842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089856 : List Nat := [2, 1, 1, 2, 3, 1, 2, 6, 1, 4]
def baseStart_3089856 : Nat := 118140960795 + 3089856 * 2 ^ 59
def prefixEnd_3089856 : Nat := 4983230072969 + 3 ^ 40 * 3089856 * 2
def baseEnd_3089856 : Nat := 528860427059589385963339

theorem tailTrace_3089856 : CollatzResearch.WordTrace tailWord_3089856 prefixEnd_3089856 528860427059589385963339 := by
  unfold tailWord_3089856
  simp only [CollatzResearch.WordTrace]
  refine ⟨56348153346993446118568711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75130871129324594824758281 56348153346993446118568711)
  ·
    refine ⟨84522230020490169177853067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56348153346993446118568711 84522230020490169177853067)
    ·
      refine ⟨126783345030735253766779601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84522230020490169177853067 126783345030735253766779601)
      ·
        refine ⟨95087508773051440325084701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126783345030735253766779601 95087508773051440325084701)
        ·
          refine ⟨35657815789894290121906763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95087508773051440325084701 35657815789894290121906763)
          ·
            refine ⟨53486723684841435182860145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35657815789894290121906763 53486723684841435182860145)
            ·
              refine ⟨40115042763631076387145109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53486723684841435182860145 40115042763631076387145109)
              ·
                refine ⟨1880392629545206705647427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40115042763631076387145109 1880392629545206705647427)
                ·
                  refine ⟨2820588944317810058471141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880392629545206705647427 2820588944317810058471141)
                  ·
                    refine ⟨528860427059589385963339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2820588944317810058471141 528860427059589385963339)
                    ·
                      rfl

theorem cell23_3089856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 1, 4].length) (baseStart_3089856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089856 prefixEnd_3089856 := by exact prefixLift 3089856
  have htrace : WordTrace (prefixWord ++ tailWord_3089856) baseStart_3089856 baseEnd_3089856 := by
    simpa [prefixWord, tailWord_3089856, baseEnd_3089856] using wordTrace_append hprefix tailTrace_3089856
  have hstable : (prefixWord ++ tailWord_3089856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089856).length < 2 ^ (prefixWord ++ tailWord_3089856).sum := by decide
  have hdescent : baseEnd_3089856 < baseStart_3089856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089858 : List Nat := [3, 5, 2, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_3089858 : Nat := 118140960795 + 3089858 * 2 ^ 59
def prefixEnd_3089858 : Nat := 4983230072969 + 3 ^ 40 * 3089858 * 2
def baseEnd_3089858 : Nat := 1586582308140077150065009

theorem tailTrace_3089858 : CollatzResearch.WordTrace tailWord_3089858 prefixEnd_3089858 1586582308140077150065009 := by
  unfold tailWord_3089858
  simp only [CollatzResearch.WordTrace]
  refine ⟨28174094909994911644677557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75130919759986431052473485 28174094909994911644677557)
  ·
    refine ⟨2641321397812022966688521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28174094909994911644677557 2641321397812022966688521)
    ·
      refine ⟨1980991048359017225016391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2641321397812022966688521 1980991048359017225016391)
      ·
        refine ⟨2971486572538525837524587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980991048359017225016391 2971486572538525837524587)
        ·
          refine ⟨4457229858807788756286881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2971486572538525837524587 4457229858807788756286881)
          ·
            refine ⟨3342922394105841567215161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4457229858807788756286881 3342922394105841567215161)
            ·
              refine ⟨2507191795579381175411371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3342922394105841567215161 2507191795579381175411371)
              ·
                refine ⟨3760787693369071763117057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507191795579381175411371 3760787693369071763117057)
                ·
                  refine ⟨2820590770026803822337793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3760787693369071763117057 2820590770026803822337793)
                  ·
                    refine ⟨2115443077520102866753345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2820590770026803822337793 2115443077520102866753345)
                    ·
                      refine ⟨1586582308140077150065009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115443077520102866753345 1586582308140077150065009)
                      ·
                        rfl

theorem cell23_3089858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_3089858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089858 prefixEnd_3089858 := by exact prefixLift 3089858
  have htrace : WordTrace (prefixWord ++ tailWord_3089858) baseStart_3089858 baseEnd_3089858 := by
    simpa [prefixWord, tailWord_3089858, baseEnd_3089858] using wordTrace_append hprefix tailTrace_3089858
  have hstable : (prefixWord ++ tailWord_3089858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089858).length < 2 ^ (prefixWord ++ tailWord_3089858).sum := by decide
  have hdescent : baseEnd_3089858 < baseStart_3089858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089892 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_3089892 : Nat := 118140960795 + 3089892 * 2 ^ 59
def prefixEnd_3089892 : Nat := 4983230072969 + 3 ^ 40 * 3089892 * 2
def baseEnd_3089892 : Nat := 1586599766482330017039851

theorem tailTrace_3089892 : CollatzResearch.WordTrace tailWord_3089892 prefixEnd_3089892 1586599766482330017039851 := by
  unfold tailWord_3089892
  simp only [CollatzResearch.WordTrace]
  refine ⟨56348809860928235192723965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75131746481237646923631953 56348809860928235192723965)
  ·
    refine ⟨21130803697848088197271487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56348809860928235192723965 21130803697848088197271487)
    ·
      refine ⟨31696205546772132295907231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21130803697848088197271487 31696205546772132295907231)
      ·
        refine ⟨47544308320158198443860847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31696205546772132295907231 47544308320158198443860847)
        ·
          refine ⟨71316462480237297665791271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47544308320158198443860847 71316462480237297665791271)
          ·
            refine ⟨106974693720355946498686907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71316462480237297665791271 106974693720355946498686907)
            ·
              refine ⟨160462040580533919748030361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106974693720355946498686907 160462040580533919748030361)
              ·
                refine ⟨120346530435400439811022771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160462040580533919748030361 120346530435400439811022771)
                ·
                  refine ⟨180519795653100659716534157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120346530435400439811022771 180519795653100659716534157)
                  ·
                    refine ⟨67694923369912747393700309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180519795653100659716534157 67694923369912747393700309)
                    ·
                      refine ⟨1586599766482330017039851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67694923369912747393700309 1586599766482330017039851)
                      ·
                        rfl

theorem cell23_3089892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_3089892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089892 prefixEnd_3089892 := by exact prefixLift 3089892
  have htrace : WordTrace (prefixWord ++ tailWord_3089892) baseStart_3089892 baseEnd_3089892 := by
    simpa [prefixWord, tailWord_3089892, baseEnd_3089892] using wordTrace_append hprefix tailTrace_3089892
  have hstable : (prefixWord ++ tailWord_3089892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089892).length < 2 ^ (prefixWord ++ tailWord_3089892).sum := by decide
  have hdescent : baseEnd_3089892 < baseStart_3089892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089929 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 1, 6]
def baseStart_3089929 : Nat := 118140960795 + 3089929 * 2 ^ 59
def prefixEnd_3089929 : Nat := 4983230072969 + 3 ^ 40 * 3089929 * 2
def baseEnd_3089929 : Nat := 528872921755515457425727

theorem tailTrace_3089929 : CollatzResearch.WordTrace tailWord_3089929 prefixEnd_3089929 528872921755515457425727 := by
  unfold tailWord_3089929
  simp only [CollatzResearch.WordTrace]
  refine ⟨112698969222722425704544841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75132646148481617136363227 112698969222722425704544841)
  ·
    refine ⟨84524226917041819278408631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112698969222722425704544841 84524226917041819278408631)
    ·
      refine ⟨126786340375562728917612947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84524226917041819278408631 126786340375562728917612947)
      ·
        refine ⟨190179510563344093376419421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126786340375562728917612947 190179510563344093376419421)
        ·
          refine ⟨71317316461254035016157283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190179510563344093376419421 71317316461254035016157283)
          ·
            refine ⟨106975974691881052524235925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71317316461254035016157283 106975974691881052524235925)
            ·
              refine ⟨5014498813681924337073559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106975974691881052524235925 5014498813681924337073559)
              ·
                refine ⟨7521748220522886505610339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5014498813681924337073559 7521748220522886505610339)
                ·
                  refine ⟨11282622330784329758415509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7521748220522886505610339 11282622330784329758415509)
                  ·
                    refine ⟨528872921755515457425727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11282622330784329758415509 528872921755515457425727)
                    ·
                      rfl

theorem cell23_3089929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 6].length) (baseStart_3089929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089929 prefixEnd_3089929 := by exact prefixLift 3089929
  have htrace : WordTrace (prefixWord ++ tailWord_3089929) baseStart_3089929 baseEnd_3089929 := by
    simpa [prefixWord, tailWord_3089929, baseEnd_3089929] using wordTrace_append hprefix tailTrace_3089929
  have hstable : (prefixWord ++ tailWord_3089929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089929).length < 2 ^ (prefixWord ++ tailWord_3089929).sum := by decide
  have hdescent : baseEnd_3089929 < baseStart_3089929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089940 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_3089940 : Nat := 118140960795 + 3089940 * 2 ^ 59
def prefixEnd_3089940 : Nat := 4983230072969 + 3 ^ 40 * 3089940 * 2
def baseEnd_3089940 : Nat := 1586624413553745829239631

theorem tailTrace_3089940 : CollatzResearch.WordTrace tailWord_3089940 prefixEnd_3089940 1586624413553745829239631 := by
  unfold tailWord_3089940
  simp only [CollatzResearch.WordTrace]
  refine ⟨56349685212841287291597637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75132913617121716388796849 56349685212841287291597637)
  ·
    refine ⟨10565565977407741367174557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56349685212841287291597637 10565565977407741367174557)
    ·
      refine ⟨3962087241527903012690459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10565565977407741367174557 3962087241527903012690459)
      ·
        refine ⟨5943130862291854519035689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3962087241527903012690459 5943130862291854519035689)
        ·
          refine ⟨4457348146718890889276767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5943130862291854519035689 4457348146718890889276767)
          ·
            refine ⟨6686022220078336333915151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4457348146718890889276767 6686022220078336333915151)
            ·
              refine ⟨10029033330117504500872727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6686022220078336333915151 10029033330117504500872727)
              ·
                refine ⟨15043549995176256751309091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10029033330117504500872727 15043549995176256751309091)
                ·
                  refine ⟨22565324992764385126963637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15043549995176256751309091 22565324992764385126963637)
                  ·
                    refine ⟨2115499218071661105652841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22565324992764385126963637 2115499218071661105652841)
                    ·
                      refine ⟨1586624413553745829239631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115499218071661105652841 1586624413553745829239631)
                      ·
                        rfl

theorem cell23_3089940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_3089940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089940 prefixEnd_3089940 := by exact prefixLift 3089940
  have htrace : WordTrace (prefixWord ++ tailWord_3089940) baseStart_3089940 baseEnd_3089940 := by
    simpa [prefixWord, tailWord_3089940, baseEnd_3089940] using wordTrace_append hprefix tailTrace_3089940
  have hstable : (prefixWord ++ tailWord_3089940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089940).length < 2 ^ (prefixWord ++ tailWord_3089940).sum := by decide
  have hdescent : baseEnd_3089940 < baseStart_3089940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089953 : List Nat := [1, 2, 3, 2, 2, 2, 4, 1, 1, 1, 4]
def baseStart_3089953 : Nat := 118140960795 + 3089953 * 2 ^ 59
def prefixEnd_3089953 : Nat := 4983230072969 + 3 ^ 40 * 3089953 * 2
def baseEnd_3089953 : Nat := 1586631088802254278377071

theorem tailTrace_3089953 : CollatzResearch.WordTrace tailWord_3089953 prefixEnd_3089953 1586631088802254278377071 := by
  unfold tailWord_3089953
  simp only [CollatzResearch.WordTrace]
  refine ⟨112699844574635477803418513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75133229716423651868945675 112699844574635477803418513)
  ·
    refine ⟨84524883430976608352563885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112699844574635477803418513 84524883430976608352563885)
    ·
      refine ⟨31696831286616228132211457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84524883430976608352563885 31696831286616228132211457)
      ·
        refine ⟨23772623464962171099158593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31696831286616228132211457 23772623464962171099158593)
        ·
          refine ⟨17829467598721628324368945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23772623464962171099158593 17829467598721628324368945)
          ·
            refine ⟨13372100699041221243276709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17829467598721628324368945 13372100699041221243276709)
            ·
              refine ⟨2507268881070228983114383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13372100699041221243276709 2507268881070228983114383)
              ·
                refine ⟨3760903321605343474671575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507268881070228983114383 3760903321605343474671575)
                ·
                  refine ⟨5641354982408015212007363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3760903321605343474671575 5641354982408015212007363)
                  ·
                    refine ⟨8462032473612022818011045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5641354982408015212007363 8462032473612022818011045)
                    ·
                      refine ⟨1586631088802254278377071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8462032473612022818011045 1586631088802254278377071)
                      ·
                        rfl

theorem cell23_3089953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_3089953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089953 prefixEnd_3089953 := by exact prefixLift 3089953
  have htrace : WordTrace (prefixWord ++ tailWord_3089953) baseStart_3089953 baseEnd_3089953 := by
    simpa [prefixWord, tailWord_3089953, baseEnd_3089953] using wordTrace_append hprefix tailTrace_3089953
  have hstable : (prefixWord ++ tailWord_3089953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089953).length < 2 ^ (prefixWord ++ tailWord_3089953).sum := by decide
  have hdescent : baseEnd_3089953 < baseStart_3089953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089980 : List Nat := [2, 2, 2, 2, 4, 1, 3, 1, 2, 4]
def baseStart_3089980 : Nat := 118140960795 + 3089980 * 2 ^ 59
def prefixEnd_3089980 : Nat := 4983230072969 + 3 ^ 40 * 3089980 * 2
def baseEnd_3089980 : Nat := 528881650926641890913149

theorem tailTrace_3089980 : CollatzResearch.WordTrace tailWord_3089980 prefixEnd_3089980 528881650926641890913149 := by
  unfold tailWord_3089980
  simp only [CollatzResearch.WordTrace]
  refine ⟨56350414672768830707325697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75133886230358440943100929 56350414672768830707325697)
  ·
    refine ⟨42262811004576623030494273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56350414672768830707325697 42262811004576623030494273)
    ·
      refine ⟨31697108253432467272870705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42262811004576623030494273 31697108253432467272870705)
      ·
        refine ⟨23772831190074350454653029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31697108253432467272870705 23772831190074350454653029)
        ·
          refine ⟨4457405848138940710247443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23772831190074350454653029 4457405848138940710247443)
          ·
            refine ⟨6686108772208411065371165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4457405848138940710247443 6686108772208411065371165)
            ·
              refine ⟨2507290789578154149514187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6686108772208411065371165 2507290789578154149514187)
              ·
                refine ⟨3760936184367231224271281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507290789578154149514187 3760936184367231224271281)
                ·
                  refine ⟨2820702138275423418203461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3760936184367231224271281 2820702138275423418203461)
                  ·
                    refine ⟨528881650926641890913149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2820702138275423418203461 528881650926641890913149)
                    ·
                      rfl

theorem cell23_3089980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_3089980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3089980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3089980 prefixEnd_3089980 := by exact prefixLift 3089980
  have htrace : WordTrace (prefixWord ++ tailWord_3089980) baseStart_3089980 baseEnd_3089980 := by
    simpa [prefixWord, tailWord_3089980, baseEnd_3089980] using wordTrace_append hprefix tailTrace_3089980
  have hstable : (prefixWord ++ tailWord_3089980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089980).length < 2 ^ (prefixWord ++ tailWord_3089980).sum := by decide
  have hdescent : baseEnd_3089980 < baseStart_3089980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090037 : List Nat := [1, 3, 4, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_3090037 : Nat := 118140960795 + 3090037 * 2 ^ 59
def prefixEnd_3090037 : Nat := 4983230072969 + 3 ^ 40 * 3090037 * 2
def baseEnd_3090037 : Nat := 1586674221177231949726685

theorem tailTrace_3090037 : CollatzResearch.WordTrace tailWord_3090037 prefixEnd_3090037 1586674221177231949726685 := by
  unfold tailWord_3090037
  simp only [CollatzResearch.WordTrace]
  refine ⟨112702908306331160149476365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75135272204220773432984243 112702908306331160149476365)
  ·
    refine ⟨42263590614874185056053637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112702908306331160149476365 42263590614874185056053637)
    ·
      refine ⟨7924423240288909698010057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42263590614874185056053637 7924423240288909698010057)
      ·
        refine ⟨5943317430216682273507543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7924423240288909698010057 5943317430216682273507543)
        ·
          refine ⟨8914976145325023410261315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5943317430216682273507543 8914976145325023410261315)
          ·
            refine ⟨13372464217987535115391973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8914976145325023410261315 13372464217987535115391973)
            ·
              refine ⟨2507337040872662834135995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13372464217987535115391973 2507337040872662834135995)
              ·
                refine ⟨3761005561308994251203993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507337040872662834135995 3761005561308994251203993)
                ·
                  refine ⟨2820754170981745688402995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3761005561308994251203993 2820754170981745688402995)
                  ·
                    refine ⟨4231131256472618532604493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2820754170981745688402995 4231131256472618532604493)
                    ·
                      refine ⟨1586674221177231949726685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4231131256472618532604493 1586674221177231949726685)
                      ·
                        rfl

theorem cell23_3090037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_3090037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090037 prefixEnd_3090037 := by exact prefixLift 3090037
  have htrace : WordTrace (prefixWord ++ tailWord_3090037) baseStart_3090037 baseEnd_3090037 := by
    simpa [prefixWord, tailWord_3090037, baseEnd_3090037] using wordTrace_append hprefix tailTrace_3090037
  have hstable : (prefixWord ++ tailWord_3090037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090037).length < 2 ^ (prefixWord ++ tailWord_3090037).sum := by decide
  have hdescent : baseEnd_3090037 < baseStart_3090037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090039 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 4]
def baseStart_3090039 : Nat := 118140960795 + 3090039 * 2 ^ 59
def prefixEnd_3090039 : Nat := 4983230072969 + 3 ^ 40 * 3090039 * 2
def baseEnd_3090039 : Nat := 1586675248138540941901675

theorem tailTrace_3090039 : CollatzResearch.WordTrace tailWord_3090039 prefixEnd_3090039 1586675248138540941901675 := by
  unfold tailWord_3090039
  simp only [CollatzResearch.WordTrace]
  refine ⟨112702981252323914491049171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75135320834882609660699447 112702981252323914491049171)
  ·
    refine ⟨169054471878485871736573757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112702981252323914491049171 169054471878485871736573757)
    ·
      refine ⟨63395426954432201901215159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169054471878485871736573757 63395426954432201901215159)
      ·
        refine ⟨95093140431648302851822739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63395426954432201901215159 95093140431648302851822739)
        ·
          refine ⟨142639710647472454277734109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95093140431648302851822739 142639710647472454277734109)
          ·
            refine ⟨53489891492802170354150291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142639710647472454277734109 53489891492802170354150291)
            ·
              refine ⟨80234837239203255531225437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53489891492802170354150291 80234837239203255531225437)
              ·
                refine ⟨30088063964701220824209539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80234837239203255531225437 30088063964701220824209539)
                ·
                  refine ⟨45132095947051831236314309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30088063964701220824209539 45132095947051831236314309)
                  ·
                    refine ⟨8462267990072218356808933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45132095947051831236314309 8462267990072218356808933)
                    ·
                      refine ⟨1586675248138540941901675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8462267990072218356808933 1586675248138540941901675)
                      ·
                        rfl

theorem cell23_3090039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_3090039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090039 prefixEnd_3090039 := by exact prefixLift 3090039
  have htrace : WordTrace (prefixWord ++ tailWord_3090039) baseStart_3090039 baseEnd_3090039 := by
    simpa [prefixWord, tailWord_3090039, baseEnd_3090039] using wordTrace_append hprefix tailTrace_3090039
  have hstable : (prefixWord ++ tailWord_3090039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090039).length < 2 ^ (prefixWord ++ tailWord_3090039).sum := by decide
  have hdescent : baseEnd_3090039 < baseStart_3090039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090089 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 5, 2, 5]
def baseStart_3090089 : Nat := 118140960795 + 3090089 * 2 ^ 59
def prefixEnd_3090089 : Nat := 4983230072969 + 3 ^ 40 * 3090089 * 2
def baseEnd_3090089 : Nat := 1586700922171265746276445

theorem tailTrace_3090089 : CollatzResearch.WordTrace tailWord_3090089 prefixEnd_3090089 1586700922171265746276445 := by
  unfold tailWord_3090089
  simp only [CollatzResearch.WordTrace]
  refine ⟨112704804902142773030369321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75136536601428515353579547 112704804902142773030369321)
  ·
    refine ⟨84528603676607079772776991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112704804902142773030369321 84528603676607079772776991)
    ·
      refine ⟨126792905514910619659165487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84528603676607079772776991 126792905514910619659165487)
      ·
        refine ⟨190189358272365929488748231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126792905514910619659165487 190189358272365929488748231)
        ·
          refine ⟨285284037408548894233122347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190189358272365929488748231 285284037408548894233122347)
          ·
            refine ⟨427926056112823341349683521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285284037408548894233122347 427926056112823341349683521)
            ·
              refine ⟨320944542084617506012262641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427926056112823341349683521 320944542084617506012262641)
              ·
                refine ⟨240708406563463129509196981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320944542084617506012262641 240708406563463129509196981)
                ·
                  refine ⟨22566413115324668391487217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 240708406563463129509196981 22566413115324668391487217)
                  ·
                    refine ⟨16924809836493501293615413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22566413115324668391487217 16924809836493501293615413)
                    ·
                      refine ⟨1586700922171265746276445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16924809836493501293615413 1586700922171265746276445)
                      ·
                        rfl

theorem cell23_3090089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_3090089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090089 prefixEnd_3090089 := by exact prefixLift 3090089
  have htrace : WordTrace (prefixWord ++ tailWord_3090089) baseStart_3090089 baseEnd_3090089 := by
    simpa [prefixWord, tailWord_3090089, baseEnd_3090089] using wordTrace_append hprefix tailTrace_3090089
  have hstable : (prefixWord ++ tailWord_3090089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090089).length < 2 ^ (prefixWord ++ tailWord_3090089).sum := by decide
  have hdescent : baseEnd_3090089 < baseStart_3090089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090093 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_3090093 : Nat := 118140960795 + 3090093 * 2 ^ 59
def prefixEnd_3090093 : Nat := 4983230072969 + 3 ^ 40 * 3090093 * 2
def baseEnd_3090093 : Nat := 1586702976093883730626427

theorem tailTrace_3090093 : CollatzResearch.WordTrace tailWord_3090093 prefixEnd_3090093 1586702976093883730626427 := by
  unfold tailWord_3090093
  simp only [CollatzResearch.WordTrace]
  refine ⟨112704950794128281713514933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75136633862752187809009955 112704950794128281713514933)
  ·
    refine ⟨10566089136949526410642025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112704950794128281713514933 10566089136949526410642025)
    ·
      refine ⟨7924566852712144807981519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10566089136949526410642025 7924566852712144807981519)
      ·
        refine ⟨11886850279068217211972279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7924566852712144807981519 11886850279068217211972279)
        ·
          refine ⟨17830275418602325817958419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11886850279068217211972279 17830275418602325817958419)
          ·
            refine ⟨26745413127903488726937629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17830275418602325817958419 26745413127903488726937629)
            ·
              refine ⟨10029529922963808272601611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26745413127903488726937629 10029529922963808272601611)
              ·
                refine ⟨15044294884445712408902417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10029529922963808272601611 15044294884445712408902417)
                ·
                  refine ⟨11283221163334284306676813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15044294884445712408902417 11283221163334284306676813)
                  ·
                    refine ⟨4231207936250356615003805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11283221163334284306676813 4231207936250356615003805)
                    ·
                      refine ⟨1586702976093883730626427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4231207936250356615003805 1586702976093883730626427)
                      ·
                        rfl

theorem cell23_3090093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_3090093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090093 prefixEnd_3090093 := by exact prefixLift 3090093
  have htrace : WordTrace (prefixWord ++ tailWord_3090093) baseStart_3090093 baseEnd_3090093 := by
    simpa [prefixWord, tailWord_3090093, baseEnd_3090093] using wordTrace_append hprefix tailTrace_3090093
  have hstable : (prefixWord ++ tailWord_3090093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090093).length < 2 ^ (prefixWord ++ tailWord_3090093).sum := by decide
  have hdescent : baseEnd_3090093 < baseStart_3090093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090143 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 3, 4]
def baseStart_3090143 : Nat := 118140960795 + 3090143 * 2 ^ 59
def prefixEnd_3090143 : Nat := 4983230072969 + 3 ^ 40 * 3090143 * 2
def baseEnd_3090143 : Nat := 528909550042202845000399

theorem tailTrace_3090143 : CollatzResearch.WordTrace tailWord_3090143 prefixEnd_3090143 528909550042202845000399 := by
  unfold tailWord_3090143
  simp only [CollatzResearch.WordTrace]
  refine ⟨112706774443947140252835083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75137849629298093501890055 112706774443947140252835083)
  ·
    refine ⟨169060161665920710379252625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112706774443947140252835083 169060161665920710379252625)
    ·
      refine ⟨126795121249440532784439469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169060161665920710379252625 126795121249440532784439469)
      ·
        refine ⟨47548170468540199794164801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126795121249440532784439469 47548170468540199794164801)
        ·
          refine ⟨35661127851405149845623601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47548170468540199794164801 35661127851405149845623601)
          ·
            refine ⟨26745845888553862384217701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35661127851405149845623601 26745845888553862384217701)
            ·
              refine ⟨5014846104103849197040819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26745845888553862384217701 5014846104103849197040819)
              ·
                refine ⟨7522269156155773795561229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5014846104103849197040819 7522269156155773795561229)
                ·
                  refine ⟨2820850933558415173335461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7522269156155773795561229 2820850933558415173335461)
                  ·
                    refine ⟨528909550042202845000399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2820850933558415173335461 528909550042202845000399)
                    ·
                      rfl

theorem cell23_3090143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 4].length) (baseStart_3090143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090143 prefixEnd_3090143 := by exact prefixLift 3090143
  have htrace : WordTrace (prefixWord ++ tailWord_3090143) baseStart_3090143 baseEnd_3090143 := by
    simpa [prefixWord, tailWord_3090143, baseEnd_3090143] using wordTrace_append hprefix tailTrace_3090143
  have hstable : (prefixWord ++ tailWord_3090143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090143).length < 2 ^ (prefixWord ++ tailWord_3090143).sum := by decide
  have hdescent : baseEnd_3090143 < baseStart_3090143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090156 : List Nat := [2, 2, 1, 1, 2, 2, 2, 5, 6]
def baseStart_3090156 : Nat := 118140960795 + 3090156 * 2 ^ 59
def prefixEnd_3090156 : Nat := 4983230072969 + 3 ^ 40 * 3090156 * 2
def baseEnd_3090156 : Nat := 176303925041679664904293

theorem tailTrace_3090156 : CollatzResearch.WordTrace tailWord_3090156 prefixEnd_3090156 176303925041679664904293 := by
  unfold tailWord_3090156
  simp only [CollatzResearch.WordTrace]
  refine ⟨56353624296450021736529161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75138165728600028982038881 56353624296450021736529161)
  ·
    refine ⟨42265218222337516302396871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56353624296450021736529161 42265218222337516302396871)
    ·
      refine ⟨63397827333506274453595307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42265218222337516302396871 63397827333506274453595307)
      ·
        refine ⟨95096741000259411680392961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63397827333506274453595307 95096741000259411680392961)
        ·
          refine ⟨71322555750194558760294721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95096741000259411680392961 71322555750194558760294721)
          ·
            refine ⟨53491916812645919070221041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71322555750194558760294721 53491916812645919070221041)
            ·
              refine ⟨40118937609484439302665781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53491916812645919070221041 40118937609484439302665781)
              ·
                refine ⟨3761150400889166184624917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40118937609484439302665781 3761150400889166184624917)
                ·
                  refine ⟨176303925041679664904293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3761150400889166184624917 176303925041679664904293)
                  ·
                    rfl

theorem cell23_3090156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 6].length) (baseStart_3090156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090156 prefixEnd_3090156 := by exact prefixLift 3090156
  have htrace : WordTrace (prefixWord ++ tailWord_3090156) baseStart_3090156 baseEnd_3090156 := by
    simpa [prefixWord, tailWord_3090156, baseEnd_3090156] using wordTrace_append hprefix tailTrace_3090156
  have hstable : (prefixWord ++ tailWord_3090156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090156).length < 2 ^ (prefixWord ++ tailWord_3090156).sum := by decide
  have hdescent : baseEnd_3090156 < baseStart_3090156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090200 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 3, 1, 3]
def baseStart_3090200 : Nat := 118140960795 + 3090200 * 2 ^ 59
def prefixEnd_3090200 : Nat := 4983230072969 + 3 ^ 40 * 3090200 * 2
def baseEnd_3090200 : Nat := 1586757918523914811988435

theorem tailTrace_3090200 : CollatzResearch.WordTrace tailWord_3090200 prefixEnd_3090200 1586757918523914811988435 := by
  unfold tailWord_3090200
  simp only [CollatzResearch.WordTrace]
  refine ⟨56354426702370319493830027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75139235603160425991773369 56354426702370319493830027)
  ·
    refine ⟨84531640053555479240745041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56354426702370319493830027 84531640053555479240745041)
    ·
      refine ⟨63398730040166609430558781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84531640053555479240745041 63398730040166609430558781)
      ·
        refine ⟨23774523765062478536459543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63398730040166609430558781 23774523765062478536459543)
        ·
          refine ⟨35661785647593717804689315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23774523765062478536459543 35661785647593717804689315)
          ·
            refine ⟨53492678471390576707033973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35661785647593717804689315 53492678471390576707033973)
            ·
              refine ⟨5014938606692866566284435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53492678471390576707033973 5014938606692866566284435)
              ·
                refine ⟨7522407910039299849426653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5014938606692866566284435 7522407910039299849426653)
                ·
                  refine ⟨2820902966264737443534995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7522407910039299849426653 2820902966264737443534995)
                  ·
                    refine ⟨4231354449397106165302493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2820902966264737443534995 4231354449397106165302493)
                    ·
                      refine ⟨1586757918523914811988435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4231354449397106165302493 1586757918523914811988435)
                      ·
                        rfl

theorem cell23_3090200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_3090200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090200 prefixEnd_3090200 := by exact prefixLift 3090200
  have htrace : WordTrace (prefixWord ++ tailWord_3090200) baseStart_3090200 baseEnd_3090200 := by
    simpa [prefixWord, tailWord_3090200, baseEnd_3090200] using wordTrace_append hprefix tailTrace_3090200
  have hstable : (prefixWord ++ tailWord_3090200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090200).length < 2 ^ (prefixWord ++ tailWord_3090200).sum := by decide
  have hdescent : baseEnd_3090200 < baseStart_3090200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090210 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 4, 3, 2]
def baseStart_3090210 : Nat := 118140960795 + 3090210 * 2 ^ 59
def prefixEnd_3090210 : Nat := 4983230072969 + 3 ^ 40 * 3090210 * 2
def baseEnd_3090210 : Nat := 1586763053330459772863389

theorem tailTrace_3090210 : CollatzResearch.WordTrace tailWord_3090210 prefixEnd_3090210 1586763053330459772863389 := by
  unfold tailWord_3090210
  simp only [CollatzResearch.WordTrace]
  refine ⟨28177304533676102673881021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75139478756469607130349389 28177304533676102673881021)
  ·
    refine ⟨10566489200128538502705383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28177304533676102673881021 10566489200128538502705383)
    ·
      refine ⟨15849733800192807754058075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10566489200128538502705383 15849733800192807754058075)
      ·
        refine ⟨23774600700289211631087113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15849733800192807754058075 23774600700289211631087113)
        ·
          refine ⟨17830950525216908723315335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23774600700289211631087113 17830950525216908723315335)
          ·
            refine ⟨26746425787825363084973003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17830950525216908723315335 26746425787825363084973003)
            ·
              refine ⟨40119638681738044627459505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26746425787825363084973003 40119638681738044627459505)
              ·
                refine ⟨30089729011303533470594629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40119638681738044627459505 30089729011303533470594629)
                ·
                  refine ⟨5641824189619412525736493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30089729011303533470594629 5641824189619412525736493)
                  ·
                    refine ⟨2115684071107279697151185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5641824189619412525736493 2115684071107279697151185)
                    ·
                      refine ⟨1586763053330459772863389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115684071107279697151185 1586763053330459772863389)
                      ·
                        rfl

theorem cell23_3090210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_3090210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090210 prefixEnd_3090210 := by exact prefixLift 3090210
  have htrace : WordTrace (prefixWord ++ tailWord_3090210) baseStart_3090210 baseEnd_3090210 := by
    simpa [prefixWord, tailWord_3090210, baseEnd_3090210] using wordTrace_append hprefix tailTrace_3090210
  have hstable : (prefixWord ++ tailWord_3090210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090210).length < 2 ^ (prefixWord ++ tailWord_3090210).sum := by decide
  have hdescent : baseEnd_3090210 < baseStart_3090210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090220 : List Nat := [2, 2, 1, 1, 1, 7, 1, 2, 1, 5]
def baseStart_3090220 : Nat := 118140960795 + 3090220 * 2 ^ 59
def prefixEnd_3090220 : Nat := 4983230072969 + 3 ^ 40 * 3090220 * 2
def baseEnd_3090220 : Nat := 528922729379001577912781

theorem tailTrace_3090220 : CollatzResearch.WordTrace tailWord_3090220 prefixEnd_3090220 528922729379001577912781 := by
  unfold tailWord_3090220
  simp only [CollatzResearch.WordTrace]
  refine ⟨56354791432334091201694057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75139721909778788268925409 56354791432334091201694057)
  ·
    refine ⟨42266093574250568401270543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56354791432334091201694057 42266093574250568401270543)
    ·
      refine ⟨63399140361375852601905815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42266093574250568401270543 63399140361375852601905815)
      ·
        refine ⟨95098710542063778902858723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63399140361375852601905815 95098710542063778902858723)
        ·
          refine ⟨142648065813095668354288085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95098710542063778902858723 142648065813095668354288085)
          ·
            refine ⟨3343314042494429727053627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 142648065813095668354288085 3343314042494429727053627)
            ·
              refine ⟨5014971063741644590580441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3343314042494429727053627 5014971063741644590580441)
              ·
                refine ⟨3761228297806233442935331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5014971063741644590580441 3761228297806233442935331)
                ·
                  refine ⟨5641842446709350164402997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3761228297806233442935331 5641842446709350164402997)
                  ·
                    refine ⟨528922729379001577912781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5641842446709350164402997 528922729379001577912781)
                    ·
                      rfl

theorem cell23_3090220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_3090220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090220 prefixEnd_3090220 := by exact prefixLift 3090220
  have htrace : WordTrace (prefixWord ++ tailWord_3090220) baseStart_3090220 baseEnd_3090220 := by
    simpa [prefixWord, tailWord_3090220, baseEnd_3090220] using wordTrace_append hprefix tailTrace_3090220
  have hstable : (prefixWord ++ tailWord_3090220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090220).length < 2 ^ (prefixWord ++ tailWord_3090220).sum := by decide
  have hdescent : baseEnd_3090220 < baseStart_3090220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090227 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 2, 3, 2]
def baseStart_3090227 : Nat := 118140960795 + 3090227 * 2 ^ 59
def prefixEnd_3090227 : Nat := 4983230072969 + 3 ^ 40 * 3090227 * 2
def baseEnd_3090227 : Nat := 1586771782501586206350811

theorem tailTrace_3090227 : CollatzResearch.WordTrace tailWord_3090227 prefixEnd_3090227 1586771782501586206350811 := by
  unfold tailWord_3090227
  simp only [CollatzResearch.WordTrace]
  refine ⟨112709838175642822598892935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75139892117095215065928623 112709838175642822598892935)
  ·
    refine ⟨169064757263464233898339403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112709838175642822598892935 169064757263464233898339403)
    ·
      refine ⟨253597135895196350847509105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169064757263464233898339403 253597135895196350847509105)
      ·
        refine ⟨190197851921397263135631829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253597135895196350847509105 190197851921397263135631829)
        ·
          refine ⟨4457762154407748354741371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 190197851921397263135631829 4457762154407748354741371)
          ·
            refine ⟨6686643231611622532112057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4457762154407748354741371 6686643231611622532112057)
            ·
              refine ⟨5014982423708716899084043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6686643231611622532112057 5014982423708716899084043)
              ·
                refine ⟨7522473635563075348626065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5014982423708716899084043 7522473635563075348626065)
                ·
                  refine ⟨5641855226672306511469549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7522473635563075348626065 5641855226672306511469549)
                  ·
                    refine ⟨2115695710002114941801081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5641855226672306511469549 2115695710002114941801081)
                    ·
                      refine ⟨1586771782501586206350811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115695710002114941801081 1586771782501586206350811)
                      ·
                        rfl

theorem cell23_3090227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 3, 2].length) (baseStart_3090227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090227 prefixEnd_3090227 := by exact prefixLift 3090227
  have htrace : WordTrace (prefixWord ++ tailWord_3090227) baseStart_3090227 baseEnd_3090227 := by
    simpa [prefixWord, tailWord_3090227, baseEnd_3090227] using wordTrace_append hprefix tailTrace_3090227
  have hstable : (prefixWord ++ tailWord_3090227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090227).length < 2 ^ (prefixWord ++ tailWord_3090227).sum := by decide
  have hdescent : baseEnd_3090227 < baseStart_3090227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090237 : List Nat := [1, 4, 1, 4, 1, 2, 3, 1, 1, 5]
def baseStart_3090237 : Nat := 118140960795 + 3090237 * 2 ^ 59
def prefixEnd_3090237 : Nat := 4983230072969 + 3 ^ 40 * 3090237 * 2
def baseEnd_3090237 : Nat := 528925639102710389075255

theorem tailTrace_3090237 : CollatzResearch.WordTrace tailWord_3090237 prefixEnd_3090237 528925639102710389075255 := by
  unfold tailWord_3090237
  simp only [CollatzResearch.WordTrace]
  refine ⟨112710202905606594306756965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75140135270404396204504643 112710202905606594306756965)
  ·
    refine ⟨21133163044801236432516931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112710202905606594306756965 21133163044801236432516931)
    ·
      refine ⟨31699744567201854648775397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21133163044801236432516931 31699744567201854648775397)
      ·
        refine ⟨5943702106350347746645387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31699744567201854648775397 5943702106350347746645387)
        ·
          refine ⟨8915553159525521619968081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5943702106350347746645387 8915553159525521619968081)
          ·
            refine ⟨6686664869644141214976061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8915553159525521619968081 6686664869644141214976061)
            ·
              refine ⟨2507499326116552955616023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6686664869644141214976061 2507499326116552955616023)
              ·
                refine ⟨3761248989174829433424035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507499326116552955616023 3761248989174829433424035)
                ·
                  refine ⟨5641873483762244150136053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3761248989174829433424035 5641873483762244150136053)
                  ·
                    refine ⟨528925639102710389075255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5641873483762244150136053 528925639102710389075255)
                    ·
                      rfl

theorem cell23_3090237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_3090237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090237 prefixEnd_3090237 := by exact prefixLift 3090237
  have htrace : WordTrace (prefixWord ++ tailWord_3090237) baseStart_3090237 baseEnd_3090237 := by
    simpa [prefixWord, tailWord_3090237, baseEnd_3090237] using wordTrace_append hprefix tailTrace_3090237
  have hstable : (prefixWord ++ tailWord_3090237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090237).length < 2 ^ (prefixWord ++ tailWord_3090237).sum := by decide
  have hdescent : baseEnd_3090237 < baseStart_3090237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090243 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 5]
def baseStart_3090243 : Nat := 118140960795 + 3090243 * 2 ^ 59
def prefixEnd_3090243 : Nat := 4983230072969 + 3 ^ 40 * 3090243 * 2
def baseEnd_3090243 : Nat := 1586779998192058143750737

theorem tailTrace_3090243 : CollatzResearch.WordTrace tailWord_3090243 prefixEnd_3090243 1586779998192058143750737 := by
  unfold tailWord_3090243
  simp only [CollatzResearch.WordTrace]
  refine ⟨112710421743584857331475383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75140281162389904887650255 112710421743584857331475383)
  ·
    refine ⟨169065632615377285997213075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112710421743584857331475383 169065632615377285997213075)
    ·
      refine ⟨253598448923065928995819613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169065632615377285997213075 253598448923065928995819613)
      ·
        refine ⟨95099418346149723373432355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253598448923065928995819613 95099418346149723373432355)
        ·
          refine ⟨142649127519224585060148533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95099418346149723373432355 142649127519224585060148533)
          ·
            refine ⟨13373355704927304849388925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142649127519224585060148533 13373355704927304849388925)
            ·
              refine ⟨5015008389347739318520847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13373355704927304849388925 5015008389347739318520847)
              ·
                refine ⟨7522512584021608977781271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5015008389347739318520847 7522512584021608977781271)
                ·
                  refine ⟨11283768876032413466671907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7522512584021608977781271 11283768876032413466671907)
                  ·
                    refine ⟨16925653314048620200007861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11283768876032413466671907 16925653314048620200007861)
                    ·
                      refine ⟨1586779998192058143750737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16925653314048620200007861 1586779998192058143750737)
                      ·
                        rfl

theorem cell23_3090243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_3090243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090243 prefixEnd_3090243 := by exact prefixLift 3090243
  have htrace : WordTrace (prefixWord ++ tailWord_3090243) baseStart_3090243 baseEnd_3090243 := by
    simpa [prefixWord, tailWord_3090243, baseEnd_3090243] using wordTrace_append hprefix tailTrace_3090243
  have hstable : (prefixWord ++ tailWord_3090243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090243).length < 2 ^ (prefixWord ++ tailWord_3090243).sum := by decide
  have hdescent : baseEnd_3090243 < baseStart_3090243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090250 : List Nat := [3, 1, 2, 1, 1, 1, 6, 2, 2, 4]
def baseStart_3090250 : Nat := 118140960795 + 3090250 * 2 ^ 59
def prefixEnd_3090250 : Nat := 4983230072969 + 3 ^ 40 * 3090250 * 2
def baseEnd_3090250 : Nat := 528927864185546538787735

theorem tailTrace_3090250 : CollatzResearch.WordTrace tailWord_3090250 prefixEnd_3090250 528927864185546538787735 := by
  unfold tailWord_3090250
  simp only [CollatzResearch.WordTrace]
  refine ⟨28177669263639874381745051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75140451369706331684653469 28177669263639874381745051)
  ·
    refine ⟨42266503895459811572617577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28177669263639874381745051 42266503895459811572617577)
    ·
      refine ⟨31699877921594858679463183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42266503895459811572617577 31699877921594858679463183)
      ·
        refine ⟨47549816882392288019194775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31699877921594858679463183 47549816882392288019194775)
        ·
          refine ⟨71324725323588432028792163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47549816882392288019194775 71324725323588432028792163)
          ·
            refine ⟨106987087985382648043188245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71324725323588432028792163 106987087985382648043188245)
            ·
              refine ⟨5015019749314811627024449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106987087985382648043188245 5015019749314811627024449)
              ·
                refine ⟨3761264811986108720268337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5015019749314811627024449 3761264811986108720268337)
                ·
                  refine ⟨2820948608989581540201253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3761264811986108720268337 2820948608989581540201253)
                  ·
                    refine ⟨528927864185546538787735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2820948608989581540201253 528927864185546538787735)
                    ·
                      rfl

theorem cell23_3090250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_3090250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090250 prefixEnd_3090250 := by exact prefixLift 3090250
  have htrace : WordTrace (prefixWord ++ tailWord_3090250) baseStart_3090250 baseEnd_3090250 := by
    simpa [prefixWord, tailWord_3090250, baseEnd_3090250] using wordTrace_append hprefix tailTrace_3090250
  have hstable : (prefixWord ++ tailWord_3090250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090250).length < 2 ^ (prefixWord ++ tailWord_3090250).sum := by decide
  have hdescent : baseEnd_3090250 < baseStart_3090250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090260 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_3090260 : Nat := 118140960795 + 3090260 * 2 ^ 59
def prefixEnd_3090260 : Nat := 4983230072969 + 3 ^ 40 * 3090260 * 2
def baseEnd_3090260 : Nat := 1586788727363184577238159

theorem tailTrace_3090260 : CollatzResearch.WordTrace tailWord_3090260 prefixEnd_3090260 1586788727363184577238159 := by
  unfold tailWord_3090260
  simp only [CollatzResearch.WordTrace]
  refine ⟨56355520892261634617422117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75140694523015512823229489 56355520892261634617422117)
  ·
    refine ⟨10566660167299056490766647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56355520892261634617422117 10566660167299056490766647)
    ·
      refine ⟨15849990250948584736149971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10566660167299056490766647 15849990250948584736149971)
      ·
        refine ⟨23774985376422877104224957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15849990250948584736149971 23774985376422877104224957)
        ·
          refine ⟨8915619516158578914084359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23774985376422877104224957 8915619516158578914084359)
          ·
            refine ⟨13373429274237868371126539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8915619516158578914084359 13373429274237868371126539)
            ·
              refine ⟨20060143911356802556689809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13373429274237868371126539 20060143911356802556689809)
              ·
                refine ⟨15045107933517601917517357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20060143911356802556689809 15045107933517601917517357)
                ·
                  refine ⟨5641915475069100719069009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15045107933517601917517357 5641915475069100719069009)
                  ·
                    refine ⟨4231436606301825539301757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5641915475069100719069009 4231436606301825539301757)
                    ·
                      refine ⟨1586788727363184577238159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4231436606301825539301757 1586788727363184577238159)
                      ·
                        rfl

theorem cell23_3090260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_3090260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090260 prefixEnd_3090260 := by exact prefixLift 3090260
  have htrace : WordTrace (prefixWord ++ tailWord_3090260) baseStart_3090260 baseEnd_3090260 := by
    simpa [prefixWord, tailWord_3090260, baseEnd_3090260] using wordTrace_append hprefix tailTrace_3090260
  have hstable : (prefixWord ++ tailWord_3090260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090260).length < 2 ^ (prefixWord ++ tailWord_3090260).sum := by decide
  have hdescent : baseEnd_3090260 < baseStart_3090260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090274 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_3090274 : Nat := 118140960795 + 3090274 * 2 ^ 59
def prefixEnd_3090274 : Nat := 4983230072969 + 3 ^ 40 * 3090274 * 2
def baseEnd_3090274 : Nat := 1586795916092347522463095

theorem tailTrace_3090274 : CollatzResearch.WordTrace tailWord_3090274 prefixEnd_3090274 1586795916092347522463095 := by
  unfold tailWord_3090274
  simp only [CollatzResearch.WordTrace]
  refine ⟨28177888101618137406463469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75141034937648366417235917 28177888101618137406463469)
  ·
    refine ⟨10566708038106801527423801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28177888101618137406463469 10566708038106801527423801)
    ·
      refine ⟨7925031028580101145567851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10566708038106801527423801 7925031028580101145567851)
      ·
        refine ⟨11887546542870151718351777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7925031028580101145567851 11887546542870151718351777)
        ·
          refine ⟨8915659907152613788763833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11887546542870151718351777 8915659907152613788763833)
          ·
            refine ⟨6686744930364460341572875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8915659907152613788763833 6686744930364460341572875)
            ·
              refine ⟨10030117395546690512359313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6686744930364460341572875 10030117395546690512359313)
              ·
                refine ⟨7522588046660017884269485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10030117395546690512359313 7522588046660017884269485)
                ·
                  refine ⟨2820970517497506706601057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7522588046660017884269485 2820970517497506706601057)
                  ·
                    refine ⟨2115727888123130029950793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2820970517497506706601057 2115727888123130029950793)
                    ·
                      refine ⟨1586795916092347522463095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115727888123130029950793 1586795916092347522463095)
                      ·
                        rfl

theorem cell23_3090274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_3090274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090274 prefixEnd_3090274 := by exact prefixLift 3090274
  have htrace : WordTrace (prefixWord ++ tailWord_3090274) baseStart_3090274 baseEnd_3090274 := by
    simpa [prefixWord, tailWord_3090274, baseEnd_3090274] using wordTrace_append hprefix tailTrace_3090274
  have hstable : (prefixWord ++ tailWord_3090274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090274).length < 2 ^ (prefixWord ++ tailWord_3090274).sum := by decide
  have hdescent : baseEnd_3090274 < baseStart_3090274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090290 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 4, 1, 3]
def baseStart_3090290 : Nat := 118140960795 + 3090290 * 2 ^ 59
def prefixEnd_3090290 : Nat := 4983230072969 + 3 ^ 40 * 3090290 * 2
def baseEnd_3090290 : Nat := 1586804131782819459863021

theorem tailTrace_3090290 : CollatzResearch.WordTrace tailWord_3090290 prefixEnd_3090290 1586804131782819459863021 := by
  unfold tailWord_3090290
  simp only [CollatzResearch.WordTrace]
  refine ⟨28178033993603646089609081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75141423982943056238957549 28178033993603646089609081)
  ·
    refine ⟨21133525495202734567206811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28178033993603646089609081 21133525495202734567206811)
    ·
      refine ⟨31700288242804101850810217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21133525495202734567206811 31700288242804101850810217)
      ·
        refine ⟨23775216182103076388107663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31700288242804101850810217 23775216182103076388107663)
        ·
          refine ⟨35662824273154614582161495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23775216182103076388107663 35662824273154614582161495)
          ·
            refine ⟨53494236409731921873242243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35662824273154614582161495 53494236409731921873242243)
            ·
              refine ⟨80241354614597882809863365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53494236409731921873242243 80241354614597882809863365)
              ·
                refine ⟨15045253990237103026849381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80241354614597882809863365 15045253990237103026849381)
                ·
                  refine ⟨2820985123169456817534259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15045253990237103026849381 2820985123169456817534259)
                  ·
                    refine ⟨4231477684754185226301389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2820985123169456817534259 4231477684754185226301389)
                    ·
                      refine ⟨1586804131782819459863021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4231477684754185226301389 1586804131782819459863021)
                      ·
                        rfl

theorem cell23_3090290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_3090290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090290 prefixEnd_3090290 := by exact prefixLift 3090290
  have htrace : WordTrace (prefixWord ++ tailWord_3090290) baseStart_3090290 baseEnd_3090290 := by
    simpa [prefixWord, tailWord_3090290, baseEnd_3090290] using wordTrace_append hprefix tailTrace_3090290
  have hstable : (prefixWord ++ tailWord_3090290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090290).length < 2 ^ (prefixWord ++ tailWord_3090290).sum := by decide
  have hdescent : baseEnd_3090290 < baseStart_3090290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090294 : List Nat := [5, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3090294 : Nat := 118140960795 + 3090294 * 2 ^ 59
def prefixEnd_3090294 : Nat := 4983230072969 + 3 ^ 40 * 3090294 * 2
def baseEnd_3090294 : Nat := 1586806185705437444213003

theorem tailTrace_3090294 : CollatzResearch.WordTrace tailWord_3090294 prefixEnd_3090294 1586806185705437444213003 := by
  unfold tailWord_3090294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7044517616650005815098871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75141521244266728694387957 7044517616650005815098871)
  ·
    refine ⟨10566776424975008722648307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7044517616650005815098871 10566776424975008722648307)
    ·
      refine ⟨15850164637462513083972461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10566776424975008722648307 15850164637462513083972461)
      ·
        refine ⟨5943811739048442406489673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15850164637462513083972461 5943811739048442406489673)
        ·
          refine ⟨4457858804286331804867255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5943811739048442406489673 4457858804286331804867255)
          ·
            refine ⟨6686788206429497707300883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4457858804286331804867255 6686788206429497707300883)
            ·
              refine ⟨10030182309644246560951325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6686788206429497707300883 10030182309644246560951325)
              ·
                refine ⟨3761318366116592460356747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10030182309644246560951325 3761318366116592460356747)
                ·
                  refine ⟨5641977549174888690535121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3761318366116592460356747 5641977549174888690535121)
                  ·
                    refine ⟨4231483161881166517901341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5641977549174888690535121 4231483161881166517901341)
                    ·
                      refine ⟨1586806185705437444213003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4231483161881166517901341 1586806185705437444213003)
                      ·
                        rfl

theorem cell23_3090294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3090294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090294 prefixEnd_3090294 := by exact prefixLift 3090294
  have htrace : WordTrace (prefixWord ++ tailWord_3090294) baseStart_3090294 baseEnd_3090294 := by
    simpa [prefixWord, tailWord_3090294, baseEnd_3090294] using wordTrace_append hprefix tailTrace_3090294
  have hstable : (prefixWord ++ tailWord_3090294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090294).length < 2 ^ (prefixWord ++ tailWord_3090294).sum := by decide
  have hdescent : baseEnd_3090294 < baseStart_3090294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090307 : List Nat := [1, 1, 1, 3, 4, 2, 3, 2, 2, 1, 3]
def baseStart_3090307 : Nat := 118140960795 + 3090307 * 2 ^ 59
def prefixEnd_3090307 : Nat := 4983230072969 + 3 ^ 40 * 3090307 * 2
def baseEnd_3090307 : Nat := 1586812860953945893350443

theorem tailTrace_3090307 : CollatzResearch.WordTrace tailWord_3090307 prefixEnd_3090307 1586812860953945893350443 := by
  unfold tailWord_3090307
  simp only [CollatzResearch.WordTrace]
  refine ⟨112712756015352996261805175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75141837343568664174536783 112712756015352996261805175)
  ·
    refine ⟨169069134023029494392707763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112712756015352996261805175 169069134023029494392707763)
    ·
      refine ⟨253603701034544241589061645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169069134023029494392707763 253603701034544241589061645)
      ·
        refine ⟨95101387887954090595898117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253603701034544241589061645 95101387887954090595898117)
        ·
          refine ⟨17831510228991391986730897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95101387887954090595898117 17831510228991391986730897)
          ·
            refine ⟨13373632671743543990048173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17831510228991391986730897 13373632671743543990048173)
            ·
              refine ⟨5015112251903828996268065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13373632671743543990048173 5015112251903828996268065)
              ·
                refine ⟨3761334188927871747201049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5015112251903828996268065 3761334188927871747201049)
                ·
                  refine ⟨2821000641695903810400787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3761334188927871747201049 2821000641695903810400787)
                  ·
                    refine ⟨4231500962543855715601181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2821000641695903810400787 4231500962543855715601181)
                    ·
                      refine ⟨1586812860953945893350443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4231500962543855715601181 1586812860953945893350443)
                      ·
                        rfl

theorem cell23_3090307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_3090307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090307 prefixEnd_3090307 := by exact prefixLift 3090307
  have htrace : WordTrace (prefixWord ++ tailWord_3090307) baseStart_3090307 baseEnd_3090307 := by
    simpa [prefixWord, tailWord_3090307, baseEnd_3090307] using wordTrace_append hprefix tailTrace_3090307
  have hstable : (prefixWord ++ tailWord_3090307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090307).length < 2 ^ (prefixWord ++ tailWord_3090307).sum := by decide
  have hdescent : baseEnd_3090307 < baseStart_3090307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090383 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 4, 5]
def baseStart_3090383 : Nat := 118140960795 + 3090383 * 2 ^ 59
def prefixEnd_3090383 : Nat := 4983230072969 + 3 ^ 40 * 3090383 * 2
def baseEnd_3090383 : Nat := 528950628494562532000031

theorem tailTrace_3090383 : CollatzResearch.WordTrace tailWord_3090383 prefixEnd_3090383 528950628494562532000031 := by
  unfold tailWord_3090383
  simp only [CollatzResearch.WordTrace]
  refine ⟨112715527963077661241571803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75143685308718440827714535 112715527963077661241571803)
  ·
    refine ⟨169073291944616491862357705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112715527963077661241571803 169073291944616491862357705)
    ·
      refine ⟨126804968958462368896768279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169073291944616491862357705 126804968958462368896768279)
      ·
        refine ⟨190207453437693553345152419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126804968958462368896768279 190207453437693553345152419)
        ·
          refine ⟨285311180156540330017728629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190207453437693553345152419 285311180156540330017728629)
          ·
            refine ⟨26747923139675655939162059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 285311180156540330017728629 26747923139675655939162059)
            ·
              refine ⟨40121884709513483908743089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26747923139675655939162059 40121884709513483908743089)
              ·
                refine ⟨30091413532135112931557317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40121884709513483908743089 30091413532135112931557317)
                ·
                  refine ⟨5642140037275333674666997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30091413532135112931557317 5642140037275333674666997)
                  ·
                    refine ⟨528950628494562532000031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5642140037275333674666997 528950628494562532000031)
                    ·
                      rfl

theorem cell23_3090383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 5].length) (baseStart_3090383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090383 prefixEnd_3090383 := by exact prefixLift 3090383
  have htrace : WordTrace (prefixWord ++ tailWord_3090383) baseStart_3090383 baseEnd_3090383 := by
    simpa [prefixWord, tailWord_3090383, baseEnd_3090383] using wordTrace_append hprefix tailTrace_3090383
  have hstable : (prefixWord ++ tailWord_3090383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090383).length < 2 ^ (prefixWord ++ tailWord_3090383).sum := by decide
  have hdescent : baseEnd_3090383 < baseStart_3090383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090437 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 2, 4, 2]
def baseStart_3090437 : Nat := 118140960795 + 3090437 * 2 ^ 59
def prefixEnd_3090437 : Nat := 4983230072969 + 3 ^ 40 * 3090437 * 2
def baseEnd_3090437 : Nat := 1586879613439030384724845

theorem tailTrace_3090437 : CollatzResearch.WordTrace tailWord_3090437 prefixEnd_3090437 1586879613439030384724845 := by
  unfold tailWord_3090437
  simp only [CollatzResearch.WordTrace]
  refine ⟨112717497504882028464037565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75144998336588018976025043 112717497504882028464037565)
  ·
    refine ⟨42269061564330760674014087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112717497504882028464037565 42269061564330760674014087)
    ·
      refine ⟨63403592346496141011021131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42269061564330760674014087 63403592346496141011021131)
      ·
        refine ⟨95105388519744211516531697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63403592346496141011021131 95105388519744211516531697)
        ·
          refine ⟨71329041389808158637398773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95105388519744211516531697 71329041389808158637398773)
          ·
            refine ⟨6687097630294514872256135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71329041389808158637398773 6687097630294514872256135)
            ·
              refine ⟨10030646445441772308384203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6687097630294514872256135 10030646445441772308384203)
              ·
                refine ⟨15045969668162658462576305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10030646445441772308384203 15045969668162658462576305)
                ·
                  refine ⟨11284477251121993846932229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15045969668162658462576305 11284477251121993846932229)
                  ·
                    refine ⟨2115839484585373846299793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11284477251121993846932229 2115839484585373846299793)
                    ·
                      refine ⟨1586879613439030384724845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115839484585373846299793 1586879613439030384724845)
                      ·
                        rfl

theorem cell23_3090437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 4, 2].length) (baseStart_3090437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090437 prefixEnd_3090437 := by exact prefixLift 3090437
  have htrace : WordTrace (prefixWord ++ tailWord_3090437) baseStart_3090437 baseEnd_3090437 := by
    simpa [prefixWord, tailWord_3090437, baseEnd_3090437] using wordTrace_append hprefix tailTrace_3090437
  have hstable : (prefixWord ++ tailWord_3090437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090437).length < 2 ^ (prefixWord ++ tailWord_3090437).sum := by decide
  have hdescent : baseEnd_3090437 < baseStart_3090437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090440 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 1, 4, 3]
def baseStart_3090440 : Nat := 118140960795 + 3090440 * 2 ^ 59
def prefixEnd_3090440 : Nat := 4983230072969 + 3 ^ 40 * 3090440 * 2
def baseEnd_3090440 : Nat := 1586881153880993872987331

theorem tailTrace_3090440 : CollatzResearch.WordTrace tailWord_3090440 prefixEnd_3090440 1586881153880993872987331 := by
  unfold tailWord_3090440
  simp only [CollatzResearch.WordTrace]
  refine ⟨56358803461935579988198387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75145071282580773317597849 56358803461935579988198387)
  ·
    refine ⟨84538205192903369982297581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56358803461935579988198387 84538205192903369982297581)
    ·
      refine ⟨31701826947338763743361593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84538205192903369982297581 31701826947338763743361593)
      ·
        refine ⟨23776370210504072807521195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31701826947338763743361593 23776370210504072807521195)
        ·
          refine ⟨35664555315756109211281793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23776370210504072807521195 35664555315756109211281793)
          ·
            refine ⟨26748416486817081908461345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35664555315756109211281793 26748416486817081908461345)
            ·
              refine ⟨20061312365112811431346009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26748416486817081908461345 20061312365112811431346009)
              ·
                refine ⟨15045984273834608573509507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20061312365112811431346009 15045984273834608573509507)
                ·
                  refine ⟨22568976410751912860264261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15045984273834608573509507 22568976410751912860264261)
                  ·
                    refine ⟨4231683077015983661299549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22568976410751912860264261 4231683077015983661299549)
                    ·
                      refine ⟨1586881153880993872987331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4231683077015983661299549 1586881153880993872987331)
                      ·
                        rfl

theorem cell23_3090440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_3090440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090440 prefixEnd_3090440 := by exact prefixLift 3090440
  have htrace : WordTrace (prefixWord ++ tailWord_3090440) baseStart_3090440 baseEnd_3090440 := by
    simpa [prefixWord, tailWord_3090440, baseEnd_3090440] using wordTrace_append hprefix tailTrace_3090440
  have hstable : (prefixWord ++ tailWord_3090440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090440).length < 2 ^ (prefixWord ++ tailWord_3090440).sum := by decide
  have hdescent : baseEnd_3090440 < baseStart_3090440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090487 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 3, 1, 3]
def baseStart_3090487 : Nat := 118140960795 + 3090487 * 2 ^ 59
def prefixEnd_3090487 : Nat := 4983230072969 + 3 ^ 40 * 3090487 * 2
def baseEnd_3090487 : Nat := 1586905287471755189099615

theorem tailTrace_3090487 : CollatzResearch.WordTrace tailWord_3090487 prefixEnd_3090487 1586905287471755189099615 := by
  unfold tailWord_3090487
  simp only [CollatzResearch.WordTrace]
  refine ⟨112719321154700887003357715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75146214103133924668905143 112719321154700887003357715)
  ·
    refine ⟨169078981732051330505036573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112719321154700887003357715 169078981732051330505036573)
    ·
      refine ⟨63404618149519248939388715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169078981732051330505036573 63404618149519248939388715)
      ·
        refine ⟨95106927224278873409083073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63404618149519248939388715 95106927224278873409083073)
        ·
          refine ⟨71330195418209155056812305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95106927224278873409083073 71330195418209155056812305)
          ·
            refine ⟨53497646563656866292609229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71330195418209155056812305 53497646563656866292609229)
            ·
              refine ⟨20061617461371324859728461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53497646563656866292609229 20061617461371324859728461)
              ·
                refine ⟨7523106548014246822398173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20061617461371324859728461 7523106548014246822398173)
                ·
                  refine ⟨2821164955505342558399315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7523106548014246822398173 2821164955505342558399315)
                  ·
                    refine ⟨4231747433258013837598973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2821164955505342558399315 4231747433258013837598973)
                    ·
                      refine ⟨1586905287471755189099615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4231747433258013837598973 1586905287471755189099615)
                      ·
                        rfl

theorem cell23_3090487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_3090487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090487 prefixEnd_3090487 := by exact prefixLift 3090487
  have htrace : WordTrace (prefixWord ++ tailWord_3090487) baseStart_3090487 baseEnd_3090487 := by
    simpa [prefixWord, tailWord_3090487, baseEnd_3090487] using wordTrace_append hprefix tailTrace_3090487
  have hstable : (prefixWord ++ tailWord_3090487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090487).length < 2 ^ (prefixWord ++ tailWord_3090487).sum := by decide
  have hdescent : baseEnd_3090487 < baseStart_3090487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090537 : List Nat := [1, 2, 1, 1, 1, 5, 2, 4, 2, 4]
def baseStart_3090537 : Nat := 118140960795 + 3090537 * 2 ^ 59
def prefixEnd_3090537 : Nat := 4983230072969 + 3 ^ 40 * 3090537 * 2
def baseEnd_3090537 : Nat := 528976987168159997824795

theorem tailTrace_3090537 : CollatzResearch.WordTrace tailWord_3090537 prefixEnd_3090537 528976987168159997824795 := by
  unfold tailWord_3090537
  simp only [CollatzResearch.WordTrace]
  refine ⟨112721144804519745542677865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75147429869679830361785243 112721144804519745542677865)
  ·
    refine ⟨84540858603389809157008399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112721144804519745542677865 84540858603389809157008399)
    ·
      refine ⟨126811287905084713735512599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84540858603389809157008399 126811287905084713735512599)
      ·
        refine ⟨190216931857627070603268899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126811287905084713735512599 190216931857627070603268899)
        ·
          refine ⟨285325397786440605904903349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190216931857627070603268899 285325397786440605904903349)
          ·
            refine ⟨26749256042478806803584689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 285325397786440605904903349 26749256042478806803584689)
            ·
              refine ⟨20061942031859105102688517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26749256042478806803584689 20061942031859105102688517)
              ·
                refine ⟨3761614130973582206754097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20061942031859105102688517 3761614130973582206754097)
                ·
                  refine ⟨2821210598230186655065573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3761614130973582206754097 2821210598230186655065573)
                  ·
                    refine ⟨528976987168159997824795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2821210598230186655065573 528976987168159997824795)
                    ·
                      rfl

theorem cell23_3090537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 4].length) (baseStart_3090537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090537 prefixEnd_3090537 := by exact prefixLift 3090537
  have htrace : WordTrace (prefixWord ++ tailWord_3090537) baseStart_3090537 baseEnd_3090537 := by
    simpa [prefixWord, tailWord_3090537, baseEnd_3090537] using wordTrace_append hprefix tailTrace_3090537
  have hstable : (prefixWord ++ tailWord_3090537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090537).length < 2 ^ (prefixWord ++ tailWord_3090537).sum := by decide
  have hdescent : baseEnd_3090537 < baseStart_3090537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090538 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 3, 1, 3]
def baseStart_3090538 : Nat := 118140960795 + 3090538 * 2 ^ 59
def prefixEnd_3090538 : Nat := 4983230072969 + 3 ^ 40 * 3090538 * 2
def baseEnd_3090538 : Nat := 1586931474985134489561881

theorem tailTrace_3090538 : CollatzResearch.WordTrace tailWord_3090538 prefixEnd_3090538 1586931474985134489561881 := by
  unfold tailWord_3090538
  simp only [CollatzResearch.WordTrace]
  refine ⟨28180295319379030678366067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75147454185010748475642845 28180295319379030678366067)
  ·
    refine ⟨42270442979068546017549101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28180295319379030678366067 42270442979068546017549101)
    ·
      refine ⟨15851416117150704756580913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42270442979068546017549101 15851416117150704756580913)
      ·
        refine ⟨11888562087863028567435685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15851416117150704756580913 11888562087863028567435685)
        ·
          refine ⟨2229105391474317856394191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11888562087863028567435685 2229105391474317856394191)
          ·
            refine ⟨3343658087211476784591287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2229105391474317856394191 3343658087211476784591287)
            ·
              refine ⟨5015487130817215176886931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3343658087211476784591287 5015487130817215176886931)
              ·
                refine ⟨7523230696225822765330397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5015487130817215176886931 7523230696225822765330397)
                ·
                  refine ⟨2821211511084683536998899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7523230696225822765330397 2821211511084683536998899)
                  ·
                    refine ⟨4231817266627025305498349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2821211511084683536998899 4231817266627025305498349)
                    ·
                      refine ⟨1586931474985134489561881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4231817266627025305498349 1586931474985134489561881)
                      ·
                        rfl

theorem cell23_3090538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_3090538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090538 prefixEnd_3090538 := by exact prefixLift 3090538
  have htrace : WordTrace (prefixWord ++ tailWord_3090538) baseStart_3090538 baseEnd_3090538 := by
    simpa [prefixWord, tailWord_3090538, baseEnd_3090538] using wordTrace_append hprefix tailTrace_3090538
  have hstable : (prefixWord ++ tailWord_3090538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090538).length < 2 ^ (prefixWord ++ tailWord_3090538).sum := by decide
  have hdescent : baseEnd_3090538 < baseStart_3090538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090540 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 6]
def baseStart_3090540 : Nat := 118140960795 + 3090540 * 2 ^ 59
def prefixEnd_3090540 : Nat := 4983230072969 + 3 ^ 40 * 3090540 * 2
def baseEnd_3090540 : Nat := 1586932501946443481736871

theorem tailTrace_3090540 : CollatzResearch.WordTrace tailWord_3090540 prefixEnd_3090540 1586932501946443481736871 := by
  unfold tailWord_3090540
  simp only [CollatzResearch.WordTrace]
  refine ⟨56360627111754438527518537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75147502815672584703358049 56360627111754438527518537)
  ·
    refine ⟨42270470333815828895638903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56360627111754438527518537 42270470333815828895638903)
    ·
      refine ⟨63405705500723743343458355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42270470333815828895638903 63405705500723743343458355)
      ·
        refine ⟨95108558251085615015187533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63405705500723743343458355 95108558251085615015187533)
        ·
          refine ⟨35665709344157105630695325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95108558251085615015187533 35665709344157105630695325)
          ·
            refine ⟨13374641004058914611510747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35665709344157105630695325 13374641004058914611510747)
            ·
              refine ⟨20061961506088371917266121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13374641004058914611510747 20061961506088371917266121)
              ·
                refine ⟨15046471129566278937949591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20061961506088371917266121 15046471129566278937949591)
                ·
                  refine ⟨22569706694349418406924387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15046471129566278937949591 22569706694349418406924387)
                  ·
                    refine ⟨33854560041524127610386581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22569706694349418406924387 33854560041524127610386581)
                    ·
                      refine ⟨1586932501946443481736871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33854560041524127610386581 1586932501946443481736871)
                      ·
                        rfl

theorem cell23_3090540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_3090540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090540 prefixEnd_3090540 := by exact prefixLift 3090540
  have htrace : WordTrace (prefixWord ++ tailWord_3090540) baseStart_3090540 baseEnd_3090540 := by
    simpa [prefixWord, tailWord_3090540, baseEnd_3090540] using wordTrace_append hprefix tailTrace_3090540
  have hstable : (prefixWord ++ tailWord_3090540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090540).length < 2 ^ (prefixWord ++ tailWord_3090540).sum := by decide
  have hdescent : baseEnd_3090540 < baseStart_3090540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090561 : List Nat := [1, 2, 4, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_3090561 : Nat := 118140960795 + 3090561 * 2 ^ 59
def prefixEnd_3090561 : Nat := 4983230072969 + 3 ^ 40 * 3090561 * 2
def baseEnd_3090561 : Nat := 1586943285040187899574275

theorem tailTrace_3090561 : CollatzResearch.WordTrace tailWord_3090561 prefixEnd_3090561 1586943285040187899574275 := by
  unfold tailWord_3090561
  simp only [CollatzResearch.WordTrace]
  refine ⟨112722020156432797641551537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75148013437621865094367691 112722020156432797641551537)
  ·
    refine ⟨84541515117324598231163653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112722020156432797641551537 84541515117324598231163653)
    ·
      refine ⟨15851534084498362168343185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84541515117324598231163653 15851534084498362168343185)
      ·
        refine ⟨11888650563373771626257389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15851534084498362168343185 11888650563373771626257389)
        ·
          refine ⟨4458243961265164359846521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11888650563373771626257389 4458243961265164359846521)
          ·
            refine ⟨3343682970948873269884891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4458243961265164359846521 3343682970948873269884891)
            ·
              refine ⟨5015524456423309904827337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3343682970948873269884891 5015524456423309904827337)
              ·
                refine ⟨3761643342317482428620503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5015524456423309904827337 3761643342317482428620503)
                ·
                  refine ⟨5642465013476223642930755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3761643342317482428620503 5642465013476223642930755)
                  ·
                    refine ⟨8463697520214335464396133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5642465013476223642930755 8463697520214335464396133)
                    ·
                      refine ⟨1586943285040187899574275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8463697520214335464396133 1586943285040187899574275)
                      ·
                        rfl

theorem cell23_3090561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_3090561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090561 prefixEnd_3090561 := by exact prefixLift 3090561
  have htrace : WordTrace (prefixWord ++ tailWord_3090561) baseStart_3090561 baseEnd_3090561 := by
    simpa [prefixWord, tailWord_3090561, baseEnd_3090561] using wordTrace_append hprefix tailTrace_3090561
  have hstable : (prefixWord ++ tailWord_3090561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090561).length < 2 ^ (prefixWord ++ tailWord_3090561).sum := by decide
  have hdescent : baseEnd_3090561 < baseStart_3090561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090574 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4]
def baseStart_3090574 : Nat := 118140960795 + 3090574 * 2 ^ 59
def prefixEnd_3090574 : Nat := 4983230072969 + 3 ^ 40 * 3090574 * 2
def baseEnd_3090574 : Nat := 1586949960288696348711715

theorem tailTrace_3090574 : CollatzResearch.WordTrace tailWord_3090574 prefixEnd_3090574 1586949960288696348711715 := by
  unfold tailWord_3090574
  simp only [CollatzResearch.WordTrace]
  refine ⟨14090311788173212607721847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75148329536923800574516517 14090311788173212607721847)
  ·
    refine ⟨21135467682259818911582771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14090311788173212607721847 21135467682259818911582771)
    ·
      refine ⟨31703201523389728367374157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21135467682259818911582771 31703201523389728367374157)
      ·
        refine ⟨11888700571271148137765309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31703201523389728367374157 11888700571271148137765309)
        ·
          refine ⟨4458262714226680551661991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11888700571271148137765309 4458262714226680551661991)
          ·
            refine ⟨6687394071340020827492987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4458262714226680551661991 6687394071340020827492987)
            ·
              refine ⟨10031091107010031241239481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6687394071340020827492987 10031091107010031241239481)
              ·
                refine ⟨7523318330257523430929611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10031091107010031241239481 7523318330257523430929611)
                ·
                  refine ⟨11284977495386285146394417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7523318330257523430929611 11284977495386285146394417)
                  ·
                    refine ⟨8463733121539713859795813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11284977495386285146394417 8463733121539713859795813)
                    ·
                      refine ⟨1586949960288696348711715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8463733121539713859795813 1586949960288696348711715)
                      ·
                        rfl

theorem cell23_3090574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_3090574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090574 prefixEnd_3090574 := by exact prefixLift 3090574
  have htrace : WordTrace (prefixWord ++ tailWord_3090574) baseStart_3090574 baseEnd_3090574 := by
    simpa [prefixWord, tailWord_3090574, baseEnd_3090574] using wordTrace_append hprefix tailTrace_3090574
  have hstable : (prefixWord ++ tailWord_3090574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090574).length < 2 ^ (prefixWord ++ tailWord_3090574).sum := by decide
  have hdescent : baseEnd_3090574 < baseStart_3090574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090578 : List Nat := [3, 2, 3, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_3090578 : Nat := 118140960795 + 3090578 * 2 ^ 59
def prefixEnd_3090578 : Nat := 4983230072969 + 3 ^ 40 * 3090578 * 2
def baseEnd_3090578 : Nat := 1586952014211314333061697

theorem tailTrace_3090578 : CollatzResearch.WordTrace tailWord_3090578 prefixEnd_3090578 1586952014211314333061697 := by
  unfold tailWord_3090578
  simp only [CollatzResearch.WordTrace]
  refine ⟨28180660049342802386230097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75148426798247473029946925 28180660049342802386230097)
  ·
    refine ⟨21135495037007101789672573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28180660049342802386230097 21135495037007101789672573)
    ·
      refine ⟨7925810638877663171127215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21135495037007101789672573 7925810638877663171127215)
      ·
        refine ⟨11888715958316494756690823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7925810638877663171127215 11888715958316494756690823)
        ·
          refine ⟨17833073937474742135036235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11888715958316494756690823 17833073937474742135036235)
          ·
            refine ⟨26749610906212113202554353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17833073937474742135036235 26749610906212113202554353)
            ·
              refine ⟨20062208179659084901915765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26749610906212113202554353 20062208179659084901915765)
              ·
                refine ⟨1880832016843039209554603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20062208179659084901915765 1880832016843039209554603)
                ·
                  refine ⟨2821248025264558814331905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880832016843039209554603 2821248025264558814331905)
                  ·
                    refine ⟨2115936018948419110748929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2821248025264558814331905 2115936018948419110748929)
                    ·
                      refine ⟨1586952014211314333061697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115936018948419110748929 1586952014211314333061697)
                      ·
                        rfl

theorem cell23_3090578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_3090578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090578 prefixEnd_3090578 := by exact prefixLift 3090578
  have htrace : WordTrace (prefixWord ++ tailWord_3090578) baseStart_3090578 baseEnd_3090578 := by
    simpa [prefixWord, tailWord_3090578, baseEnd_3090578] using wordTrace_append hprefix tailTrace_3090578
  have hstable : (prefixWord ++ tailWord_3090578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090578).length < 2 ^ (prefixWord ++ tailWord_3090578).sum := by decide
  have hdescent : baseEnd_3090578 < baseStart_3090578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090612 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_3090612 : Nat := 118140960795 + 3090612 * 2 ^ 59
def prefixEnd_3090612 : Nat := 4983230072969 + 3 ^ 40 * 3090612 * 2
def baseEnd_3090612 : Nat := 1586969472553567200036541

theorem tailTrace_3090612 : CollatzResearch.WordTrace tailWord_3090612 prefixEnd_3090612 1586969472553567200036541 := by
  unfold tailWord_3090612
  simp only [CollatzResearch.WordTrace]
  refine ⟨56361940139624016675829045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75149253519498688901105393 56361940139624016675829045)
  ·
    refine ⟨5283931888089751563358973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56361940139624016675829045 5283931888089751563358973)
    ·
      refine ⟨1981474458033656836259615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5283931888089751563358973 1981474458033656836259615)
      ·
        refine ⟨2972211687050485254389423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1981474458033656836259615 2972211687050485254389423)
        ·
          refine ⟨4458317530575727881584135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2972211687050485254389423 4458317530575727881584135)
          ·
            refine ⟨6687476295863591822376203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4458317530575727881584135 6687476295863591822376203)
            ·
              refine ⟨10031214443795387733564305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6687476295863591822376203 10031214443795387733564305)
              ·
                refine ⟨7523410832846540800173229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10031214443795387733564305 7523410832846540800173229)
                ·
                  refine ⟨2821279062317452800064961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7523410832846540800173229 2821279062317452800064961)
                  ·
                    refine ⟨2115959296738089600048721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2821279062317452800064961 2115959296738089600048721)
                    ·
                      refine ⟨1586969472553567200036541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115959296738089600048721 1586969472553567200036541)
                      ·
                        rfl

theorem cell23_3090612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_3090612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090612 prefixEnd_3090612 := by exact prefixLift 3090612
  have htrace : WordTrace (prefixWord ++ tailWord_3090612) baseStart_3090612 baseEnd_3090612 := by
    simpa [prefixWord, tailWord_3090612, baseEnd_3090612] using wordTrace_append hprefix tailTrace_3090612
  have hstable : (prefixWord ++ tailWord_3090612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090612).length < 2 ^ (prefixWord ++ tailWord_3090612).sum := by decide
  have hdescent : baseEnd_3090612 < baseStart_3090612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090634 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 1, 4, 2]
def baseStart_3090634 : Nat := 118140960795 + 3090634 * 2 ^ 59
def prefixEnd_3090634 : Nat := 4983230072969 + 3 ^ 40 * 3090634 * 2
def baseEnd_3090634 : Nat := 1586980769127966113961439

theorem tailTrace_3090634 : CollatzResearch.WordTrace tailWord_3090634 prefixEnd_3090634 1586980769127966113961439 := by
  unfold tailWord_3090634
  simp only [CollatzResearch.WordTrace]
  refine ⟨28181170671292082777239739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75149788456778887405972637 28181170671292082777239739)
  ·
    refine ⟨42271756006938124165859609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28181170671292082777239739 42271756006938124165859609)
    ·
      refine ⟨31703817005203593124394707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42271756006938124165859609 31703817005203593124394707)
      ·
        refine ⟨47555725507805389686592061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31703817005203593124394707 47555725507805389686592061)
        ·
          refine ⟨17833397065427021132472023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47555725507805389686592061 17833397065427021132472023)
          ·
            refine ⟨26750095598140531698708035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17833397065427021132472023 26750095598140531698708035)
            ·
              refine ⟨40125143397210797548062053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26750095598140531698708035 40125143397210797548062053)
              ·
                refine ⟨7523464386977024540261635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40125143397210797548062053 7523464386977024540261635)
                ·
                  refine ⟨11285196580465536810392453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7523464386977024540261635 11285196580465536810392453)
                  ·
                    refine ⟨2115974358837288151948585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11285196580465536810392453 2115974358837288151948585)
                    ·
                      refine ⟨1586980769127966113961439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115974358837288151948585 1586980769127966113961439)
                      ·
                        rfl

theorem cell23_3090634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_3090634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090634 prefixEnd_3090634 := by exact prefixLift 3090634
  have htrace : WordTrace (prefixWord ++ tailWord_3090634) baseStart_3090634 baseEnd_3090634 := by
    simpa [prefixWord, tailWord_3090634, baseEnd_3090634] using wordTrace_append hprefix tailTrace_3090634
  have hstable : (prefixWord ++ tailWord_3090634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090634).length < 2 ^ (prefixWord ++ tailWord_3090634).sum := by decide
  have hdescent : baseEnd_3090634 < baseStart_3090634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090638 : List Nat := [4, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2]
def baseStart_3090638 : Nat := 118140960795 + 3090638 * 2 ^ 59
def prefixEnd_3090638 : Nat := 4983230072969 + 3 ^ 40 * 3090638 * 2
def baseEnd_3090638 : Nat := 1586982823050584098311421

theorem tailTrace_3090638 : CollatzResearch.WordTrace tailWord_3090638 prefixEnd_3090638 1586982823050584098311421 := by
  unfold tailWord_3090638
  simp only [CollatzResearch.WordTrace]
  refine ⟨14090603572144229974013071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75149885718102559861403045 14090603572144229974013071)
  ·
    refine ⟨21135905358216344961019607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14090603572144229974013071 21135905358216344961019607)
    ·
      refine ⟨31703858037324517441529411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21135905358216344961019607 31703858037324517441529411)
      ·
        refine ⟨47555787055986776162294117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31703858037324517441529411 47555787055986776162294117)
        ·
          refine ⟨8916710072997520530430147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47555787055986776162294117 8916710072997520530430147)
          ·
            refine ⟨13375065109496280795645221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8916710072997520530430147 13375065109496280795645221)
            ·
              refine ⟨2507824708030552649183479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13375065109496280795645221 2507824708030552649183479)
              ·
                refine ⟨3761737062045828973775219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507824708030552649183479 3761737062045828973775219)
                ·
                  refine ⟨5642605593068743460662829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3761737062045828973775219 5642605593068743460662829)
                  ·
                    refine ⟨2115977097400778797748561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5642605593068743460662829 2115977097400778797748561)
                    ·
                      refine ⟨1586982823050584098311421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115977097400778797748561 1586982823050584098311421)
                      ·
                        rfl

theorem cell23_3090638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_3090638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090638 prefixEnd_3090638 := by exact prefixLift 3090638
  have htrace : WordTrace (prefixWord ++ tailWord_3090638) baseStart_3090638 baseEnd_3090638 := by
    simpa [prefixWord, tailWord_3090638, baseEnd_3090638] using wordTrace_append hprefix tailTrace_3090638
  have hstable : (prefixWord ++ tailWord_3090638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090638).length < 2 ^ (prefixWord ++ tailWord_3090638).sum := by decide
  have hdescent : baseEnd_3090638 < baseStart_3090638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090645 : List Nat := [1, 3, 2, 4, 3, 1, 1, 2, 2, 1, 3]
def baseStart_3090645 : Nat := 118140960795 + 3090645 * 2 ^ 59
def prefixEnd_3090645 : Nat := 4983230072969 + 3 ^ 40 * 3090645 * 2
def baseEnd_3090645 : Nat := 1586986417415165570923889

theorem tailTrace_3090645 : CollatzResearch.WordTrace tailWord_3090645 prefixEnd_3090645 1586986417415165570923889 := by
  unfold tailWord_3090645
  simp only [CollatzResearch.WordTrace]
  refine ⟨112725083888128479987609389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75150055925418986658406259 112725083888128479987609389)
  ·
    refine ⟨42271906458048179995353521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112725083888128479987609389 42271906458048179995353521)
    ·
      refine ⟨31703929843536134996515141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42271906458048179995353521 31703929843536134996515141)
      ·
        refine ⟨5944486845663025311846589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31703929843536134996515141 5944486845663025311846589)
        ·
          refine ⟨2229182567123634491942471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5944486845663025311846589 2229182567123634491942471)
          ·
            refine ⟨3343773850685451737913707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2229182567123634491942471 3343773850685451737913707)
            ·
              refine ⟨5015660776028177606870561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3343773850685451737913707 5015660776028177606870561)
              ·
                refine ⟨3761745582021133205152921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5015660776028177606870561 3761745582021133205152921)
                ·
                  refine ⟨2821309186515849903864691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3761745582021133205152921 2821309186515849903864691)
                  ·
                    refine ⟨4231963779773774855797037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2821309186515849903864691 4231963779773774855797037)
                    ·
                      refine ⟨1586986417415165570923889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4231963779773774855797037 1586986417415165570923889)
                      ·
                        rfl

theorem cell23_3090645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_3090645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090645 prefixEnd_3090645 := by exact prefixLift 3090645
  have htrace : WordTrace (prefixWord ++ tailWord_3090645) baseStart_3090645 baseEnd_3090645 := by
    simpa [prefixWord, tailWord_3090645, baseEnd_3090645] using wordTrace_append hprefix tailTrace_3090645
  have hstable : (prefixWord ++ tailWord_3090645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090645).length < 2 ^ (prefixWord ++ tailWord_3090645).sum := by decide
  have hdescent : baseEnd_3090645 < baseStart_3090645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090657 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 7]
def baseStart_3090657 : Nat := 118140960795 + 3090657 * 2 ^ 59
def prefixEnd_3090657 : Nat := 4983230072969 + 3 ^ 40 * 3090657 * 2
def baseEnd_3090657 : Nat := 176332508798113280441537

theorem tailTrace_3090657 : CollatzResearch.WordTrace tailWord_3090657 prefixEnd_3090657 176332508798113280441537 := by
  unfold tailWord_3090657
  simp only [CollatzResearch.WordTrace]
  refine ⟨112725521564085006037046225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75150347709390004024697483 112725521564085006037046225)
  ·
    refine ⟨84544141173063754527784669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112725521564085006037046225 84544141173063754527784669)
    ·
      refine ⟨31704052939898907947919251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84544141173063754527784669 31704052939898907947919251)
      ·
        refine ⟨47556079409848361921878877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31704052939898907947919251 47556079409848361921878877)
        ·
          refine ⟨17833529778693135720704579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47556079409848361921878877 17833529778693135720704579)
          ·
            refine ⟨26750294668039703581056869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17833529778693135720704579 26750294668039703581056869)
            ·
              refine ⟨5015680250257444421448163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26750294668039703581056869 5015680250257444421448163)
              ·
                refine ⟨7523520375386166632172245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5015680250257444421448163 7523520375386166632172245)
                ·
                  refine ⟨176332508798113280441537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7523520375386166632172245 176332508798113280441537)
                  ·
                    rfl

theorem cell23_3090657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 7].length) (baseStart_3090657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090657 prefixEnd_3090657 := by exact prefixLift 3090657
  have htrace : WordTrace (prefixWord ++ tailWord_3090657) baseStart_3090657 baseEnd_3090657 := by
    simpa [prefixWord, tailWord_3090657, baseEnd_3090657] using wordTrace_append hprefix tailTrace_3090657
  have hstable : (prefixWord ++ tailWord_3090657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090657).length < 2 ^ (prefixWord ++ tailWord_3090657).sum := by decide
  have hdescent : baseEnd_3090657 < baseStart_3090657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090667 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 3]
def baseStart_3090667 : Nat := 118140960795 + 3090667 * 2 ^ 59
def prefixEnd_3090667 : Nat := 4983230072969 + 3 ^ 40 * 3090667 * 2
def baseEnd_3090667 : Nat := 1586997713989564484848787

theorem tailTrace_3090667 : CollatzResearch.WordTrace tailWord_3090667 prefixEnd_3090667 1586997713989564484848787 := by
  unfold tailWord_3090667
  simp only [CollatzResearch.WordTrace]
  refine ⟨112725886294048777744910255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75150590862699185163273503 112725886294048777744910255)
  ·
    refine ⟨169088829441073166617365383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112725886294048777744910255 169088829441073166617365383)
    ·
      refine ⟨253633244161609749926048075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169088829441073166617365383 253633244161609749926048075)
      ·
        refine ⟨380449866242414624889072113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253633244161609749926048075 380449866242414624889072113)
        ·
          refine ⟨285337399681810968666804085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380449866242414624889072113 285337399681810968666804085)
          ·
            refine ⟨26750381220169778312512883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 285337399681810968666804085 26750381220169778312512883)
            ·
              refine ⟨40125571830254667468769325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26750381220169778312512883 40125571830254667468769325)
              ·
                refine ⟨15047089436345500300788497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40125571830254667468769325 15047089436345500300788497)
                ·
                  refine ⟨11285317077259125225591373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15047089436345500300788497 11285317077259125225591373)
                  ·
                    refine ⟨4231993903972171959596765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11285317077259125225591373 4231993903972171959596765)
                    ·
                      refine ⟨1586997713989564484848787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4231993903972171959596765 1586997713989564484848787)
                      ·
                        rfl

theorem cell23_3090667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 3].length) (baseStart_3090667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090667 prefixEnd_3090667 := by exact prefixLift 3090667
  have htrace : WordTrace (prefixWord ++ tailWord_3090667) baseStart_3090667 baseEnd_3090667 := by
    simpa [prefixWord, tailWord_3090667, baseEnd_3090667] using wordTrace_append hprefix tailTrace_3090667
  have hstable : (prefixWord ++ tailWord_3090667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090667).length < 2 ^ (prefixWord ++ tailWord_3090667).sum := by decide
  have hdescent : baseEnd_3090667 < baseStart_3090667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090668 : List Nat := [2, 2, 1, 1, 2, 3, 5, 1, 2, 2, 2]
def baseStart_3090668 : Nat := 118140960795 + 3090668 * 2 ^ 59
def prefixEnd_3090668 : Nat := 4983230072969 + 3 ^ 40 * 3090668 * 2
def baseEnd_3090668 : Nat := 1586998227470218980936283

theorem tailTrace_3090668 : CollatzResearch.WordTrace tailWord_3090668 prefixEnd_3090668 1586998227470218980936283 := by
  unfold tailWord_3090668
  simp only [CollatzResearch.WordTrace]
  refine ⟨56362961383522577457848329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75150615178030103277131105 56362961383522577457848329)
  ·
    refine ⟨42272221037641933093386247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56362961383522577457848329 42272221037641933093386247)
    ·
      refine ⟨63408331556462899640079371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42272221037641933093386247 63408331556462899640079371)
      ·
        refine ⟨95112497334694349460119057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63408331556462899640079371 95112497334694349460119057)
        ·
          refine ⟨71334373001020762095089293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95112497334694349460119057 71334373001020762095089293)
          ·
            refine ⟨26750389875382785785658485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71334373001020762095089293 26750389875382785785658485)
            ·
              refine ⟨2507849050817136167405483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26750389875382785785658485 2507849050817136167405483)
              ·
                refine ⟨3761773576225704251108225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507849050817136167405483 3761773576225704251108225)
                ·
                  refine ⟨2821330182169278188331169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3761773576225704251108225 2821330182169278188331169)
                  ·
                    refine ⟨2115997636626958641248377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2821330182169278188331169 2115997636626958641248377)
                    ·
                      refine ⟨1586998227470218980936283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2115997636626958641248377 1586998227470218980936283)
                      ·
                        rfl

theorem cell23_3090668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 2, 2].length) (baseStart_3090668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090668 prefixEnd_3090668 := by exact prefixLift 3090668
  have htrace : WordTrace (prefixWord ++ tailWord_3090668) baseStart_3090668 baseEnd_3090668 := by
    simpa [prefixWord, tailWord_3090668, baseEnd_3090668] using wordTrace_append hprefix tailTrace_3090668
  have hstable : (prefixWord ++ tailWord_3090668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090668).length < 2 ^ (prefixWord ++ tailWord_3090668).sum := by decide
  have hdescent : baseEnd_3090668 < baseStart_3090668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090687 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 2, 5]
def baseStart_3090687 : Nat := 118140960795 + 3090687 * 2 ^ 59
def prefixEnd_3090687 : Nat := 4983230072969 + 3 ^ 40 * 3090687 * 2
def baseEnd_3090687 : Nat := 529002661200884802199565

theorem tailTrace_3090687 : CollatzResearch.WordTrace tailWord_3090687 prefixEnd_3090687 529002661200884802199565 := by
  unfold tailWord_3090687
  simp only [CollatzResearch.WordTrace]
  refine ⟨112726615753976321160638315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75151077169317547440425543 112726615753976321160638315)
  ·
    refine ⟨169089923630964481740957473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112726615753976321160638315 169089923630964481740957473)
    ·
      refine ⟨126817442723223361305718105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169089923630964481740957473 126817442723223361305718105)
      ·
        refine ⟨95113082042417520979288579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126817442723223361305718105 95113082042417520979288579)
        ·
          refine ⟨142669623063626281468932869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95113082042417520979288579 142669623063626281468932869)
          ·
            refine ⟨26750554324429927775424913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142669623063626281468932869 26750554324429927775424913)
            ·
              refine ⟨20062915743322445831568685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26750554324429927775424913 20062915743322445831568685)
              ·
                refine ⟨7523593403745917186838257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20062915743322445831568685 7523593403745917186838257)
                ·
                  refine ⟨5642695052809437890128693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7523593403745917186838257 5642695052809437890128693)
                  ·
                    refine ⟨529002661200884802199565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5642695052809437890128693 529002661200884802199565)
                    ·
                      rfl

theorem cell23_3090687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 5].length) (baseStart_3090687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090687 prefixEnd_3090687 := by exact prefixLift 3090687
  have htrace : WordTrace (prefixWord ++ tailWord_3090687) baseStart_3090687 baseEnd_3090687 := by
    simpa [prefixWord, tailWord_3090687, baseEnd_3090687] using wordTrace_append hprefix tailTrace_3090687
  have hstable : (prefixWord ++ tailWord_3090687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090687).length < 2 ^ (prefixWord ++ tailWord_3090687).sum := by decide
  have hdescent : baseEnd_3090687 < baseStart_3090687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090714 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5]
def baseStart_3090714 : Nat := 118140960795 + 3090714 * 2 ^ 59
def prefixEnd_3090714 : Nat := 4983230072969 + 3 ^ 40 * 3090714 * 2
def baseEnd_3090714 : Nat := 1587021847580325800961071

theorem tailTrace_3090714 : CollatzResearch.WordTrace tailWord_3090714 prefixEnd_3090714 1587021847580325800961071 := by
  unfold tailWord_3090714
  simp only [CollatzResearch.WordTrace]
  refine ⟨28181900131219626192967799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75151733683252336514580797 28181900131219626192967799)
  ·
    refine ⟨42272850196829439289451699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28181900131219626192967799 42272850196829439289451699)
    ·
      refine ⟨63409275295244158934177549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42272850196829439289451699 63409275295244158934177549)
      ·
        refine ⟨23778478235716559600316581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63409275295244158934177549 23778478235716559600316581)
        ·
          refine ⟨4458464669196854925059359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23778478235716559600316581 4458464669196854925059359)
          ·
            refine ⟨6687697003795282387589039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4458464669196854925059359 6687697003795282387589039)
            ·
              refine ⟨10031545505692923581383559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6687697003795282387589039 10031545505692923581383559)
              ·
                refine ⟨15047318258539385372075339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10031545505692923581383559 15047318258539385372075339)
                ·
                  refine ⟨22570977387809078058113009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15047318258539385372075339 22570977387809078058113009)
                  ·
                    refine ⟨16928233040856808543584757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22570977387809078058113009 16928233040856808543584757)
                    ·
                      refine ⟨1587021847580325800961071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16928233040856808543584757 1587021847580325800961071)
                      ·
                        rfl

theorem cell23_3090714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_3090714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090714 prefixEnd_3090714 := by exact prefixLift 3090714
  have htrace : WordTrace (prefixWord ++ tailWord_3090714) baseStart_3090714 baseEnd_3090714 := by
    simpa [prefixWord, tailWord_3090714, baseEnd_3090714] using wordTrace_append hprefix tailTrace_3090714
  have hstable : (prefixWord ++ tailWord_3090714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090714).length < 2 ^ (prefixWord ++ tailWord_3090714).sum := by decide
  have hdescent : baseEnd_3090714 < baseStart_3090714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090744 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 2, 2, 3]
def baseStart_3090744 : Nat := 118140960795 + 3090744 * 2 ^ 59
def prefixEnd_3090744 : Nat := 4983230072969 + 3 ^ 40 * 3090744 * 2
def baseEnd_3090744 : Nat := 1587037251999960683585933

theorem tailTrace_3090744 : CollatzResearch.WordTrace tailWord_3090744 prefixEnd_3090744 1587037251999960683585933 := by
  unfold tailWord_3090744
  simp only [CollatzResearch.WordTrace]
  refine ⟨56364347357384909947731643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75152463143179879930308857 56364347357384909947731643)
  ·
    refine ⟨84546521036077364921597465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56364347357384909947731643 84546521036077364921597465)
    ·
      refine ⟨63409890777058023691198099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84546521036077364921597465 63409890777058023691198099)
      ·
        refine ⟨95114836165587035536797149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63409890777058023691198099 95114836165587035536797149)
        ·
          refine ⟨35668063562095138326298931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95114836165587035536797149 35668063562095138326298931)
          ·
            refine ⟨53502095343142707489448397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35668063562095138326298931 53502095343142707489448397)
            ·
              refine ⟨20063285753678515308543149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53502095343142707489448397 20063285753678515308543149)
              ·
                refine ⟨7523732157629443240703681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20063285753678515308543149 7523732157629443240703681)
                ·
                  refine ⟨5642799118222082430527761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7523732157629443240703681 5642799118222082430527761)
                  ·
                    refine ⟨4232099338666561822895821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5642799118222082430527761 4232099338666561822895821)
                    ·
                      refine ⟨1587037251999960683585933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4232099338666561822895821 1587037251999960683585933)
                      ·
                        rfl

theorem cell23_3090744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_3090744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090744 prefixEnd_3090744 := by exact prefixLift 3090744
  have htrace : WordTrace (prefixWord ++ tailWord_3090744) baseStart_3090744 baseEnd_3090744 := by
    simpa [prefixWord, tailWord_3090744, baseEnd_3090744] using wordTrace_append hprefix tailTrace_3090744
  have hstable : (prefixWord ++ tailWord_3090744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090744).length < 2 ^ (prefixWord ++ tailWord_3090744).sum := by decide
  have hdescent : baseEnd_3090744 < baseStart_3090744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090751 : List Nat := [1, 1, 2, 2, 4, 1, 2, 5, 1, 4]
def baseStart_3090751 : Nat := 118140960795 + 3090751 * 2 ^ 59
def prefixEnd_3090751 : Nat := 4983230072969 + 3 ^ 40 * 3090751 * 2
def baseEnd_3090751 : Nat := 529013615454847385399467

theorem tailTrace_3090751 : CollatzResearch.WordTrace tailWord_3090751 prefixEnd_3090751 529013615454847385399467 := by
  unfold tailWord_3090751
  simp only [CollatzResearch.WordTrace]
  refine ⟨112728950025744460090968107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75152633350496306727312071 112728950025744460090968107)
  ·
    refine ⟨169093425038616690136452161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112728950025744460090968107 169093425038616690136452161)
    ·
      refine ⟨126820068778962517602339121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169093425038616690136452161 126820068778962517602339121)
      ·
        refine ⟨95115051584221888201754341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126820068778962517602339121 95115051584221888201754341)
        ·
          refine ⟨17834072172041604037828939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95115051584221888201754341 17834072172041604037828939)
          ·
            refine ⟨26751108258062406056743409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17834072172041604037828939 26751108258062406056743409)
            ·
              refine ⟨20063331193546804542557557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26751108258062406056743409 20063331193546804542557557)
              ·
                refine ⟨1880937299395012925864771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20063331193546804542557557 1880937299395012925864771)
                ·
                  refine ⟨2821405949092519388797157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880937299395012925864771 2821405949092519388797157)
                  ·
                    refine ⟨529013615454847385399467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2821405949092519388797157 529013615454847385399467)
                    ·
                      rfl

theorem cell23_3090751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 1, 4].length) (baseStart_3090751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090751 prefixEnd_3090751 := by exact prefixLift 3090751
  have htrace : WordTrace (prefixWord ++ tailWord_3090751) baseStart_3090751 baseEnd_3090751 := by
    simpa [prefixWord, tailWord_3090751, baseEnd_3090751] using wordTrace_append hprefix tailTrace_3090751
  have hstable : (prefixWord ++ tailWord_3090751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090751).length < 2 ^ (prefixWord ++ tailWord_3090751).sum := by decide
  have hdescent : baseEnd_3090751 < baseStart_3090751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090764 : List Nat := [2, 2, 1, 3, 2, 1, 4, 2, 6]
def baseStart_3090764 : Nat := 118140960795 + 3090764 * 2 ^ 59
def prefixEnd_3090764 : Nat := 4983230072969 + 3 ^ 40 * 3090764 * 2
def baseEnd_3090764 : Nat := 176338613512561178370649

theorem tailTrace_3090764 : CollatzResearch.WordTrace tailWord_3090764 prefixEnd_3090764 176338613512561178370649 := by
  unfold tailWord_3090764
  simp only [CollatzResearch.WordTrace]
  refine ⟨56364712087348681655595673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75152949449798242207460897 56364712087348681655595673)
  ·
    refine ⟨42273534065511511241696755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56364712087348681655595673 42273534065511511241696755)
    ·
      refine ⟨63410301098267266862545133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42273534065511511241696755 63410301098267266862545133)
      ·
        refine ⟨23778862911850225073454425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63410301098267266862545133 23778862911850225073454425)
        ·
          refine ⟨17834147183887668805090819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23778862911850225073454425 17834147183887668805090819)
          ·
            refine ⟨26751220775831503207636229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17834147183887668805090819 26751220775831503207636229)
            ·
              refine ⟨5015853895468406851431793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26751220775831503207636229 5015853895468406851431793)
              ·
                refine ⟨3761890421601305138573845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5015853895468406851431793 3761890421601305138573845)
                ·
                  refine ⟨176338613512561178370649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3761890421601305138573845 176338613512561178370649)
                  ·
                    rfl

theorem cell23_3090764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 6].length) (baseStart_3090764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090764 prefixEnd_3090764 := by exact prefixLift 3090764
  have htrace : WordTrace (prefixWord ++ tailWord_3090764) baseStart_3090764 baseEnd_3090764 := by
    simpa [prefixWord, tailWord_3090764, baseEnd_3090764] using wordTrace_append hprefix tailTrace_3090764
  have hstable : (prefixWord ++ tailWord_3090764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090764).length < 2 ^ (prefixWord ++ tailWord_3090764).sum := by decide
  have hdescent : baseEnd_3090764 < baseStart_3090764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090768 : List Nat := [2, 1, 1, 1, 1, 6, 4, 2, 1, 4]
def baseStart_3090768 : Nat := 118140960795 + 3090768 * 2 ^ 59
def prefixEnd_3090768 : Nat := 4983230072969 + 3 ^ 40 * 3090768 * 2
def baseEnd_3090768 : Nat := 529016525178556196561941

theorem tailTrace_3090768 : CollatzResearch.WordTrace tailWord_3090768 prefixEnd_3090768 529016525178556196561941 := by
  unfold tailWord_3090768
  simp only [CollatzResearch.WordTrace]
  refine ⟨56364785033341435997168479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75153046711121914662891305 56364785033341435997168479)
  ·
    refine ⟨84547177550012153995752719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56364785033341435997168479 84547177550012153995752719)
    ·
      refine ⟨126820766325018230993629079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84547177550012153995752719 126820766325018230993629079)
      ·
        refine ⟨190231149487527346490443619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126820766325018230993629079 190231149487527346490443619)
        ·
          refine ⟨285346724231291019735665429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190231149487527346490443619 285346724231291019735665429)
          ·
            refine ⟨13375627698341766550109317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 285346724231291019735665429 13375627698341766550109317)
            ·
              refine ⟨2507930193439081228145497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13375627698341766550109317 2507930193439081228145497)
              ·
                refine ⟨1880947645079310921109123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2507930193439081228145497 1880947645079310921109123)
                ·
                  refine ⟨2821421467618966381663685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880947645079310921109123 2821421467618966381663685)
                  ·
                    refine ⟨529016525178556196561941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2821421467618966381663685 529016525178556196561941)
                    ·
                      rfl

theorem cell23_3090768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 1, 4].length) (baseStart_3090768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090768 prefixEnd_3090768 := by exact prefixLift 3090768
  have htrace : WordTrace (prefixWord ++ tailWord_3090768) baseStart_3090768 baseEnd_3090768 := by
    simpa [prefixWord, tailWord_3090768, baseEnd_3090768] using wordTrace_append hprefix tailTrace_3090768
  have hstable : (prefixWord ++ tailWord_3090768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090768).length < 2 ^ (prefixWord ++ tailWord_3090768).sum := by decide
  have hdescent : baseEnd_3090768 < baseStart_3090768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090787 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 7]
def baseStart_3090787 : Nat := 118140960795 + 3090787 * 2 ^ 59
def prefixEnd_3090787 : Nat := 4983230072969 + 3 ^ 40 * 3090787 * 2
def baseEnd_3090787 : Nat := 1587059331668104015348235

theorem tailTrace_3090787 : CollatzResearch.WordTrace tailWord_3090787 prefixEnd_3090787 1587059331668104015348235 := by
  unfold tailWord_3090787
  simp only [CollatzResearch.WordTrace]
  refine ⟨112730263053614038239278615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75153508702409358826185743 112730263053614038239278615)
  ·
    refine ⟨169095394580421057358917923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112730263053614038239278615 169095394580421057358917923)
    ·
      refine ⟨253643091870631586038376885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169095394580421057358917923 253643091870631586038376885)
      ·
        refine ⟨23779039862871711191097833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253643091870631586038376885 23779039862871711191097833)
        ·
          refine ⟨17834279897153783393323375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23779039862871711191097833 17834279897153783393323375)
          ·
            refine ⟨26751419845730675089985063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17834279897153783393323375 26751419845730675089985063)
            ·
              refine ⟨40127129768596012634977595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26751419845730675089985063 40127129768596012634977595)
              ·
                refine ⟨60190694652894018952466393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40127129768596012634977595 60190694652894018952466393)
                ·
                  refine ⟨45143020989670514214349795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60190694652894018952466393 45143020989670514214349795)
                  ·
                    refine ⟨67714531484505771321524693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45143020989670514214349795 67714531484505771321524693)
                    ·
                      refine ⟨1587059331668104015348235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67714531484505771321524693 1587059331668104015348235)
                      ·
                        rfl

theorem cell23_3090787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_3090787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090787 prefixEnd_3090787 := by exact prefixLift 3090787
  have htrace : WordTrace (prefixWord ++ tailWord_3090787) baseStart_3090787 baseEnd_3090787 := by
    simpa [prefixWord, tailWord_3090787, baseEnd_3090787] using wordTrace_append hprefix tailTrace_3090787
  have hstable : (prefixWord ++ tailWord_3090787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090787).length < 2 ^ (prefixWord ++ tailWord_3090787).sum := by decide
  have hdescent : baseEnd_3090787 < baseStart_3090787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090791 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_3090791 : Nat := 118140960795 + 3090791 * 2 ^ 59
def prefixEnd_3090791 : Nat := 4983230072969 + 3 ^ 40 * 3090791 * 2
def baseEnd_3090791 : Nat := 1587061385590721999698217

theorem tailTrace_3090791 : CollatzResearch.WordTrace tailWord_3090791 prefixEnd_3090791 1587061385590721999698217 := by
  unfold tailWord_3090791
  simp only [CollatzResearch.WordTrace]
  refine ⟨112730408945599546922424227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75153605963733031281616151 112730408945599546922424227)
  ·
    refine ⟨169095613418399320383636341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112730408945599546922424227 169095613418399320383636341)
    ·
      refine ⟨15852713757974936285965907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169095613418399320383636341 15852713757974936285965907)
      ·
        refine ⟨23779070636962404428948861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15852713757974936285965907 23779070636962404428948861)
        ·
          refine ⟨8917151488860901660855823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23779070636962404428948861 8917151488860901660855823)
          ·
            refine ⟨13375727233291352491283735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8917151488860901660855823 13375727233291352491283735)
            ·
              refine ⟨20063590849937028736925603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13375727233291352491283735 20063590849937028736925603)
              ·
                refine ⟨30095386274905543105388405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20063590849937028736925603 30095386274905543105388405)
                ·
                  refine ⟨2821442463272394666130163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30095386274905543105388405 2821442463272394666130163)
                  ·
                    refine ⟨4232163694908591999195245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2821442463272394666130163 4232163694908591999195245)
                    ·
                      refine ⟨1587061385590721999698217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4232163694908591999195245 1587061385590721999698217)
                      ·
                        rfl

theorem cell23_3090791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_3090791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090791 prefixEnd_3090791 := by exact prefixLift 3090791
  have htrace : WordTrace (prefixWord ++ tailWord_3090791) baseStart_3090791 baseEnd_3090791 := by
    simpa [prefixWord, tailWord_3090791, baseEnd_3090791] using wordTrace_append hprefix tailTrace_3090791
  have hstable : (prefixWord ++ tailWord_3090791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090791).length < 2 ^ (prefixWord ++ tailWord_3090791).sum := by decide
  have hdescent : baseEnd_3090791 < baseStart_3090791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090807 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 3, 6]
def baseStart_3090807 : Nat := 118140960795 + 3090807 * 2 ^ 59
def prefixEnd_3090807 : Nat := 4983230072969 + 3 ^ 40 * 3090807 * 2
def baseEnd_3090807 : Nat := 529023200427064645699381

theorem tailTrace_3090807 : CollatzResearch.WordTrace tailWord_3090807 prefixEnd_3090807 529023200427064645699381 := by
  unfold tailWord_3090807
  simp only [CollatzResearch.WordTrace]
  refine ⟨112730992513541581655006675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75153995009027721103337783 112730992513541581655006675)
  ·
    refine ⟨169096488770312372482510013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112730992513541581655006675 169096488770312372482510013)
    ·
      refine ⟨63411183288867139680941255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169096488770312372482510013 63411183288867139680941255)
      ·
        refine ⟨95116774933300709521411883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63411183288867139680941255 95116774933300709521411883)
        ·
          refine ⟨142675162399951064282117825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95116774933300709521411883 142675162399951064282117825)
          ·
            refine ⟨107006371799963298211588369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142675162399951064282117825 107006371799963298211588369)
            ·
              refine ⟨80254778849972473658691277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107006371799963298211588369 80254778849972473658691277)
              ·
                refine ⟨30095542068739677622009229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80254778849972473658691277 30095542068739677622009229)
                ·
                  refine ⟨11285828275777379108253461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30095542068739677622009229 11285828275777379108253461)
                  ·
                    refine ⟨529023200427064645699381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11285828275777379108253461 529023200427064645699381)
                    ·
                      rfl

theorem cell23_3090807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_3090807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090807 prefixEnd_3090807 := by exact prefixLift 3090807
  have htrace : WordTrace (prefixWord ++ tailWord_3090807) baseStart_3090807 baseEnd_3090807 := by
    simpa [prefixWord, tailWord_3090807, baseEnd_3090807] using wordTrace_append hprefix tailTrace_3090807
  have hstable : (prefixWord ++ tailWord_3090807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090807).length < 2 ^ (prefixWord ++ tailWord_3090807).sum := by decide
  have hdescent : baseEnd_3090807 < baseStart_3090807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090811 : List Nat := [1, 1, 1, 1, 1, 7, 4, 1, 1, 5]
def baseStart_3090811 : Nat := 118140960795 + 3090811 * 2 ^ 59
def prefixEnd_3090811 : Nat := 4983230072969 + 3 ^ 40 * 3090811 * 2
def baseEnd_3090811 : Nat := 529023885067937307149375

theorem tailTrace_3090811 : CollatzResearch.WordTrace tailWord_3090811 prefixEnd_3090811 529023885067937307149375 := by
  unfold tailWord_3090811
  simp only [CollatzResearch.WordTrace]
  refine ⟨112731138405527090338152287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75154092270351393558768191 112731138405527090338152287)
  ·
    refine ⟨169096707608290635507228431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112731138405527090338152287 169096707608290635507228431)
    ·
      refine ⟨253645061412435953260842647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169096707608290635507228431 253645061412435953260842647)
      ·
        refine ⟨380467592118653929891263971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253645061412435953260842647 380467592118653929891263971)
        ·
          refine ⟨570701388177980894836895957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380467592118653929891263971 570701388177980894836895957)
          ·
            refine ⟨13375813785421427222739749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 570701388177980894836895957 13375813785421427222739749)
            ·
              refine ⟨2507965084766517604263703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13375813785421427222739749 2507965084766517604263703)
              ·
                refine ⟨3761947627149776406395555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507965084766517604263703 3761947627149776406395555)
                ·
                  refine ⟨5642921440724664609593333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3761947627149776406395555 5642921440724664609593333)
                  ·
                    refine ⟨529023885067937307149375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5642921440724664609593333 529023885067937307149375)
                    ·
                      rfl

theorem cell23_3090811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 1, 5].length) (baseStart_3090811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090811 prefixEnd_3090811 := by exact prefixLift 3090811
  have htrace : WordTrace (prefixWord ++ tailWord_3090811) baseStart_3090811 baseEnd_3090811 := by
    simpa [prefixWord, tailWord_3090811, baseEnd_3090811] using wordTrace_append hprefix tailTrace_3090811
  have hstable : (prefixWord ++ tailWord_3090811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090811).length < 2 ^ (prefixWord ++ tailWord_3090811).sum := by decide
  have hdescent : baseEnd_3090811 < baseStart_3090811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090837 : List Nat := [1, 3, 2, 1, 1, 2, 1, 12]
def baseStart_3090837 : Nat := 118140960795 + 3090837 * 2 ^ 59
def prefixEnd_3090837 : Nat := 4983230072969 + 3 ^ 40 * 3090837 * 2
def baseEnd_3090837 : Nat := 58780926137067734063815

theorem tailTrace_3090837 : CollatzResearch.WordTrace tailWord_3090837 prefixEnd_3090837 58780926137067734063815 := by
  unfold tailWord_3090837
  simp only [CollatzResearch.WordTrace]
  refine ⟨112732086703432896778598765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75154724468955264519065843 112732086703432896778598765)
  ·
    refine ⟨42274532513787336291974537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112732086703432896778598765 42274532513787336291974537)
    ·
      refine ⟨31705899385340502218980903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42274532513787336291974537 31705899385340502218980903)
      ·
        refine ⟨47558849078010753328471355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31705899385340502218980903 47558849078010753328471355)
        ·
          refine ⟨71338273617016129992707033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47558849078010753328471355 71338273617016129992707033)
          ·
            refine ⟨53503705212762097494530275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71338273617016129992707033 53503705212762097494530275)
            ·
              refine ⟨80255557819143146241795413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53503705212762097494530275 80255557819143146241795413)
              ·
                refine ⟨58780926137067734063815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 80255557819143146241795413 58780926137067734063815)
                ·
                  rfl

theorem cell23_3090837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 12].length) (baseStart_3090837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090837 prefixEnd_3090837 := by exact prefixLift 3090837
  have htrace : WordTrace (prefixWord ++ tailWord_3090837) baseStart_3090837 baseEnd_3090837 := by
    simpa [prefixWord, tailWord_3090837, baseEnd_3090837] using wordTrace_append hprefix tailTrace_3090837
  have hstable : (prefixWord ++ tailWord_3090837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090837).length < 2 ^ (prefixWord ++ tailWord_3090837).sum := by decide
  have hdescent : baseEnd_3090837 < baseStart_3090837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090848 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 3, 2, 2]
def baseStart_3090848 : Nat := 118140960795 + 3090848 * 2 ^ 59
def prefixEnd_3090848 : Nat := 4983230072969 + 3 ^ 40 * 3090848 * 2
def baseEnd_3090848 : Nat := 1587090653988028276685455

theorem tailTrace_3090848 : CollatzResearch.WordTrace tailWord_3090848 prefixEnd_3090848 1587090653988028276685455 := by
  unfold tailWord_3090848
  simp only [CollatzResearch.WordTrace]
  refine ⟨56366243953196522828624599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75154991937595363771499465 56366243953196522828624599)
  ·
    refine ⟨84549365929794784242936899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56366243953196522828624599 84549365929794784242936899)
    ·
      refine ⟨126824048894692176364405349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84549365929794784242936899 126824048894692176364405349)
      ·
        refine ⟨23779509167754783068326003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126824048894692176364405349 23779509167754783068326003)
        ·
          refine ⟨35669263751632174602489005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23779509167754783068326003 35669263751632174602489005)
          ·
            refine ⟨13375973906862065475933377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35669263751632174602489005 13375973906862065475933377)
            ·
              refine ⟨10031980430146549106950033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13375973906862065475933377 10031980430146549106950033)
              ·
                refine ⟨7523985322609911830212525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10031980430146549106950033 7523985322609911830212525)
                ·
                  refine ⟨2821494495978716936329697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7523985322609911830212525 2821494495978716936329697)
                  ·
                    refine ⟨2116120871984037702247273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2821494495978716936329697 2116120871984037702247273)
                    ·
                      refine ⟨1587090653988028276685455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2116120871984037702247273 1587090653988028276685455)
                      ·
                        rfl

theorem cell23_3090848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_3090848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090848 prefixEnd_3090848 := by exact prefixLift 3090848
  have htrace : WordTrace (prefixWord ++ tailWord_3090848) baseStart_3090848 baseEnd_3090848 := by
    simpa [prefixWord, tailWord_3090848, baseEnd_3090848] using wordTrace_append hprefix tailTrace_3090848
  have hstable : (prefixWord ++ tailWord_3090848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090848).length < 2 ^ (prefixWord ++ tailWord_3090848).sum := by decide
  have hdescent : baseEnd_3090848 < baseStart_3090848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090851 : List Nat := [1, 1, 1, 4, 1, 4, 1, 4, 1, 2, 3]
def baseStart_3090851 : Nat := 118140960795 + 3090851 * 2 ^ 59
def prefixEnd_3090851 : Nat := 4983230072969 + 3 ^ 40 * 3090851 * 2
def baseEnd_3090851 : Nat := 1587092194429991764947941

theorem tailTrace_3090851 : CollatzResearch.WordTrace tailWord_3090851 prefixEnd_3090851 1587092194429991764947941 := by
  unfold tailWord_3090851
  simp only [CollatzResearch.WordTrace]
  refine ⟨112732597325382177169608407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75155064883588118113072271 112732597325382177169608407)
  ·
    refine ⟨169098895988073265754412611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112732597325382177169608407 169098895988073265754412611)
    ·
      refine ⟨253648343982109898631618917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169098895988073265754412611 253648343982109898631618917)
      ·
        refine ⟨47559064496645605993428547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253648343982109898631618917 47559064496645605993428547)
        ·
          refine ⟨71338596744968408990142821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47559064496645605993428547 71338596744968408990142821)
          ·
            refine ⟨13375986889681576685651779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71338596744968408990142821 13375986889681576685651779)
            ·
              refine ⟨20063980334522365028477669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13375986889681576685651779 20063980334522365028477669)
              ·
                refine ⟨3761996312722943442839563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20063980334522365028477669 3761996312722943442839563)
                ·
                  refine ⟨5642994469084415164259345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3761996312722943442839563 5642994469084415164259345)
                  ·
                    refine ⟨4232245851813311373194509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5642994469084415164259345 4232245851813311373194509)
                    ·
                      refine ⟨1587092194429991764947941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4232245851813311373194509 1587092194429991764947941)
                      ·
                        rfl

theorem cell23_3090851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_3090851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090851 prefixEnd_3090851 := by exact prefixLift 3090851
  have htrace : WordTrace (prefixWord ++ tailWord_3090851) baseStart_3090851 baseEnd_3090851 := by
    simpa [prefixWord, tailWord_3090851, baseEnd_3090851] using wordTrace_append hprefix tailTrace_3090851
  have hstable : (prefixWord ++ tailWord_3090851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090851).length < 2 ^ (prefixWord ++ tailWord_3090851).sum := by decide
  have hdescent : baseEnd_3090851 < baseStart_3090851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090857 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 6]
def baseStart_3090857 : Nat := 118140960795 + 3090857 * 2 ^ 59
def prefixEnd_3090857 : Nat := 4983230072969 + 3 ^ 40 * 3090857 * 2
def baseEnd_3090857 : Nat := 1587095275313918741472913

theorem tailTrace_3090857 : CollatzResearch.WordTrace tailWord_3090857 prefixEnd_3090857 1587095275313918741472913 := by
  unfold tailWord_3090857
  simp only [CollatzResearch.WordTrace]
  refine ⟨112732816163360440194326825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75155210775573626796217883 112732816163360440194326825)
  ·
    refine ⟨84549612122520330145745119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112732816163360440194326825 84549612122520330145745119)
    ·
      refine ⟨126824418183780495218617679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84549612122520330145745119 126824418183780495218617679)
      ·
        refine ⟨190236627275670742827926519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126824418183780495218617679 190236627275670742827926519)
        ·
          refine ⟨285354940913506114241889779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190236627275670742827926519 285354940913506114241889779)
          ·
            refine ⟨428032411370259171362834669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285354940913506114241889779 428032411370259171362834669)
            ·
              refine ⟨160512154263847189261063001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 428032411370259171362834669 160512154263847189261063001)
              ·
                refine ⟨120384115697885391945797251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160512154263847189261063001 120384115697885391945797251)
                ·
                  refine ⟨180576173546828087918695877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120384115697885391945797251 180576173546828087918695877)
                  ·
                    refine ⟨33858032540030266484755477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 180576173546828087918695877 33858032540030266484755477)
                    ·
                      refine ⟨1587095275313918741472913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33858032540030266484755477 1587095275313918741472913)
                      ·
                        rfl

theorem cell23_3090857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_3090857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090857 prefixEnd_3090857 := by exact prefixLift 3090857
  have htrace : WordTrace (prefixWord ++ tailWord_3090857) baseStart_3090857 baseEnd_3090857 := by
    simpa [prefixWord, tailWord_3090857, baseEnd_3090857] using wordTrace_append hprefix tailTrace_3090857
  have hstable : (prefixWord ++ tailWord_3090857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090857).length < 2 ^ (prefixWord ++ tailWord_3090857).sum := by decide
  have hdescent : baseEnd_3090857 < baseStart_3090857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090867 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 3, 9]
def baseStart_3090867 : Nat := 118140960795 + 3090867 * 2 ^ 59
def prefixEnd_3090867 : Nat := 4983230072969 + 3 ^ 40 * 3090867 * 2
def baseEnd_3090867 : Nat := 529033470040154567449289

theorem tailTrace_3090867 : CollatzResearch.WordTrace tailWord_3090867 prefixEnd_3090867 529033470040154567449289 := by
  unfold tailWord_3090867
  simp only [CollatzResearch.WordTrace]
  refine ⟨112733180893324211902190855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75155453928882807934793903 112733180893324211902190855)
  ·
    refine ⟨169099771339986317853286283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112733180893324211902190855 169099771339986317853286283)
    ·
      refine ⟨253649657009979476779929425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169099771339986317853286283 253649657009979476779929425)
      ·
        refine ⟨190237242757484607584947069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253649657009979476779929425 190237242757484607584947069)
        ·
          refine ⟨71338966034056727844355151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190237242757484607584947069 71338966034056727844355151)
          ·
            refine ⟨107008449051085091766532727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71338966034056727844355151 107008449051085091766532727)
            ·
              refine ⟨160512673576627637649799091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107008449051085091766532727 160512673576627637649799091)
              ·
                refine ⟨240769010364941456474698637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160512673576627637649799091 240769010364941456474698637)
                ·
                  refine ⟨90288378886853046178011989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240769010364941456474698637 90288378886853046178011989)
                  ·
                    refine ⟨529033470040154567449289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 90288378886853046178011989 529033470040154567449289)
                    ·
                      rfl

theorem cell23_3090867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 9].length) (baseStart_3090867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090867 prefixEnd_3090867 := by exact prefixLift 3090867
  have htrace : WordTrace (prefixWord ++ tailWord_3090867) baseStart_3090867 baseEnd_3090867 := by
    simpa [prefixWord, tailWord_3090867, baseEnd_3090867] using wordTrace_append hprefix tailTrace_3090867
  have hstable : (prefixWord ++ tailWord_3090867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090867).length < 2 ^ (prefixWord ++ tailWord_3090867).sum := by decide
  have hdescent : baseEnd_3090867 < baseStart_3090867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090891 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 3, 3, 2]
def baseStart_3090891 : Nat := 118140960795 + 3090891 * 2 ^ 59
def prefixEnd_3090891 : Nat := 4983230072969 + 3 ^ 40 * 3090891 * 2
def baseEnd_3090891 : Nat := 1587112733656171608447757

theorem tailTrace_3090891 : CollatzResearch.WordTrace tailWord_3090891 prefixEnd_3090891 1587112733656171608447757 := by
  unfold tailWord_3090891
  simp only [CollatzResearch.WordTrace]
  refine ⟨112734056245237264001064527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75156037496824842667376351 112734056245237264001064527)
  ·
    refine ⟨169101084367855896001596791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112734056245237264001064527 169101084367855896001596791)
    ·
      refine ⟨253651626551783844002395187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169101084367855896001596791 253651626551783844002395187)
      ·
        refine ⟨380477439827675766003592781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253651626551783844002395187 380477439827675766003592781)
        ·
          refine ⟨142679039935378412251347293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380477439827675766003592781 142679039935378412251347293)
          ·
            refine ⟨53504639975766904594255235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142679039935378412251347293 53504639975766904594255235)
            ·
              refine ⟨80256959963650356891382853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53504639975766904594255235 80256959963650356891382853)
              ·
                refine ⟨15048179993184441917134285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80256959963650356891382853 15048179993184441917134285)
                ·
                  refine ⟨5643067497444165718925357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15048179993184441917134285 5643067497444165718925357)
                  ·
                    refine ⟨2116150311541562144597009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5643067497444165718925357 2116150311541562144597009)
                    ·
                      refine ⟨1587112733656171608447757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2116150311541562144597009 1587112733656171608447757)
                      ·
                        rfl

theorem cell23_3090891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 3, 2].length) (baseStart_3090891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090891 prefixEnd_3090891 := by exact prefixLift 3090891
  have htrace : WordTrace (prefixWord ++ tailWord_3090891) baseStart_3090891 baseEnd_3090891 := by
    simpa [prefixWord, tailWord_3090891, baseEnd_3090891] using wordTrace_append hprefix tailTrace_3090891
  have hstable : (prefixWord ++ tailWord_3090891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090891).length < 2 ^ (prefixWord ++ tailWord_3090891).sum := by decide
  have hdescent : baseEnd_3090891 < baseStart_3090891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090892 : List Nat := [2, 2, 1, 4, 4, 1, 2, 1, 2, 4]
def baseStart_3090892 : Nat := 118140960795 + 3090892 * 2 ^ 59
def prefixEnd_3090892 : Nat := 4983230072969 + 3 ^ 40 * 3090892 * 2
def baseEnd_3090892 : Nat := 529037749045608701511751

theorem tailTrace_3090892 : CollatzResearch.WordTrace tailWord_3090892 prefixEnd_3090892 529037749045608701511751 := by
  unfold tailWord_3090892
  simp only [CollatzResearch.WordTrace]
  refine ⟨56367046359116820585925465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75156061812155760781233953 56367046359116820585925465)
  ·
    refine ⟨42275284769337615439444099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56367046359116820585925465 42275284769337615439444099)
    ·
      refine ⟨63412927154006423159166149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42275284769337615439444099 63412927154006423159166149)
      ·
        refine ⟨11889923841376204342343653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63412927154006423159166149 11889923841376204342343653)
        ·
          refine ⟨2229360720258038314189435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11889923841376204342343653 2229360720258038314189435)
          ·
            refine ⟨3344041080387057471284153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2229360720258038314189435 3344041080387057471284153)
            ·
              refine ⟨2508030810290293103463115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3344041080387057471284153 2508030810290293103463115)
              ·
                refine ⟨3762046215435439655194673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2508030810290293103463115 3762046215435439655194673)
                ·
                  refine ⟨2821534661576579741396005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3762046215435439655194673 2821534661576579741396005)
                  ·
                    refine ⟨529037749045608701511751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2821534661576579741396005 529037749045608701511751)
                    ·
                      rfl

theorem cell23_3090892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_3090892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090892 prefixEnd_3090892 := by exact prefixLift 3090892
  have htrace : WordTrace (prefixWord ++ tailWord_3090892) baseStart_3090892 baseEnd_3090892 := by
    simpa [prefixWord, tailWord_3090892, baseEnd_3090892] using wordTrace_append hprefix tailTrace_3090892
  have hstable : (prefixWord ++ tailWord_3090892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090892).length < 2 ^ (prefixWord ++ tailWord_3090892).sum := by decide
  have hdescent : baseEnd_3090892 < baseStart_3090892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090924 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 5]
def baseStart_3090924 : Nat := 118140960795 + 3090924 * 2 ^ 59
def prefixEnd_3090924 : Nat := 4983230072969 + 3 ^ 40 * 3090924 * 2
def baseEnd_3090924 : Nat := 1587129678517769979335105

theorem tailTrace_3090924 : CollatzResearch.WordTrace tailWord_3090924 prefixEnd_3090924 1587129678517769979335105 := by
  unfold tailWord_3090924
  simp only [CollatzResearch.WordTrace]
  refine ⟨56367629927058855318507913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75156839902745140424677217 56367629927058855318507913)
  ·
    refine ⟨42275722445294141488880935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56367629927058855318507913 42275722445294141488880935)
    ·
      refine ⟨63413583667941212233321403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42275722445294141488880935 63413583667941212233321403)
      ·
        refine ⟨95120375501911818349982105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63413583667941212233321403 95120375501911818349982105)
        ·
          refine ⟨71340281626433863762486579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95120375501911818349982105 71340281626433863762486579)
          ·
            refine ⟨107010422439650795643729869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71340281626433863762486579 107010422439650795643729869)
            ·
              refine ⟨40128908414869048366398701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107010422439650795643729869 40128908414869048366398701)
              ·
                refine ⟨15048340655575893137399513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40128908414869048366398701 15048340655575893137399513)
                ·
                  refine ⟨11286255491681919853049635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15048340655575893137399513 11286255491681919853049635)
                  ·
                    refine ⟨16929383237522879779574453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11286255491681919853049635 16929383237522879779574453)
                    ·
                      refine ⟨1587129678517769979335105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16929383237522879779574453 1587129678517769979335105)
                      ·
                        rfl

theorem cell23_3090924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_3090924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090924 prefixEnd_3090924 := by exact prefixLift 3090924
  have htrace : WordTrace (prefixWord ++ tailWord_3090924) baseStart_3090924 baseEnd_3090924 := by
    simpa [prefixWord, tailWord_3090924, baseEnd_3090924] using wordTrace_append hprefix tailTrace_3090924
  have hstable : (prefixWord ++ tailWord_3090924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090924).length < 2 ^ (prefixWord ++ tailWord_3090924).sum := by decide
  have hdescent : baseEnd_3090924 < baseStart_3090924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090933 : List Nat := [1, 3, 5, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_3090933 : Nat := 118140960795 + 3090933 * 2 ^ 59
def prefixEnd_3090933 : Nat := 4983230072969 + 3 ^ 40 * 3090933 * 2
def baseEnd_3090933 : Nat := 1587134299843660444122565

theorem tailTrace_3090933 : CollatzResearch.WordTrace tailWord_3090933 prefixEnd_3090933 1587134299843660444122565 := by
  unfold tailWord_3090933
  simp only [CollatzResearch.WordTrace]
  refine ⟨112735588111085105174093453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75157058740723403449395635 112735588111085105174093453)
  ·
    refine ⟨42275845541656914440285045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112735588111085105174093453 42275845541656914440285045)
    ·
      refine ⟨3963360519530335728776723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42275845541656914440285045 3963360519530335728776723)
      ·
        refine ⟨5945040779295503593165085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3963360519530335728776723 5945040779295503593165085)
        ·
          refine ⟨2229390292235813847436907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5945040779295503593165085 2229390292235813847436907)
          ·
            refine ⟨3344085438353720771155361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2229390292235813847436907 3344085438353720771155361)
            ·
              refine ⟨2508064078765290578366521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3344085438353720771155361 2508064078765290578366521)
              ·
                refine ⟨1881048059073967933774891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2508064078765290578366521 1881048059073967933774891)
                ·
                  refine ⟨2821572088610951900662337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881048059073967933774891 2821572088610951900662337)
                  ·
                    refine ⟨2116179066458213925496753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2821572088610951900662337 2116179066458213925496753)
                    ·
                      refine ⟨1587134299843660444122565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2116179066458213925496753 1587134299843660444122565)
                      ·
                        rfl

theorem cell23_3090933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_3090933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090933 prefixEnd_3090933 := by exact prefixLift 3090933
  have htrace : WordTrace (prefixWord ++ tailWord_3090933) baseStart_3090933 baseEnd_3090933 := by
    simpa [prefixWord, tailWord_3090933, baseEnd_3090933] using wordTrace_append hprefix tailTrace_3090933
  have hstable : (prefixWord ++ tailWord_3090933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090933).length < 2 ^ (prefixWord ++ tailWord_3090933).sum := by decide
  have hdescent : baseEnd_3090933 < baseStart_3090933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090955 : List Nat := [1, 1, 1, 1, 7, 1, 2, 3, 2, 2, 2]
def baseStart_3090955 : Nat := 118140960795 + 3090955 * 2 ^ 59
def prefixEnd_3090955 : Nat := 4983230072969 + 3 ^ 40 * 3090955 * 2
def baseEnd_3090955 : Nat := 1587145596418059358047463

theorem tailTrace_3090955 : CollatzResearch.WordTrace tailWord_3090955 prefixEnd_3090955 1587145596418059358047463 := by
  unfold tailWord_3090955
  simp only [CollatzResearch.WordTrace]
  refine ⟨112736390517005402931394319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75157593678003601954262879 112736390517005402931394319)
  ·
    refine ⟨169104585775508104397091479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112736390517005402931394319 169104585775508104397091479)
    ·
      refine ⟨253656878663262156595637219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169104585775508104397091479 253656878663262156595637219)
      ·
        refine ⟨380485317994893234893455829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253656878663262156595637219 380485317994893234893455829)
        ·
          refine ⟨8917624640505310192815371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 380485317994893234893455829 8917624640505310192815371)
          ·
            refine ⟨13376436960757965289223057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8917624640505310192815371 13376436960757965289223057)
            ·
              refine ⟨10032327720568473966917293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13376436960757965289223057 10032327720568473966917293)
              ·
                refine ⟨3762122895213177737593985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10032327720568473966917293 3762122895213177737593985)
                ·
                  refine ⟨2821592171409883303195489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3762122895213177737593985 2821592171409883303195489)
                  ·
                    refine ⟨2116194128557412477396617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2821592171409883303195489 2116194128557412477396617)
                    ·
                      refine ⟨1587145596418059358047463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2116194128557412477396617 1587145596418059358047463)
                      ·
                        rfl

theorem cell23_3090955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 2, 2].length) (baseStart_3090955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3090955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3090955 prefixEnd_3090955 := by exact prefixLift 3090955
  have htrace : WordTrace (prefixWord ++ tailWord_3090955) baseStart_3090955 baseEnd_3090955 := by
    simpa [prefixWord, tailWord_3090955, baseEnd_3090955] using wordTrace_append hprefix tailTrace_3090955
  have hstable : (prefixWord ++ tailWord_3090955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090955).length < 2 ^ (prefixWord ++ tailWord_3090955).sum := by decide
  have hdescent : baseEnd_3090955 < baseStart_3090955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091006 : List Nat := [4, 2, 1, 4, 1, 1, 3, 1, 2, 2, 2]
def baseStart_3091006 : Nat := 118140960795 + 3091006 * 2 ^ 59
def prefixEnd_3091006 : Nat := 4983230072969 + 3 ^ 40 * 3091006 * 2
def baseEnd_3091006 : Nat := 1587171783931438658509729

theorem tailTrace_3091006 : CollatzResearch.WordTrace tailWord_3091006 prefixEnd_3091006 1587171783931438658509729 := by
  unfold tailWord_3091006
  simp only [CollatzResearch.WordTrace]
  refine ⟨14092281329977579830187609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75158833759880425761000581 14092281329977579830187609)
  ·
    refine ⟨10569210997483184872640707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14092281329977579830187609 10569210997483184872640707)
    ·
      refine ⟨15853816496224777308961061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10569210997483184872640707 15853816496224777308961061)
      ·
        refine ⟨2972590593042145745430199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15853816496224777308961061 2972590593042145745430199)
        ·
          refine ⟨4458885889563218618145299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2972590593042145745430199 4458885889563218618145299)
          ·
            refine ⟨6688328834344827927217949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4458885889563218618145299 6688328834344827927217949)
            ·
              refine ⟨2508123312879310472706731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6688328834344827927217949 2508123312879310472706731)
              ·
                refine ⟨3762184969318965709060097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2508123312879310472706731 3762184969318965709060097)
                ·
                  refine ⟨2821638726989224281795073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3762184969318965709060097 2821638726989224281795073)
                  ·
                    refine ⟨2116229045241918211346305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2821638726989224281795073 2116229045241918211346305)
                    ·
                      refine ⟨1587171783931438658509729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2116229045241918211346305 1587171783931438658509729)
                      ·
                        rfl

theorem cell23_3091006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_3091006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091006 prefixEnd_3091006 := by exact prefixLift 3091006
  have htrace : WordTrace (prefixWord ++ tailWord_3091006) baseStart_3091006 baseEnd_3091006 := by
    simpa [prefixWord, tailWord_3091006, baseEnd_3091006] using wordTrace_append hprefix tailTrace_3091006
  have hstable : (prefixWord ++ tailWord_3091006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091006).length < 2 ^ (prefixWord ++ tailWord_3091006).sum := by decide
  have hdescent : baseEnd_3091006 < baseStart_3091006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091024 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 6]
def baseStart_3091024 : Nat := 118140960795 + 3091024 * 2 ^ 59
def prefixEnd_3091024 : Nat := 4983230072969 + 3 ^ 40 * 3091024 * 2
def baseEnd_3091024 : Nat := 1587181026583219588084645

theorem tailTrace_3091024 : CollatzResearch.WordTrace tailWord_3091024 prefixEnd_3091024 1587181026583219588084645 := by
  unfold tailWord_3091024
  simp only [CollatzResearch.WordTrace]
  refine ⟨56369453576877713857828063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75159271435836951810437417 56369453576877713857828063)
  ·
    refine ⟨84554180365316570786742095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56369453576877713857828063 84554180365316570786742095)
    ·
      refine ⟨126831270547974856180113143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84554180365316570786742095 126831270547974856180113143)
      ·
        refine ⟨190246905821962284270169715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126831270547974856180113143 190246905821962284270169715)
        ·
          refine ⟨285370358732943426405254573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190246905821962284270169715 285370358732943426405254573)
          ·
            refine ⟨107013884524853784901970465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285370358732943426405254573 107013884524853784901970465)
            ·
              refine ⟨80260413393640338676477849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107013884524853784901970465 80260413393640338676477849)
              ·
                refine ⟨60195310045230254007358387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80260413393640338676477849 60195310045230254007358387)
                ·
                  refine ⟨90292965067845381011037581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60195310045230254007358387 90292965067845381011037581)
                  ·
                    refine ⟨33859861900442017879139093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90292965067845381011037581 33859861900442017879139093)
                    ·
                      refine ⟨1587181026583219588084645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33859861900442017879139093 1587181026583219588084645)
                      ·
                        rfl

theorem cell23_3091024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_3091024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091024 prefixEnd_3091024 := by exact prefixLift 3091024
  have htrace : WordTrace (prefixWord ++ tailWord_3091024) baseStart_3091024 baseEnd_3091024 := by
    simpa [prefixWord, tailWord_3091024, baseEnd_3091024] using wordTrace_append hprefix tailTrace_3091024
  have hstable : (prefixWord ++ tailWord_3091024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091024).length < 2 ^ (prefixWord ++ tailWord_3091024).sum := by decide
  have hdescent : baseEnd_3091024 < baseStart_3091024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091031 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 3]
def baseStart_3091031 : Nat := 118140960795 + 3091031 * 2 ^ 59
def prefixEnd_3091031 : Nat := 4983230072969 + 3 ^ 40 * 3091031 * 2
def baseEnd_3091031 : Nat := 1587184620947801060697113

theorem tailTrace_3091031 : CollatzResearch.WordTrace tailWord_3091031 prefixEnd_3091031 1587184620947801060697113 := by
  unfold tailWord_3091031
  simp only [CollatzResearch.WordTrace]
  refine ⟨112739162464730067911160947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75159441643153378607440631 112739162464730067911160947)
  ·
    refine ⟨169108743697095101866741421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112739162464730067911160947 169108743697095101866741421)
    ·
      refine ⟨63415778886410663200028033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169108743697095101866741421 63415778886410663200028033)
      ·
        refine ⟨47561834164807997400021025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63415778886410663200028033 47561834164807997400021025)
        ·
          refine ⟨35671375623605998050015769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47561834164807997400021025 35671375623605998050015769)
          ·
            refine ⟨26753531717704498537511827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35671375623605998050015769 26753531717704498537511827)
            ·
              refine ⟨40130297576556747806267741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26753531717704498537511827 40130297576556747806267741)
              ·
                refine ⟨15048861591208780427350403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40130297576556747806267741 15048861591208780427350403)
                ·
                  refine ⟨22573292386813170641025605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15048861591208780427350403 22573292386813170641025605)
                  ·
                    refine ⟨4232492322527469495192301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22573292386813170641025605 4232492322527469495192301)
                    ·
                      refine ⟨1587184620947801060697113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4232492322527469495192301 1587184620947801060697113)
                      ·
                        rfl

theorem cell23_3091031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_3091031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091031 prefixEnd_3091031 := by exact prefixLift 3091031
  have htrace : WordTrace (prefixWord ++ tailWord_3091031) baseStart_3091031 baseEnd_3091031 := by
    simpa [prefixWord, tailWord_3091031, baseEnd_3091031] using wordTrace_append hprefix tailTrace_3091031
  have hstable : (prefixWord ++ tailWord_3091031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091031).length < 2 ^ (prefixWord ++ tailWord_3091031).sum := by decide
  have hdescent : baseEnd_3091031 < baseStart_3091031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091068 : List Nat := [2, 2, 2, 1, 1, 2, 6, 1, 6]
def baseStart_3091068 : Nat := 118140960795 + 3091068 * 2 ^ 59
def prefixEnd_3091068 : Nat := 4983230072969 + 3 ^ 40 * 3091068 * 2
def baseEnd_3091068 : Nat := 176355957748001935103827

theorem tailTrace_3091068 : CollatzResearch.WordTrace tailWord_3091068 prefixEnd_3091068 176355957748001935103827 := by
  unfold tailWord_3091068
  simp only [CollatzResearch.WordTrace]
  refine ⟨56370255982798011615128929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75160341310397348820171905 56370255982798011615128929)
  ·
    refine ⟨42277691987098508711346697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56370255982798011615128929 42277691987098508711346697)
    ·
      refine ⟨31708268990323881533510023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42277691987098508711346697 31708268990323881533510023)
      ·
        refine ⟨47562403485485822300265035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31708268990323881533510023 47562403485485822300265035)
        ·
          refine ⟨71343605228228733450397553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47562403485485822300265035 71343605228228733450397553)
          ·
            refine ⟨53507703921171550087798165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71343605228228733450397553 53507703921171550087798165)
            ·
              refine ⟨2508173621304916410365539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53507703921171550087798165 2508173621304916410365539)
              ·
                refine ⟨3762260431957374615548309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2508173621304916410365539 3762260431957374615548309)
                ·
                  refine ⟨176355957748001935103827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3762260431957374615548309 176355957748001935103827)
                  ·
                    rfl

theorem cell23_3091068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 6].length) (baseStart_3091068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091068 prefixEnd_3091068 := by exact prefixLift 3091068
  have htrace : WordTrace (prefixWord ++ tailWord_3091068) baseStart_3091068 baseEnd_3091068 := by
    simpa [prefixWord, tailWord_3091068, baseEnd_3091068] using wordTrace_append hprefix tailTrace_3091068
  have hstable : (prefixWord ++ tailWord_3091068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091068).length < 2 ^ (prefixWord ++ tailWord_3091068).sum := by decide
  have hdescent : baseEnd_3091068 < baseStart_3091068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091135 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 5, 2, 2]
def baseStart_3091135 : Nat := 118140960795 + 3091135 * 2 ^ 59
def prefixEnd_3091135 : Nat := 4983230072969 + 3 ^ 40 * 3091135 * 2
def baseEnd_3091135 : Nat := 1587238022935868653796635

theorem tailTrace_3091135 : CollatzResearch.WordTrace tailWord_3091135 prefixEnd_3091135 1587238022935868653796635 := by
  unfold tailWord_3091135
  simp only [CollatzResearch.WordTrace]
  refine ⟨112742955656353293672946859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75161970437568862448631239 112742955656353293672946859)
  ·
    refine ⟨169114433484529940509420289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112742955656353293672946859 169114433484529940509420289)
    ·
      refine ⟨126835825113397455382065217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169114433484529940509420289 126835825113397455382065217)
      ·
        refine ⟨95126868835048091536548913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126835825113397455382065217 95126868835048091536548913)
        ·
          refine ⟨71345151626286068652411685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95126868835048091536548913 71345151626286068652411685)
          ·
            refine ⟨13377215929928637872327191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71345151626286068652411685 13377215929928637872327191)
            ·
              refine ⟨20065823894892956808490787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13377215929928637872327191 20065823894892956808490787)
              ·
                refine ⟨30098735842339435212736181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20065823894892956808490787 30098735842339435212736181)
                ·
                  refine ⟨2821756485219322051194017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30098735842339435212736181 2821756485219322051194017)
                  ·
                    refine ⟨2116317363914491538395513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2821756485219322051194017 2116317363914491538395513)
                    ·
                      refine ⟨1587238022935868653796635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2116317363914491538395513 1587238022935868653796635)
                      ·
                        rfl

theorem cell23_3091135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 2, 2].length) (baseStart_3091135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091135 prefixEnd_3091135 := by exact prefixLift 3091135
  have htrace : WordTrace (prefixWord ++ tailWord_3091135) baseStart_3091135 baseEnd_3091135 := by
    simpa [prefixWord, tailWord_3091135, baseEnd_3091135] using wordTrace_append hprefix tailTrace_3091135
  have hstable : (prefixWord ++ tailWord_3091135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091135).length < 2 ^ (prefixWord ++ tailWord_3091135).sum := by decide
  have hdescent : baseEnd_3091135 < baseStart_3091135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091169 : List Nat := [1, 2, 3, 1, 4, 1, 2, 4, 1, 2, 2]
def baseStart_3091169 : Nat := 118140960795 + 3091169 * 2 ^ 59
def prefixEnd_3091169 : Nat := 4983230072969 + 3 ^ 40 * 3091169 * 2
def baseEnd_3091169 : Nat := 1587255481278121520771479

theorem tailTrace_3091169 : CollatzResearch.WordTrace tailWord_3091169 prefixEnd_3091169 1587255481278121520771479 := by
  unfold tailWord_3091169
  simp only [CollatzResearch.WordTrace]
  refine ⟨112744195738230117479684561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75162797158820078319789707 112744195738230117479684561)
  ·
    refine ⟨84558146803672588109763421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112744195738230117479684561 84558146803672588109763421)
    ·
      refine ⟨31709305051377220541161283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84558146803672588109763421 31709305051377220541161283)
      ·
        refine ⟨47563957577065830811741925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31709305051377220541161283 47563957577065830811741925)
        ·
          refine ⟨8918242045699843277201611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47563957577065830811741925 8918242045699843277201611)
          ·
            refine ⟨13377363068549764915802417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8918242045699843277201611 13377363068549764915802417)
            ·
              refine ⟨10033022301412323686851813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13377363068549764915802417 10033022301412323686851813)
              ·
                refine ⟨1881191681514810691284715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10033022301412323686851813 1881191681514810691284715)
                ·
                  refine ⟨2821787522272216036927073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881191681514810691284715 2821787522272216036927073)
                  ·
                    refine ⟨2116340641704162027695305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2821787522272216036927073 2116340641704162027695305)
                    ·
                      refine ⟨1587255481278121520771479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2116340641704162027695305 1587255481278121520771479)
                      ·
                        rfl

theorem cell23_3091169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_3091169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091169 prefixEnd_3091169 := by exact prefixLift 3091169
  have htrace : WordTrace (prefixWord ++ tailWord_3091169) baseStart_3091169 baseEnd_3091169 := by
    simpa [prefixWord, tailWord_3091169, baseEnd_3091169] using wordTrace_append hprefix tailTrace_3091169
  have hstable : (prefixWord ++ tailWord_3091169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091169).length < 2 ^ (prefixWord ++ tailWord_3091169).sum := by decide
  have hdescent : baseEnd_3091169 < baseStart_3091169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091202 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_3091202 : Nat := 118140960795 + 3091202 * 2 ^ 59
def prefixEnd_3091202 : Nat := 4983230072969 + 3 ^ 40 * 3091202 * 2
def baseEnd_3091202 : Nat := 1587272426139719891658827

theorem tailTrace_3091202 : CollatzResearch.WordTrace tailWord_3091202 prefixEnd_3091202 1587272426139719891658827 := by
  unfold tailWord_3091202
  simp only [CollatzResearch.WordTrace]
  refine ⟨28186349836777641028908965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75163599564740376077090573 28186349836777641028908965)
  ·
    refine ⟨5284940594395807692920431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28186349836777641028908965 5284940594395807692920431)
    ·
      refine ⟨7927410891593711539380647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5284940594395807692920431 7927410891593711539380647)
      ·
        refine ⟨11891116337390567309070971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7927410891593711539380647 11891116337390567309070971)
        ·
          refine ⟨17836674506085850963606457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11891116337390567309070971 17836674506085850963606457)
          ·
            refine ⟨13377505879564388222704843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17836674506085850963606457 13377505879564388222704843)
            ·
              refine ⟨20066258819346582334057265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13377505879564388222704843 20066258819346582334057265)
              ·
                refine ⟨15049694114509936750542949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20066258819346582334057265 15049694114509936750542949)
                ·
                  refine ⟨2821817646470613140726803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15049694114509936750542949 2821817646470613140726803)
                  ·
                    refine ⟨4232726469705919711090205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2821817646470613140726803 4232726469705919711090205)
                    ·
                      refine ⟨1587272426139719891658827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4232726469705919711090205 1587272426139719891658827)
                      ·
                        rfl

theorem cell23_3091202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_3091202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091202 prefixEnd_3091202 := by exact prefixLift 3091202
  have htrace : WordTrace (prefixWord ++ tailWord_3091202) baseStart_3091202 baseEnd_3091202 := by
    simpa [prefixWord, tailWord_3091202, baseEnd_3091202] using wordTrace_append hprefix tailTrace_3091202
  have hstable : (prefixWord ++ tailWord_3091202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091202).length < 2 ^ (prefixWord ++ tailWord_3091202).sum := by decide
  have hdescent : baseEnd_3091202 < baseStart_3091202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091236 : List Nat := [2, 3, 1, 3, 3, 2, 2, 1, 2, 1, 3]
def baseStart_3091236 : Nat := 118140960795 + 3091236 * 2 ^ 59
def prefixEnd_3091236 : Nat := 4983230072969 + 3 ^ 40 * 3091236 * 2
def baseEnd_3091236 : Nat := 1587289884481972758633671

theorem tailTrace_3091236 : CollatzResearch.WordTrace tailWord_3091236 prefixEnd_3091236 1587289884481972758633671 := by
  unfold tailWord_3091236
  simp only [CollatzResearch.WordTrace]
  refine ⟨56373319714493693961186781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75164426285991591948249041 56373319714493693961186781)
  ·
    refine ⟨21139994892935135235445043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56373319714493693961186781 21139994892935135235445043)
    ·
      refine ⟨31709992339402702853167565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21139994892935135235445043 31709992339402702853167565)
      ·
        refine ⟨11891247127276013569937837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31709992339402702853167565 11891247127276013569937837)
        ·
          refine ⟨4459217672728505088726689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11891247127276013569937837 4459217672728505088726689)
          ·
            refine ⟨3344413254546378816545017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4459217672728505088726689 3344413254546378816545017)
            ·
              refine ⟨2508309940909784112408763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3344413254546378816545017 2508309940909784112408763)
              ·
                refine ⟨3762464911364676168613145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2508309940909784112408763 3762464911364676168613145)
                ·
                  refine ⟨2821848683523507126459859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3762464911364676168613145 2821848683523507126459859)
                  ·
                    refine ⟨4232773025285260689689789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2821848683523507126459859 4232773025285260689689789)
                    ·
                      refine ⟨1587289884481972758633671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4232773025285260689689789 1587289884481972758633671)
                      ·
                        rfl

theorem cell23_3091236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_3091236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091236 prefixEnd_3091236 := by exact prefixLift 3091236
  have htrace : WordTrace (prefixWord ++ tailWord_3091236) baseStart_3091236 baseEnd_3091236 := by
    simpa [prefixWord, tailWord_3091236, baseEnd_3091236] using wordTrace_append hprefix tailTrace_3091236
  have hstable : (prefixWord ++ tailWord_3091236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091236).length < 2 ^ (prefixWord ++ tailWord_3091236).sum := by decide
  have hdescent : baseEnd_3091236 < baseStart_3091236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091241 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 9]
def baseStart_3091241 : Nat := 118140960795 + 3091241 * 2 ^ 59
def prefixEnd_3091241 : Nat := 4983230072969 + 3 ^ 40 * 3091241 * 2
def baseEnd_3091241 : Nat := 1587292451885245239071147

theorem tailTrace_3091241 : CollatzResearch.WordTrace tailWord_3091241 prefixEnd_3091241 1587292451885245239071147 := by
  unfold tailWord_3091241
  simp only [CollatzResearch.WordTrace]
  refine ⟨112746821793969273776305577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75164547862646182517537051 112746821793969273776305577)
  ·
    refine ⟨84560116345476955332229183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112746821793969273776305577 84560116345476955332229183)
    ·
      refine ⟨126840174518215432998343775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84560116345476955332229183 126840174518215432998343775)
      ·
        refine ⟨190260261777323149497515663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126840174518215432998343775 190260261777323149497515663)
        ·
          refine ⟨285390392665984724246273495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190260261777323149497515663 285390392665984724246273495)
          ·
            refine ⟨428085588998977086369410243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285390392665984724246273495 428085588998977086369410243)
            ·
              refine ⟨642128383498465629554115365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428085588998977086369410243 642128383498465629554115365)
              ·
                refine ⟨120399071905962305541396631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 642128383498465629554115365 120399071905962305541396631)
                ·
                  refine ⟨180598607858943458312094947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120399071905962305541396631 180598607858943458312094947)
                  ·
                    refine ⟨270897911788415187468142421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 180598607858943458312094947 270897911788415187468142421)
                    ·
                      refine ⟨1587292451885245239071147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 270897911788415187468142421 1587292451885245239071147)
                      ·
                        rfl

theorem cell23_3091241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_3091241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091241 prefixEnd_3091241 := by exact prefixLift 3091241
  have htrace : WordTrace (prefixWord ++ tailWord_3091241) baseStart_3091241 baseEnd_3091241 := by
    simpa [prefixWord, tailWord_3091241, baseEnd_3091241] using wordTrace_append hprefix tailTrace_3091241
  have hstable : (prefixWord ++ tailWord_3091241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091241).length < 2 ^ (prefixWord ++ tailWord_3091241).sum := by decide
  have hdescent : baseEnd_3091241 < baseStart_3091241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091246 : List Nat := [4, 1, 3, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_3091246 : Nat := 118140960795 + 3091246 * 2 ^ 59
def prefixEnd_3091246 : Nat := 4983230072969 + 3 ^ 40 * 3091246 * 2
def baseEnd_3091246 : Nat := 1587295019288517719508625

theorem tailTrace_3091246 : CollatzResearch.WordTrace tailWord_3091246 prefixEnd_3091246 1587295019288517719508625 := by
  unfold tailWord_3091246
  simp only [CollatzResearch.WordTrace]
  refine ⟨14093375519868894953779699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75164669439300773086825061 14093375519868894953779699)
  ·
    refine ⟨21140063279803342430669549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14093375519868894953779699 21140063279803342430669549)
    ·
      refine ⟨7927523729926253411501081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21140063279803342430669549 7927523729926253411501081)
      ·
        refine ⟨5945642797444690058625811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7927523729926253411501081 5945642797444690058625811)
        ·
          refine ⟨8918464196167035087938717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5945642797444690058625811 8918464196167035087938717)
          ·
            refine ⟨3344424073562638157977019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8918464196167035087938717 3344424073562638157977019)
            ·
              refine ⟨5016636110343957236965529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3344424073562638157977019 5016636110343957236965529)
              ·
                refine ⟨3762477082757967927724147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5016636110343957236965529 3762477082757967927724147)
                ·
                  refine ⟨5643715624136951891586221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762477082757967927724147 5643715624136951891586221)
                  ·
                    refine ⟨2116393359051356959344833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5643715624136951891586221 2116393359051356959344833)
                    ·
                      refine ⟨1587295019288517719508625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2116393359051356959344833 1587295019288517719508625)
                      ·
                        rfl

theorem cell23_3091246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_3091246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091246 prefixEnd_3091246 := by exact prefixLift 3091246
  have htrace : WordTrace (prefixWord ++ tailWord_3091246) baseStart_3091246 baseEnd_3091246 := by
    simpa [prefixWord, tailWord_3091246, baseEnd_3091246] using wordTrace_append hprefix tailTrace_3091246
  have hstable : (prefixWord ++ tailWord_3091246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091246).length < 2 ^ (prefixWord ++ tailWord_3091246).sum := by decide
  have hdescent : baseEnd_3091246 < baseStart_3091246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091285 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 1, 7, 2]
def baseStart_3091285 : Nat := 118140960795 + 3091285 * 2 ^ 59
def prefixEnd_3091285 : Nat := 4983230072969 + 3 ^ 40 * 3091285 * 2
def baseEnd_3091285 : Nat := 1587315045034043066920945

theorem tailTrace_3091285 : CollatzResearch.WordTrace tailWord_3091285 prefixEnd_3091285 1587315045034043066920945 := by
  unfold tailWord_3091285
  simp only [CollatzResearch.WordTrace]
  refine ⟨112748426605809869290907309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75165617737206579527271539 112748426605809869290907309)
  ·
    refine ⟨42280659977178700984090241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112748426605809869290907309 42280659977178700984090241)
    ·
      refine ⟨31710494982884025738067681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42280659977178700984090241 31710494982884025738067681)
      ·
        refine ⟨23782871237163019303550761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31710494982884025738067681 23782871237163019303550761)
        ·
          refine ⟨17837153427872264477663071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23782871237163019303550761 17837153427872264477663071)
          ·
            refine ⟨26755730141808396716494607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17837153427872264477663071 26755730141808396716494607)
            ·
              refine ⟨40133595212712595074741911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26755730141808396716494607 40133595212712595074741911)
              ·
                refine ⟨60200392819068892612112867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40133595212712595074741911 60200392819068892612112867)
                ·
                  refine ⟨90300589228603338918169301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60200392819068892612112867 90300589228603338918169301)
                  ·
                    refine ⟨2116420060045390755894593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 90300589228603338918169301 2116420060045390755894593)
                    ·
                      refine ⟨1587315045034043066920945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2116420060045390755894593 1587315045034043066920945)
                      ·
                        rfl

theorem cell23_3091285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_3091285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091285 prefixEnd_3091285 := by exact prefixLift 3091285
  have htrace : WordTrace (prefixWord ++ tailWord_3091285) baseStart_3091285 baseEnd_3091285 := by
    simpa [prefixWord, tailWord_3091285, baseEnd_3091285] using wordTrace_append hprefix tailTrace_3091285
  have hstable : (prefixWord ++ tailWord_3091285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091285).length < 2 ^ (prefixWord ++ tailWord_3091285).sum := by decide
  have hdescent : baseEnd_3091285 < baseStart_3091285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091292 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_3091292 : Nat := 118140960795 + 3091292 * 2 ^ 59
def prefixEnd_3091292 : Nat := 4983230072969 + 3 ^ 40 * 3091292 * 2
def baseEnd_3091292 : Nat := 1587318639398624539533413

theorem tailTrace_3091292 : CollatzResearch.WordTrace tailWord_3091292 prefixEnd_3091292 1587318639398624539533413 := by
  unfold tailWord_3091292
  simp only [CollatzResearch.WordTrace]
  refine ⟨56374340958392254743206065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75165787944523006324274753 56374340958392254743206065)
  ·
    refine ⟨42280755718794191057404549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56374340958392254743206065 42280755718794191057404549)
    ·
      refine ⟨7927641697273910823263353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42280755718794191057404549 7927641697273910823263353)
      ·
        refine ⟨5945731272955433117447515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7927641697273910823263353 5945731272955433117447515)
        ·
          refine ⟨8918596909433149676171273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5945731272955433117447515 8918596909433149676171273)
          ·
            refine ⟨6688947682074862257128455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8918596909433149676171273 6688947682074862257128455)
            ·
              refine ⟨10033421523112293385692683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6688947682074862257128455 10033421523112293385692683)
              ·
                refine ⟨15050132284668440078539025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10033421523112293385692683 15050132284668440078539025)
                ·
                  refine ⟨11287599213501330058904269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15050132284668440078539025 11287599213501330058904269)
                  ·
                    refine ⟨4232849705062998772089101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11287599213501330058904269 4232849705062998772089101)
                    ·
                      refine ⟨1587318639398624539533413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4232849705062998772089101 1587318639398624539533413)
                      ·
                        rfl

theorem cell23_3091292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_3091292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091292 prefixEnd_3091292 := by exact prefixLift 3091292
  have htrace : WordTrace (prefixWord ++ tailWord_3091292) baseStart_3091292 baseEnd_3091292 := by
    simpa [prefixWord, tailWord_3091292, baseEnd_3091292] using wordTrace_append hprefix tailTrace_3091292
  have hstable : (prefixWord ++ tailWord_3091292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091292).length < 2 ^ (prefixWord ++ tailWord_3091292).sum := by decide
  have hdescent : baseEnd_3091292 < baseStart_3091292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091315 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 4]
def baseStart_3091315 : Nat := 118140960795 + 3091315 * 2 ^ 59
def prefixEnd_3091315 : Nat := 4983230072969 + 3 ^ 40 * 3091315 * 2
def baseEnd_3091315 : Nat := 1587330449453677949545807

theorem tailTrace_3091315 : CollatzResearch.WordTrace tailWord_3091315 prefixEnd_3091315 1587330449453677949545807 := by
  unfold tailWord_3091315
  simp only [CollatzResearch.WordTrace]
  refine ⟨112749520795701184414499399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75166347197134122942999599 112749520795701184414499399)
  ·
    refine ⟨169124281193551776621749099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112749520795701184414499399 169124281193551776621749099)
    ·
      refine ⟨253686421790327664932623649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169124281193551776621749099 253686421790327664932623649)
      ·
        refine ⟨190264816342745748699467737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253686421790327664932623649 190264816342745748699467737)
        ·
          refine ⟨142698612257059311524600803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190264816342745748699467737 142698612257059311524600803)
          ·
            refine ⟨214047918385588967286901205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142698612257059311524600803 214047918385588967286901205)
            ·
              refine ⟨5016748087162241420786747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 214047918385588967286901205 5016748087162241420786747)
              ·
                refine ⟨7525122130743362131180121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5016748087162241420786747 7525122130743362131180121)
                ·
                  refine ⟨5643841598057521598385091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7525122130743362131180121 5643841598057521598385091)
                  ·
                    refine ⟨8465762397086282397577637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5643841598057521598385091 8465762397086282397577637)
                    ·
                      refine ⟨1587330449453677949545807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8465762397086282397577637 1587330449453677949545807)
                      ·
                        rfl

theorem cell23_3091315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 4].length) (baseStart_3091315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091315 prefixEnd_3091315 := by exact prefixLift 3091315
  have htrace : WordTrace (prefixWord ++ tailWord_3091315) baseStart_3091315 baseEnd_3091315 := by
    simpa [prefixWord, tailWord_3091315, baseEnd_3091315] using wordTrace_append hprefix tailTrace_3091315
  have hstable : (prefixWord ++ tailWord_3091315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091315).length < 2 ^ (prefixWord ++ tailWord_3091315).sum := by decide
  have hdescent : baseEnd_3091315 < baseStart_3091315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091392 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 4, 3, 2]
def baseStart_3091392 : Nat := 118140960795 + 3091392 * 2 ^ 59
def prefixEnd_3091392 : Nat := 4983230072969 + 3 ^ 40 * 3091392 * 2
def baseEnd_3091392 : Nat := 1587369987464074148282953

theorem tailTrace_3091392 : CollatzResearch.WordTrace tailWord_3091392 prefixEnd_3091392 1587369987464074148282953 := by
  unfold tailWord_3091392
  simp only [CollatzResearch.WordTrace]
  refine ⟨56376164608211113282526215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75168219477614817710034953 56376164608211113282526215)
  ·
    refine ⟨84564246912316669923789323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56376164608211113282526215 84564246912316669923789323)
    ·
      refine ⟨126846370368475004885683985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84564246912316669923789323 126846370368475004885683985)
      ·
        refine ⟨95134777776356253664262989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126846370368475004885683985 95134777776356253664262989)
        ·
          refine ⟨35675541666133595124098621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95134777776356253664262989 35675541666133595124098621)
          ·
            refine ⟨13378328124800098171536983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35675541666133595124098621 13378328124800098171536983)
            ·
              refine ⟨20067492187200147257305475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13378328124800098171536983 20067492187200147257305475)
              ·
                refine ⟨30101238280800220885958213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20067492187200147257305475 30101238280800220885958213)
                ·
                  refine ⟨5643982177650041416117165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30101238280800220885958213 5643982177650041416117165)
                  ·
                    refine ⟨2116493316618765531043937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5643982177650041416117165 2116493316618765531043937)
                    ·
                      refine ⟨1587369987464074148282953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2116493316618765531043937 1587369987464074148282953)
                      ·
                        rfl

theorem cell23_3091392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 4, 3, 2].length) (baseStart_3091392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091392 prefixEnd_3091392 := by exact prefixLift 3091392
  have htrace : WordTrace (prefixWord ++ tailWord_3091392) baseStart_3091392 baseEnd_3091392 := by
    simpa [prefixWord, tailWord_3091392, baseEnd_3091392] using wordTrace_append hprefix tailTrace_3091392
  have hstable : (prefixWord ++ tailWord_3091392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091392).length < 2 ^ (prefixWord ++ tailWord_3091392).sum := by decide
  have hdescent : baseEnd_3091392 < baseStart_3091392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091399 : List Nat := [1, 1, 4, 1, 1, 2, 2, 6, 1, 1, 3]
def baseStart_3091399 : Nat := 118140960795 + 3091399 * 2 ^ 59
def prefixEnd_3091399 : Nat := 4983230072969 + 3 ^ 40 * 3091399 * 2
def baseEnd_3091399 : Nat := 1587373581828655620895421

theorem tailTrace_3091399 : CollatzResearch.WordTrace tailWord_3091399 prefixEnd_3091399 1587373581828655620895421 := by
  unfold tailWord_3091399
  simp only [CollatzResearch.WordTrace]
  refine ⟨112752584527396866760557251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75168389684931244507038167 112752584527396866760557251)
  ·
    refine ⟨169128876791095300140835877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112752584527396866760557251 169128876791095300140835877)
    ·
      refine ⟨31711664398330368776406727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169128876791095300140835877 31711664398330368776406727)
      ·
        refine ⟨47567496597495553164610091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31711664398330368776406727 47567496597495553164610091)
        ·
          refine ⟨71351244896243329746915137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47567496597495553164610091 71351244896243329746915137)
          ·
            refine ⟨53513433672182497310186353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71351244896243329746915137 53513433672182497310186353)
            ·
              refine ⟨40135075254136872982639765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53513433672182497310186353 40135075254136872982639765)
              ·
                refine ⟨1881331652537665921061239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40135075254136872982639765 1881331652537665921061239)
                ·
                  refine ⟨2821997478806498881591859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881331652537665921061239 2821997478806498881591859)
                  ·
                    refine ⟨4232996218209748322387789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2821997478806498881591859 4232996218209748322387789)
                    ·
                      refine ⟨1587373581828655620895421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4232996218209748322387789 1587373581828655620895421)
                      ·
                        rfl

theorem cell23_3091399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_3091399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091399 prefixEnd_3091399 := by exact prefixLift 3091399
  have htrace : WordTrace (prefixWord ++ tailWord_3091399) baseStart_3091399 baseEnd_3091399 := by
    simpa [prefixWord, tailWord_3091399, baseEnd_3091399] using wordTrace_append hprefix tailTrace_3091399
  have hstable : (prefixWord ++ tailWord_3091399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091399).length < 2 ^ (prefixWord ++ tailWord_3091399).sum := by decide
  have hdescent : baseEnd_3091399 < baseStart_3091399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091415 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 6, 4]
def baseStart_3091415 : Nat := 118140960795 + 3091415 * 2 ^ 59
def prefixEnd_3091415 : Nat := 4983230072969 + 3 ^ 40 * 3091415 * 2
def baseEnd_3091415 : Nat := 529127265839709186098449

theorem tailTrace_3091415 : CollatzResearch.WordTrace tailWord_3091415 prefixEnd_3091415 529127265839709186098449 := by
  unfold tailWord_3091415
  simp only [CollatzResearch.WordTrace]
  refine ⟨112753168095338901493139699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75168778730225934328759799 112753168095338901493139699)
  ·
    refine ⟨169129752143008352239709549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112753168095338901493139699 169129752143008352239709549)
    ·
      refine ⟨63423657053628132089891081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169129752143008352239709549 63423657053628132089891081)
      ·
        refine ⟨47567742790221099067418311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63423657053628132089891081 47567742790221099067418311)
        ·
          refine ⟨71351614185331648601127467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47567742790221099067418311 71351614185331648601127467)
          ·
            refine ⟨107027421277997472901691201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71351614185331648601127467 107027421277997472901691201)
            ·
              refine ⟨80270565958498104676268401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107027421277997472901691201 80270565958498104676268401)
              ·
                refine ⟨60202924468873578507201301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80270565958498104676268401 60202924468873578507201301)
                ·
                  refine ⟨2822012084478448992525061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60202924468873578507201301 2822012084478448992525061)
                  ·
                    refine ⟨529127265839709186098449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2822012084478448992525061 529127265839709186098449)
                    ·
                      rfl

theorem cell23_3091415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_3091415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091415 prefixEnd_3091415 := by exact prefixLift 3091415
  have htrace : WordTrace (prefixWord ++ tailWord_3091415) baseStart_3091415 baseEnd_3091415 := by
    simpa [prefixWord, tailWord_3091415, baseEnd_3091415] using wordTrace_append hprefix tailTrace_3091415
  have hstable : (prefixWord ++ tailWord_3091415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091415).length < 2 ^ (prefixWord ++ tailWord_3091415).sum := by decide
  have hdescent : baseEnd_3091415 < baseStart_3091415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091426 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_3091426 : Nat := 118140960795 + 3091426 * 2 ^ 59
def prefixEnd_3091426 : Nat := 4983230072969 + 3 ^ 40 * 3091426 * 2
def baseEnd_3091426 : Nat := 1587387445806327015257797

theorem tailTrace_3091426 : CollatzResearch.WordTrace tailWord_3091426 prefixEnd_3091426 1587387445806327015257797 := by
  unfold tailWord_3091426
  simp only [CollatzResearch.WordTrace]
  refine ⟨28188392324574762592947533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75169046198866033581193421 28188392324574762592947533)
  ·
    refine ⟨10570647121715535972355325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28188392324574762592947533 10570647121715535972355325)
    ·
      refine ⟨3963992670643325989633247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10570647121715535972355325 3963992670643325989633247)
      ·
        refine ⟨5945989005964988984449871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3963992670643325989633247 5945989005964988984449871)
        ·
          refine ⟨8918983508947483476674807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5945989005964988984449871 8918983508947483476674807)
          ·
            refine ⟨13378475263421225215012211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8918983508947483476674807 13378475263421225215012211)
            ·
              refine ⟨20067712895131837822518317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13378475263421225215012211 20067712895131837822518317)
              ·
                refine ⟨7525392335674439183444369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20067712895131837822518317 7525392335674439183444369)
                ·
                  refine ⟨5644044251755829387583277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7525392335674439183444369 5644044251755829387583277)
                  ·
                    refine ⟨2116516594408436020343729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5644044251755829387583277 2116516594408436020343729)
                    ·
                      refine ⟨1587387445806327015257797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2116516594408436020343729 1587387445806327015257797)
                      ·
                        rfl

theorem cell23_3091426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_3091426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091426 prefixEnd_3091426 := by exact prefixLift 3091426
  have htrace : WordTrace (prefixWord ++ tailWord_3091426) baseStart_3091426 baseEnd_3091426 := by
    simpa [prefixWord, tailWord_3091426, baseEnd_3091426] using wordTrace_append hprefix tailTrace_3091426
  have hstable : (prefixWord ++ tailWord_3091426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091426).length < 2 ^ (prefixWord ++ tailWord_3091426).sum := by decide
  have hdescent : baseEnd_3091426 < baseStart_3091426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091439 : List Nat := [1, 1, 2, 1, 4, 4, 3, 1, 1, 1, 4]
def baseStart_3091439 : Nat := 118140960795 + 3091439 * 2 ^ 59
def prefixEnd_3091439 : Nat := 4983230072969 + 3 ^ 40 * 3091439 * 2
def baseEnd_3091439 : Nat := 1587394121054835464395237

theorem tailTrace_3091439 : CollatzResearch.WordTrace tailWord_3091439 prefixEnd_3091439 1587394121054835464395237 := by
  unfold tailWord_3091439
  simp only [CollatzResearch.WordTrace]
  refine ⟨112754043447251953592013371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75169362298167969061342247 112754043447251953592013371)
  ·
    refine ⟨169131065170877930388020057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112754043447251953592013371 169131065170877930388020057)
    ·
      refine ⟨126848298878158447791015043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169131065170877930388020057 126848298878158447791015043)
      ·
        refine ⟨190272448317237671686522565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126848298878158447791015043 190272448317237671686522565)
        ·
          refine ⟨35676084059482063441222981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190272448317237671686522565 35676084059482063441222981)
          ·
            refine ⟨6689265761152886895229309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35676084059482063441222981 6689265761152886895229309)
            ·
              refine ⟨2508474660432332585710991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6689265761152886895229309 2508474660432332585710991)
              ·
                refine ⟨3762711990648498878566487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2508474660432332585710991 3762711990648498878566487)
                ·
                  refine ⟨5644067985972748317849731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762711990648498878566487 5644067985972748317849731)
                  ·
                    refine ⟨8466101978959122476774597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5644067985972748317849731 8466101978959122476774597)
                    ·
                      refine ⟨1587394121054835464395237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8466101978959122476774597 1587394121054835464395237)
                      ·
                        rfl

theorem cell23_3091439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 1, 1, 4].length) (baseStart_3091439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091439 prefixEnd_3091439 := by exact prefixLift 3091439
  have htrace : WordTrace (prefixWord ++ tailWord_3091439) baseStart_3091439 baseEnd_3091439 := by
    simpa [prefixWord, tailWord_3091439, baseEnd_3091439] using wordTrace_append hprefix tailTrace_3091439
  have hstable : (prefixWord ++ tailWord_3091439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091439).length < 2 ^ (prefixWord ++ tailWord_3091439).sum := by decide
  have hdescent : baseEnd_3091439 < baseStart_3091439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091444 : List Nat := [2, 6, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3091444 : Nat := 118140960795 + 3091444 * 2 ^ 59
def prefixEnd_3091444 : Nat := 4983230072969 + 3 ^ 40 * 3091444 * 2
def baseEnd_3091444 : Nat := 529132229486035981610905

theorem tailTrace_3091444 : CollatzResearch.WordTrace tailWord_3091444 prefixEnd_3091444 529132229486035981610905 := by
  unfold tailWord_3091444
  simp only [CollatzResearch.WordTrace]
  refine ⟨56377112906116919722972693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75169483874822559630630257 56377112906116919722972693)
  ·
    refine ⟨2642677167474230612014345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56377112906116919722972693 2642677167474230612014345)
    ·
      refine ⟨1982007875605672959010759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2642677167474230612014345 1982007875605672959010759)
      ·
        refine ⟨2973011813408509438516139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982007875605672959010759 2973011813408509438516139)
        ·
          refine ⟨4459517720112764157774209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2973011813408509438516139 4459517720112764157774209)
          ·
            refine ⟨3344638290084573118330657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4459517720112764157774209 3344638290084573118330657)
            ·
              refine ⟨2508478717563429838747993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3344638290084573118330657 2508478717563429838747993)
              ·
                refine ⟨1881359038172572379060995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2508478717563429838747993 1881359038172572379060995)
                ·
                  refine ⟨2822038557258858568591493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881359038172572379060995 2822038557258858568591493)
                  ·
                    refine ⟨529132229486035981610905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2822038557258858568591493 529132229486035981610905)
                    ·
                      rfl

theorem cell23_3091444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3091444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091444 prefixEnd_3091444 := by exact prefixLift 3091444
  have htrace : WordTrace (prefixWord ++ tailWord_3091444) baseStart_3091444 baseEnd_3091444 := by
    simpa [prefixWord, tailWord_3091444, baseEnd_3091444] using wordTrace_append hprefix tailTrace_3091444
  have hstable : (prefixWord ++ tailWord_3091444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091444).length < 2 ^ (prefixWord ++ tailWord_3091444).sum := by decide
  have hdescent : baseEnd_3091444 < baseStart_3091444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091499 : List Nat := [1, 1, 1, 1, 2, 1, 7, 3, 1, 3, 2]
def baseStart_3091499 : Nat := 118140960795 + 3091499 * 2 ^ 59
def prefixEnd_3091499 : Nat := 4983230072969 + 3 ^ 40 * 3091499 * 2
def baseEnd_3091499 : Nat := 1587424929894105229644961

theorem tailTrace_3091499 : CollatzResearch.WordTrace tailWord_3091499 prefixEnd_3091499 1587424929894105229644961 := by
  unfold tailWord_3091499
  simp only [CollatzResearch.WordTrace]
  refine ⟨112756231827034583839197551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75170821218023055892798367 112756231827034583839197551)
  ·
    refine ⟨169134347740551875758796327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112756231827034583839197551 169134347740551875758796327)
    ·
      refine ⟨253701521610827813638194491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169134347740551875758796327 253701521610827813638194491)
      ·
        refine ⟨380552282416241720457291737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253701521610827813638194491 380552282416241720457291737)
        ·
          refine ⟨285414211812181290342968803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380552282416241720457291737 285414211812181290342968803)
          ·
            refine ⟨428121317718271935514453205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285414211812181290342968803 428121317718271935514453205)
            ·
              refine ⟨10034093384021998488619997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 428121317718271935514453205 10034093384021998488619997)
              ·
                refine ⟨3762785019008249433232499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10034093384021998488619997 3762785019008249433232499)
                ·
                  refine ⟨5644177528512374149848749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762785019008249433232499 5644177528512374149848749)
                  ·
                    refine ⟨2116566573192140306193281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5644177528512374149848749 2116566573192140306193281)
                    ·
                      refine ⟨1587424929894105229644961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2116566573192140306193281 1587424929894105229644961)
                      ·
                        rfl

theorem cell23_3091499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 3, 2].length) (baseStart_3091499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091499 prefixEnd_3091499 := by exact prefixLift 3091499
  have htrace : WordTrace (prefixWord ++ tailWord_3091499) baseStart_3091499 baseEnd_3091499 := by
    simpa [prefixWord, tailWord_3091499, baseEnd_3091499] using wordTrace_append hprefix tailTrace_3091499
  have hstable : (prefixWord ++ tailWord_3091499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091499).length < 2 ^ (prefixWord ++ tailWord_3091499).sum := by decide
  have hdescent : baseEnd_3091499 < baseStart_3091499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091505 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 4, 6]
def baseStart_3091505 : Nat := 118140960795 + 3091505 * 2 ^ 59
def prefixEnd_3091505 : Nat := 4983230072969 + 3 ^ 40 * 3091505 * 2
def baseEnd_3091505 : Nat := 529142670259344068723311

theorem tailTrace_3091505 : CollatzResearch.WordTrace tailWord_3091505 prefixEnd_3091505 529142670259344068723311 := by
  unfold tailWord_3091505
  simp only [CollatzResearch.WordTrace]
  refine ⟨112756450665012846863915969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75170967110008564575943979 112756450665012846863915969)
  ·
    refine ⟨84567337998759635147936977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112756450665012846863915969 84567337998759635147936977)
    ·
      refine ⟨63425503499069726360952733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84567337998759635147936977 63425503499069726360952733)
      ·
        refine ⟨23784563812151147385357275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63425503499069726360952733 23784563812151147385357275)
        ·
          refine ⟨35676845718226721078035913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23784563812151147385357275 35676845718226721078035913)
          ·
            refine ⟨26757634288670040808526935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35676845718226721078035913 26757634288670040808526935)
            ·
              refine ⟨40136451433005061212790403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26757634288670040808526935 40136451433005061212790403)
              ·
                refine ⟨60204677149507591819185605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40136451433005061212790403 60204677149507591819185605)
                ·
                  refine ⟨11288376965532673466097301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60204677149507591819185605 11288376965532673466097301)
                  ·
                    refine ⟨529142670259344068723311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11288376965532673466097301 529142670259344068723311)
                    ·
                      rfl

theorem cell23_3091505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_3091505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091505 prefixEnd_3091505 := by exact prefixLift 3091505
  have htrace : WordTrace (prefixWord ++ tailWord_3091505) baseStart_3091505 baseEnd_3091505 := by
    simpa [prefixWord, tailWord_3091505, baseEnd_3091505] using wordTrace_append hprefix tailTrace_3091505
  have hstable : (prefixWord ++ tailWord_3091505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091505).length < 2 ^ (prefixWord ++ tailWord_3091505).sum := by decide
  have hdescent : baseEnd_3091505 < baseStart_3091505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091533 : List Nat := [1, 6, 1, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_3091533 : Nat := 118140960795 + 3091533 * 2 ^ 59
def prefixEnd_3091533 : Nat := 4983230072969 + 3 ^ 40 * 3091533 * 2
def baseEnd_3091533 : Nat := 1587442388236358096619805

theorem tailTrace_3091533 : CollatzResearch.WordTrace tailWord_3091533 prefixEnd_3091533 1587442388236358096619805 := by
  unfold tailWord_3091533
  simp only [CollatzResearch.WordTrace]
  refine ⟨112757471908911407645935253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75171647939274271763956835 112757471908911407645935253)
  ·
    refine ⟨5285506495730222233403215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 112757471908911407645935253 5285506495730222233403215)
    ·
      refine ⟨7928259743595333350104823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5285506495730222233403215 7928259743595333350104823)
      ·
        refine ⟨11892389615393000025157235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7928259743595333350104823 11892389615393000025157235)
        ·
          refine ⟨17838584423089500037735853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11892389615393000025157235 17838584423089500037735853)
          ·
            refine ⟨6689469158658562514150945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17838584423089500037735853 6689469158658562514150945)
            ·
              refine ⟨5017101868993921885613209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6689469158658562514150945 5017101868993921885613209)
              ·
                refine ⟨3762826401745441414209907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5017101868993921885613209 3762826401745441414209907)
                ·
                  refine ⟨5644239602618162121314861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762826401745441414209907 5644239602618162121314861)
                  ·
                    refine ⟨2116589850981810795493073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5644239602618162121314861 2116589850981810795493073)
                    ·
                      refine ⟨1587442388236358096619805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2116589850981810795493073 1587442388236358096619805)
                      ·
                        rfl

theorem cell23_3091533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_3091533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091533 prefixEnd_3091533 := by exact prefixLift 3091533
  have htrace : WordTrace (prefixWord ++ tailWord_3091533) baseStart_3091533 baseEnd_3091533 := by
    simpa [prefixWord, tailWord_3091533, baseEnd_3091533] using wordTrace_append hprefix tailTrace_3091533
  have hstable : (prefixWord ++ tailWord_3091533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091533).length < 2 ^ (prefixWord ++ tailWord_3091533).sum := by decide
  have hdescent : baseEnd_3091533 < baseStart_3091533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091550 : List Nat := [4, 4, 1, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_3091550 : Nat := 118140960795 + 3091550 * 2 ^ 59
def prefixEnd_3091550 : Nat := 4983230072969 + 3 ^ 40 * 3091550 * 2
def baseEnd_3091550 : Nat := 1587451117407484530107227

theorem tailTrace_3091550 : CollatzResearch.WordTrace tailWord_3091550 prefixEnd_3091550 1587451117407484530107227 := by
  unfold tailWord_3091550
  simp only [CollatzResearch.WordTrace]
  refine ⟨14094761493731227443663013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75172061299899879699536069 14094761493731227443663013)
  ·
    refine ⟨2642767780074605145686815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14094761493731227443663013 2642767780074605145686815)
    ·
      refine ⟨3964151670111907718530223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2642767780074605145686815 3964151670111907718530223)
      ·
        refine ⟨5946227505167861577795335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3964151670111907718530223 5946227505167861577795335)
        ·
          refine ⟨8919341257751792366693003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5946227505167861577795335 8919341257751792366693003)
          ·
            refine ⟨13379011886627688550039505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8919341257751792366693003 13379011886627688550039505)
            ·
              refine ⟨10034258914970766412529629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13379011886627688550039505 10034258914970766412529629)
              ·
                refine ⟨3762847093114037404698611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10034258914970766412529629 3762847093114037404698611)
                ·
                  refine ⟨5644270639671056107047917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762847093114037404698611 5644270639671056107047917)
                  ·
                    refine ⟨2116601489876646040142969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5644270639671056107047917 2116601489876646040142969)
                    ·
                      refine ⟨1587451117407484530107227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2116601489876646040142969 1587451117407484530107227)
                      ·
                        rfl

theorem cell23_3091550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_3091550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091550 prefixEnd_3091550 := by exact prefixLift 3091550
  have htrace : WordTrace (prefixWord ++ tailWord_3091550) baseStart_3091550 baseEnd_3091550 := by
    simpa [prefixWord, tailWord_3091550, baseEnd_3091550] using wordTrace_append hprefix tailTrace_3091550
  have hstable : (prefixWord ++ tailWord_3091550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091550).length < 2 ^ (prefixWord ++ tailWord_3091550).sum := by decide
  have hdescent : baseEnd_3091550 < baseStart_3091550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091595 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 2, 8]
def baseStart_3091595 : Nat := 118140960795 + 3091595 * 2 ^ 59
def prefixEnd_3091595 : Nat := 4983230072969 + 3 ^ 40 * 3091595 * 2
def baseEnd_3091595 : Nat := 529158074678978951348173

theorem tailTrace_3091595 : CollatzResearch.WordTrace tailWord_3091595 prefixEnd_3091595 529158074678978951348173 := by
  unfold tailWord_3091595
  simp only [CollatzResearch.WordTrace]
  refine ⟨112759733234686792234692239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75173155489791194823128159 112759733234686792234692239)
  ·
    refine ⟨169139599852030188352038359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112759733234686792234692239 169139599852030188352038359)
    ·
      refine ⟨253709399778045282528057539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169139599852030188352038359 253709399778045282528057539)
      ·
        refine ⟨380564099667067923792086309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253709399778045282528057539 380564099667067923792086309)
        ·
          refine ⟨71355768687575235711016183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 380564099667067923792086309 71355768687575235711016183)
          ·
            refine ⟨107033653031362853566524275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71355768687575235711016183 107033653031362853566524275)
            ·
              refine ⟨160550479547044280349786413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107033653031362853566524275 160550479547044280349786413)
              ·
                refine ⟨60206429830141605131169905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160550479547044280349786413 60206429830141605131169905)
                ·
                  refine ⟨45154822372606203848377429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60206429830141605131169905 45154822372606203848377429)
                  ·
                    refine ⟨529158074678978951348173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45154822372606203848377429 529158074678978951348173)
                    ·
                      rfl

theorem cell23_3091595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 8].length) (baseStart_3091595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091595 prefixEnd_3091595 := by exact prefixLift 3091595
  have htrace : WordTrace (prefixWord ++ tailWord_3091595) baseStart_3091595 baseEnd_3091595 := by
    simpa [prefixWord, tailWord_3091595, baseEnd_3091595] using wordTrace_append hprefix tailTrace_3091595
  have hstable : (prefixWord ++ tailWord_3091595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091595).length < 2 ^ (prefixWord ++ tailWord_3091595).sum := by decide
  have hdescent : baseEnd_3091595 < baseStart_3091595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091646 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_3091646 : Nat := 118140960795 + 3091646 * 2 ^ 59
def prefixEnd_3091646 : Nat := 4983230072969 + 3 ^ 40 * 3091646 * 2
def baseEnd_3091646 : Nat := 529166803850105384835595

theorem tailTrace_3091646 : CollatzResearch.WordTrace tailWord_3091646 prefixEnd_3091646 529166803850105384835595 := by
  unfold tailWord_3091646
  simp only [CollatzResearch.WordTrace]
  refine ⟨14095199169687753493099849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75174395571668018629865861 14095199169687753493099849)
  ·
    refine ⟨10571399377265815119824887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14095199169687753493099849 10571399377265815119824887)
    ·
      refine ⟨15857099065898722679737331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10571399377265815119824887 15857099065898722679737331)
      ·
        refine ⟨23785648598848084019605997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15857099065898722679737331 23785648598848084019605997)
        ·
          refine ⟨8919618224568031507352249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23785648598848084019605997 8919618224568031507352249)
          ·
            refine ⟨6689713668426023630514187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8919618224568031507352249 6689713668426023630514187)
            ·
              refine ⟨10034570502639035445771281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689713668426023630514187 10034570502639035445771281)
              ·
                refine ⟨7525927876979276584328461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10034570502639035445771281 7525927876979276584328461)
                ·
                  refine ⟨2822222953867228719123173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7525927876979276584328461 2822222953867228719123173)
                  ·
                    refine ⟨529166803850105384835595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2822222953867228719123173 529166803850105384835595)
                    ·
                      rfl

theorem cell23_3091646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_3091646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091646 prefixEnd_3091646 := by exact prefixLift 3091646
  have htrace : WordTrace (prefixWord ++ tailWord_3091646) baseStart_3091646 baseEnd_3091646 := by
    simpa [prefixWord, tailWord_3091646, baseEnd_3091646] using wordTrace_append hprefix tailTrace_3091646
  have hstable : (prefixWord ++ tailWord_3091646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091646).length < 2 ^ (prefixWord ++ tailWord_3091646).sum := by decide
  have hdescent : baseEnd_3091646 < baseStart_3091646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091650 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_3091650 : Nat := 118140960795 + 3091650 * 2 ^ 59
def prefixEnd_3091650 : Nat := 4983230072969 + 3 ^ 40 * 3091650 * 2
def baseEnd_3091650 : Nat := 529167488490978046285589

theorem tailTrace_3091650 : CollatzResearch.WordTrace tailWord_3091650 prefixEnd_3091650 529167488490978046285589 := by
  unfold tailWord_3091650
  simp only [CollatzResearch.WordTrace]
  refine ⟨28190434812371884156986101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75174492832991691085296269 28190434812371884156986101)
  ·
    refine ⟨2642853263659864139717447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28190434812371884156986101 2642853263659864139717447)
    ·
      refine ⟨3964279895489796209576171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2642853263659864139717447 3964279895489796209576171)
      ·
        refine ⟨5946419843234694314364257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3964279895489796209576171 5946419843234694314364257)
        ·
          refine ⟨4459814882426020735773193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5946419843234694314364257 4459814882426020735773193)
          ·
            refine ⟨3344861161819515551829895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4459814882426020735773193 3344861161819515551829895)
            ·
              refine ⟨5017291742729273327744843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3344861161819515551829895 5017291742729273327744843)
              ·
                refine ⟨7525937614093909991617265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5017291742729273327744843 7525937614093909991617265)
                ·
                  refine ⟨5644453210570432493712949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7525937614093909991617265 5644453210570432493712949)
                  ·
                    refine ⟨529167488490978046285589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5644453210570432493712949 529167488490978046285589)
                    ·
                      rfl

theorem cell23_3091650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_3091650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091650 prefixEnd_3091650 := by exact prefixLift 3091650
  have htrace : WordTrace (prefixWord ++ tailWord_3091650) baseStart_3091650 baseEnd_3091650 := by
    simpa [prefixWord, tailWord_3091650, baseEnd_3091650] using wordTrace_append hprefix tailTrace_3091650
  have hstable : (prefixWord ++ tailWord_3091650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091650).length < 2 ^ (prefixWord ++ tailWord_3091650).sum := by decide
  have hdescent : baseEnd_3091650 < baseStart_3091650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091712 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 5]
def baseStart_3091712 : Nat := 118140960795 + 3091712 * 2 ^ 59
def prefixEnd_3091712 : Nat := 4983230072969 + 3 ^ 40 * 3091712 * 2
def baseEnd_3091712 : Nat := 1587534301273512896281481

theorem tailTrace_3091712 : CollatzResearch.WordTrace tailWord_3091712 prefixEnd_3091712 1587534301273512896281481 := by
  unfold tailWord_3091712
  simp only [CollatzResearch.WordTrace]
  refine ⟨56382000287631460608350695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75176000383508614144467593 56382000287631460608350695)
  ·
    refine ⟨84573000431447190912526043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56382000287631460608350695 84573000431447190912526043)
    ·
      refine ⟨126859500647170786368789065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84573000431447190912526043 126859500647170786368789065)
      ·
        refine ⟨95144625485378089776591799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126859500647170786368789065 95144625485378089776591799)
        ·
          refine ⟨142716938228067134664887699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95144625485378089776591799 142716938228067134664887699)
          ·
            refine ⟨214075407342100701997331549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142716938228067134664887699 214075407342100701997331549)
            ·
              refine ⟨80278277753287763248999331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214075407342100701997331549 80278277753287763248999331)
              ·
                refine ⟨120417416629931644873498997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80278277753287763248999331 120417416629931644873498997)
                ·
                  refine ⟨11289132809056091706890531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120417416629931644873498997 11289132809056091706890531)
                  ·
                    refine ⟨16933699213584137560335797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11289132809056091706890531 16933699213584137560335797)
                    ·
                      refine ⟨1587534301273512896281481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16933699213584137560335797 1587534301273512896281481)
                      ·
                        rfl

theorem cell23_3091712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_3091712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091712 prefixEnd_3091712 := by exact prefixLift 3091712
  have htrace : WordTrace (prefixWord ++ tailWord_3091712) baseStart_3091712 baseEnd_3091712 := by
    simpa [prefixWord, tailWord_3091712, baseEnd_3091712] using wordTrace_append hprefix tailTrace_3091712
  have hstable : (prefixWord ++ tailWord_3091712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091712).length < 2 ^ (prefixWord ++ tailWord_3091712).sum := by decide
  have hdescent : baseEnd_3091712 < baseStart_3091712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091726 : List Nat := [4, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4]
def baseStart_3091726 : Nat := 118140960795 + 3091726 * 2 ^ 59
def prefixEnd_3091726 : Nat := 4983230072969 + 3 ^ 40 * 3091726 * 2
def baseEnd_3091726 : Nat := 1587541490002675841506417

theorem tailTrace_3091726 : CollatzResearch.WordTrace tailWord_3091726 prefixEnd_3091726 1587541490002675841506417 := by
  unfold tailWord_3091726
  simp only [CollatzResearch.WordTrace]
  refine ⟨14095563899651525200963879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75176340798141467738474021 14095563899651525200963879)
  ·
    refine ⟨21143345849477287801445819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14095563899651525200963879 21143345849477287801445819)
    ·
      refine ⟨31715018774215931702168729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21143345849477287801445819 31715018774215931702168729)
      ·
        refine ⟨23786264080661948776626547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31715018774215931702168729 23786264080661948776626547)
        ·
          refine ⟨35679396120992923164939821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23786264080661948776626547 35679396120992923164939821)
          ·
            refine ⟨13379773545372346186852433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35679396120992923164939821 13379773545372346186852433)
            ·
              refine ⟨10034830159029259640139325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13379773545372346186852433 10034830159029259640139325)
              ·
                refine ⟨3763061309635972365052247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10034830159029259640139325 3763061309635972365052247)
                ·
                  refine ⟨5644591964453958547578371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3763061309635972365052247 5644591964453958547578371)
                  ·
                    refine ⟨8466887946680937821367557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5644591964453958547578371 8466887946680937821367557)
                    ·
                      refine ⟨1587541490002675841506417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8466887946680937821367557 1587541490002675841506417)
                      ·
                        rfl

theorem cell23_3091726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_3091726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091726 prefixEnd_3091726 := by exact prefixLift 3091726
  have htrace : WordTrace (prefixWord ++ tailWord_3091726) baseStart_3091726 baseEnd_3091726 := by
    simpa [prefixWord, tailWord_3091726, baseEnd_3091726] using wordTrace_append hprefix tailTrace_3091726
  have hstable : (prefixWord ++ tailWord_3091726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091726).length < 2 ^ (prefixWord ++ tailWord_3091726).sum := by decide
  have hdescent : baseEnd_3091726 < baseStart_3091726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091729 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 5]
def baseStart_3091729 : Nat := 118140960795 + 3091729 * 2 ^ 59
def prefixEnd_3091729 : Nat := 4983230072969 + 3 ^ 40 * 3091729 * 2
def baseEnd_3091729 : Nat := 1587543030444639329768903

theorem tailTrace_3091729 : CollatzResearch.WordTrace tailWord_3091729 prefixEnd_3091729 1587543030444639329768903 := by
  unfold tailWord_3091729
  simp only [CollatzResearch.WordTrace]
  refine ⟨112764620616201333120070241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75176413744134222080046827 112764620616201333120070241)
  ·
    refine ⟨84573465462150999840052681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112764620616201333120070241 84573465462150999840052681)
    ·
      refine ⟨63430099096613249880039511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84573465462150999840052681 63430099096613249880039511)
      ·
        refine ⟨95145148644919874820059267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63430099096613249880039511 95145148644919874820059267)
        ·
          refine ⟨142717722967379812230088901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95145148644919874820059267 142717722967379812230088901)
          ·
            refine ⟨26759573056383714793141669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142717722967379812230088901 26759573056383714793141669)
            ·
              refine ⟨5017419948071946523714063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26759573056383714793141669 5017419948071946523714063)
              ·
                refine ⟨7526129922107919785571095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5017419948071946523714063 7526129922107919785571095)
                ·
                  refine ⟨11289194883161879678356643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7526129922107919785571095 11289194883161879678356643)
                  ·
                    refine ⟨16933792324742819517534965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11289194883161879678356643 16933792324742819517534965)
                    ·
                      refine ⟨1587543030444639329768903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16933792324742819517534965 1587543030444639329768903)
                      ·
                        rfl

theorem cell23_3091729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_3091729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091729 prefixEnd_3091729 := by exact prefixLift 3091729
  have htrace : WordTrace (prefixWord ++ tailWord_3091729) baseStart_3091729 baseEnd_3091729 := by
    simpa [prefixWord, tailWord_3091729, baseEnd_3091729] using wordTrace_append hprefix tailTrace_3091729
  have hstable : (prefixWord ++ tailWord_3091729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091729).length < 2 ^ (prefixWord ++ tailWord_3091729).sum := by decide
  have hdescent : baseEnd_3091729 < baseStart_3091729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091749 : List Nat := [1, 3, 1, 2, 4, 2, 2, 8]
def baseStart_3091749 : Nat := 118140960795 + 3091749 * 2 ^ 59
def prefixEnd_3091749 : Nat := 4983230072969 + 3 ^ 40 * 3091749 * 2
def baseEnd_3091749 : Nat := 58798270372508490796993

theorem tailTrace_3091749 : CollatzResearch.WordTrace tailWord_3091749 prefixEnd_3091749 58798270372508490796993 := by
  unfold tailWord_3091749
  simp only [CollatzResearch.WordTrace]
  refine ⟨112765350076128876535798301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75176900050752584357198867 112765350076128876535798301)
  ·
    refine ⟨42287006278548328700924363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112765350076128876535798301 42287006278548328700924363)
    ·
      refine ⟨63430509417822493051386545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42287006278548328700924363 63430509417822493051386545)
      ·
        refine ⟨47572882063366869788539909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63430509417822493051386545 47572882063366869788539909)
        ·
          refine ⟨8919915386881288085351233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47572882063366869788539909 8919915386881288085351233)
          ·
            refine ⟨6689936540160966064013425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8919915386881288085351233 6689936540160966064013425)
            ·
              refine ⟨5017452405120724548010069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6689936540160966064013425 5017452405120724548010069)
              ·
                refine ⟨58798270372508490796993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5017452405120724548010069 58798270372508490796993)
                ·
                  rfl

theorem cell23_3091749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 8].length) (baseStart_3091749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091749 prefixEnd_3091749 := by exact prefixLift 3091749
  have htrace : WordTrace (prefixWord ++ tailWord_3091749) baseStart_3091749 baseEnd_3091749 := by
    simpa [prefixWord, tailWord_3091749, baseEnd_3091749] using wordTrace_append hprefix tailTrace_3091749
  have hstable : (prefixWord ++ tailWord_3091749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091749).length < 2 ^ (prefixWord ++ tailWord_3091749).sum := by decide
  have hdescent : baseEnd_3091749 < baseStart_3091749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091759 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 3]
def baseStart_3091759 : Nat := 118140960795 + 3091759 * 2 ^ 59
def prefixEnd_3091759 : Nat := 4983230072969 + 3 ^ 40 * 3091759 * 2
def baseEnd_3091759 : Nat := 1587558434864274212393765

theorem tailTrace_3091759 : CollatzResearch.WordTrace tailWord_3091759 prefixEnd_3091759 1587558434864274212393765 := by
  unfold tailWord_3091759
  simp only [CollatzResearch.WordTrace]
  refine ⟨112765714806092648243662331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75177143204061765495774887 112765714806092648243662331)
  ·
    refine ⟨169148572209138972365493497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112765714806092648243662331 169148572209138972365493497)
    ·
      refine ⟨126861429156854229274120123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169148572209138972365493497 126861429156854229274120123)
      ·
        refine ⟨190292143735281343911180185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126861429156854229274120123 190292143735281343911180185)
        ·
          refine ⟨142719107801461007933385139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190292143735281343911180185 142719107801461007933385139)
          ·
            refine ⟨214078661702191511900077709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142719107801461007933385139 214078661702191511900077709)
            ·
              refine ⟨80279498138321816962529141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214078661702191511900077709 80279498138321816962529141)
              ·
                refine ⟨7526202950467670340237107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80279498138321816962529141 7526202950467670340237107)
                ·
                  refine ⟨11289304425701505510355661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7526202950467670340237107 11289304425701505510355661)
                  ·
                    refine ⟨4233489159638064566383373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11289304425701505510355661 4233489159638064566383373)
                    ·
                      refine ⟨1587558434864274212393765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4233489159638064566383373 1587558434864274212393765)
                      ·
                        rfl

theorem cell23_3091759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 3].length) (baseStart_3091759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091759 prefixEnd_3091759 := by exact prefixLift 3091759
  have htrace : WordTrace (prefixWord ++ tailWord_3091759) baseStart_3091759 baseEnd_3091759 := by
    simpa [prefixWord, tailWord_3091759, baseEnd_3091759] using wordTrace_append hprefix tailTrace_3091759
  have hstable : (prefixWord ++ tailWord_3091759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091759).length < 2 ^ (prefixWord ++ tailWord_3091759).sum := by decide
  have hdescent : baseEnd_3091759 < baseStart_3091759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091763 : List Nat := [1, 1, 1, 2, 5, 4, 1, 2, 1, 2, 3]
def baseStart_3091763 : Nat := 118140960795 + 3091763 * 2 ^ 59
def prefixEnd_3091763 : Nat := 4983230072969 + 3 ^ 40 * 3091763 * 2
def baseEnd_3091763 : Nat := 1587560488786892196743747

theorem tailTrace_3091763 : CollatzResearch.WordTrace tailWord_3091763 prefixEnd_3091763 1587560488786892196743747 := by
  unfold tailWord_3091763
  simp only [CollatzResearch.WordTrace]
  refine ⟨112765860698078156926807943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75177240465385437951205295 112765860698078156926807943)
  ·
    refine ⟨169148791047117235390211915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112765860698078156926807943 169148791047117235390211915)
    ·
      refine ⟨253723186570675853085317873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169148791047117235390211915 253723186570675853085317873)
      ·
        refine ⟨190292389928006889813988405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253723186570675853085317873 190292389928006889813988405)
        ·
          refine ⟨17839911555750645920061413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190292389928006889813988405 17839911555750645920061413)
          ·
            refine ⟨3344983416703246110011515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17839911555750645920061413 3344983416703246110011515)
            ·
              refine ⟨5017475125054869165017273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3344983416703246110011515 5017475125054869165017273)
              ·
                refine ⟨3763106343791151873762955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5017475125054869165017273 3763106343791151873762955)
                ·
                  refine ⟨5644659515686727810644433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3763106343791151873762955 5644659515686727810644433)
                  ·
                    refine ⟨4233494636765045857983325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5644659515686727810644433 4233494636765045857983325)
                    ·
                      refine ⟨1587560488786892196743747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4233494636765045857983325 1587560488786892196743747)
                      ·
                        rfl

theorem cell23_3091763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 2, 3].length) (baseStart_3091763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091763 prefixEnd_3091763 := by exact prefixLift 3091763
  have htrace : WordTrace (prefixWord ++ tailWord_3091763) baseStart_3091763 baseEnd_3091763 := by
    simpa [prefixWord, tailWord_3091763, baseEnd_3091763] using wordTrace_append hprefix tailTrace_3091763
  have hstable : (prefixWord ++ tailWord_3091763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091763).length < 2 ^ (prefixWord ++ tailWord_3091763).sum := by decide
  have hdescent : baseEnd_3091763 < baseStart_3091763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091773 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3091773 : Nat := 118140960795 + 3091773 * 2 ^ 59
def prefixEnd_3091773 : Nat := 4983230072969 + 3 ^ 40 * 3091773 * 2
def baseEnd_3091773 : Nat := 1587565623593437157618701

theorem tailTrace_3091773 : CollatzResearch.WordTrace tailWord_3091773 prefixEnd_3091773 1587565623593437157618701 := by
  unfold tailWord_3091773
  simp only [CollatzResearch.WordTrace]
  refine ⟨112766225428041928634671973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75177483618694619089781315 112766225428041928634671973)
  ·
    refine ⟨21143667267757861619000995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112766225428041928634671973 21143667267757861619000995)
    ·
      refine ⟨31715500901636792428501493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21143667267757861619000995 31715500901636792428501493)
      ·
        refine ⟨2973328209528449290172015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31715500901636792428501493 2973328209528449290172015)
        ·
          refine ⟨4459992314292673935258023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2973328209528449290172015 4459992314292673935258023)
          ·
            refine ⟨6689988471439010902887035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4459992314292673935258023 6689988471439010902887035)
            ·
              refine ⟨10034982707158516354330553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689988471439010902887035 10034982707158516354330553)
              ·
                refine ⟨7526237030368887265747915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10034982707158516354330553 7526237030368887265747915)
                ·
                  refine ⟨11289355545553330898621873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7526237030368887265747915 11289355545553330898621873)
                  ·
                    refine ⟨8467016659164998173966405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11289355545553330898621873 8467016659164998173966405)
                    ·
                      refine ⟨1587565623593437157618701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8467016659164998173966405 1587565623593437157618701)
                      ·
                        rfl

theorem cell23_3091773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3091773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091773 prefixEnd_3091773 := by exact prefixLift 3091773
  have htrace : WordTrace (prefixWord ++ tailWord_3091773) baseStart_3091773 baseEnd_3091773 := by
    simpa [prefixWord, tailWord_3091773, baseEnd_3091773] using wordTrace_append hprefix tailTrace_3091773
  have hstable : (prefixWord ++ tailWord_3091773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091773).length < 2 ^ (prefixWord ++ tailWord_3091773).sum := by decide
  have hdescent : baseEnd_3091773 < baseStart_3091773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091793 : List Nat := [1, 2, 2, 1, 4, 1, 4, 2, 2, 1, 3]
def baseStart_3091793 : Nat := 118140960795 + 3091793 * 2 ^ 59
def prefixEnd_3091793 : Nat := 4983230072969 + 3 ^ 40 * 3091793 * 2
def baseEnd_3091793 : Nat := 1587575893206527079368609

theorem tailTrace_3091793 : CollatzResearch.WordTrace tailWord_3091793 prefixEnd_3091793 1587575893206527079368609 := by
  unfold tailWord_3091793
  simp only [CollatzResearch.WordTrace]
  refine ⟨112766954887969472050400033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75177969925312981366933355 112766954887969472050400033)
  ·
    refine ⟨84575216165977104037800025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112766954887969472050400033 84575216165977104037800025)
    ·
      refine ⟨63431412124482828028350019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84575216165977104037800025 63431412124482828028350019)
      ·
        refine ⟨95147118186724242042525029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63431412124482828028350019 95147118186724242042525029)
        ·
          refine ⟨17840084660010795382973443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95147118186724242042525029 17840084660010795382973443)
          ·
            refine ⟨26760126990016193074460165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17840084660010795382973443 26760126990016193074460165)
            ·
              refine ⟨5017523810628036201461281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26760126990016193074460165 5017523810628036201461281)
              ·
                refine ⟨3763142857971027151095961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5017523810628036201461281 3763142857971027151095961)
                ·
                  refine ⟨2822357143478270363321971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3763142857971027151095961 2822357143478270363321971)
                  ·
                    refine ⟨4233535715217405544982957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2822357143478270363321971 4233535715217405544982957)
                    ·
                      refine ⟨1587575893206527079368609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4233535715217405544982957 1587575893206527079368609)
                      ·
                        rfl

theorem cell23_3091793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_3091793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091793 prefixEnd_3091793 := by exact prefixLift 3091793
  have htrace : WordTrace (prefixWord ++ tailWord_3091793) baseStart_3091793 baseEnd_3091793 := by
    simpa [prefixWord, tailWord_3091793, baseEnd_3091793] using wordTrace_append hprefix tailTrace_3091793
  have hstable : (prefixWord ++ tailWord_3091793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091793).length < 2 ^ (prefixWord ++ tailWord_3091793).sum := by decide
  have hdescent : baseEnd_3091793 < baseStart_3091793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091799 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 4]
def baseStart_3091799 : Nat := 118140960795 + 3091799 * 2 ^ 59
def prefixEnd_3091799 : Nat := 4983230072969 + 3 ^ 40 * 3091799 * 2
def baseEnd_3091799 : Nat := 1587578974090454055893581

theorem tailTrace_3091799 : CollatzResearch.WordTrace tailWord_3091799 prefixEnd_3091799 1587578974090454055893581 := by
  unfold tailWord_3091799
  simp only [CollatzResearch.WordTrace]
  refine ⟨112767173725947735075118451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75178115817298490050078967 112767173725947735075118451)
  ·
    refine ⟨169150760588921602612677677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112767173725947735075118451 169150760588921602612677677)
    ·
      refine ⟨63431535220845600979754129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169150760588921602612677677 63431535220845600979754129)
      ·
        refine ⟨47573651415634200734815597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63431535220845600979754129 47573651415634200734815597)
        ·
          refine ⟨17840119280862825275555849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47573651415634200734815597 17840119280862825275555849)
          ·
            refine ⟨13380089460647118956666887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17840119280862825275555849 13380089460647118956666887)
            ·
              refine ⟨20070134190970678435000331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13380089460647118956666887 20070134190970678435000331)
              ·
                refine ⟨30105201286456017652500497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20070134190970678435000331 30105201286456017652500497)
                ·
                  refine ⟨22578900964842013239375373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30105201286456017652500497 22578900964842013239375373)
                  ·
                    refine ⟨8467087861815754964765765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22578900964842013239375373 8467087861815754964765765)
                    ·
                      refine ⟨1587578974090454055893581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8467087861815754964765765 1587578974090454055893581)
                      ·
                        rfl

theorem cell23_3091799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_3091799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091799 prefixEnd_3091799 := by exact prefixLift 3091799
  have htrace : WordTrace (prefixWord ++ tailWord_3091799) baseStart_3091799 baseEnd_3091799 := by
    simpa [prefixWord, tailWord_3091799, baseEnd_3091799] using wordTrace_append hprefix tailTrace_3091799
  have hstable : (prefixWord ++ tailWord_3091799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091799).length < 2 ^ (prefixWord ++ tailWord_3091799).sum := by decide
  have hdescent : baseEnd_3091799 < baseStart_3091799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091866 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3]
def baseStart_3091866 : Nat := 118140960795 + 3091866 * 2 ^ 59
def prefixEnd_3091866 : Nat := 4983230072969 + 3 ^ 40 * 3091866 * 2
def baseEnd_3091866 : Nat := 1587613377294305293755773

theorem tailTrace_3091866 : CollatzResearch.WordTrace tailWord_3091866 prefixEnd_3091866 1587613377294305293755773 := by
  unfold tailWord_3091866
  simp only [CollatzResearch.WordTrace]
  refine ⟨28192404354176251379451863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75179744944470003678538301 28192404354176251379451863)
  ·
    refine ⟨42288606531264377069177795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28192404354176251379451863 42288606531264377069177795)
    ·
      refine ⟨63432909796896565603766693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42288606531264377069177795 63432909796896565603766693)
      ·
        refine ⟨11893670586918106050706255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63432909796896565603766693 11893670586918106050706255)
        ·
          refine ⟨17840505880377159076059383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11893670586918106050706255 17840505880377159076059383)
          ·
            refine ⟨26760758820565738614089075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17840505880377159076059383 26760758820565738614089075)
            ·
              refine ⟨40141138230848607921133613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26760758820565738614089075 40141138230848607921133613)
              ·
                refine ⟨15052926836568227970425105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40141138230848607921133613 15052926836568227970425105)
                ·
                  refine ⟨11289695127426170977818829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15052926836568227970425105 11289695127426170977818829)
                  ·
                    refine ⟨4233635672784814116682061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11289695127426170977818829 4233635672784814116682061)
                    ·
                      refine ⟨1587613377294305293755773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4233635672784814116682061 1587613377294305293755773)
                      ·
                        rfl

theorem cell23_3091866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_3091866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091866 prefixEnd_3091866 := by exact prefixLift 3091866
  have htrace : WordTrace (prefixWord ++ tailWord_3091866) baseStart_3091866 baseEnd_3091866 := by
    simpa [prefixWord, tailWord_3091866, baseEnd_3091866] using wordTrace_append hprefix tailTrace_3091866
  have hstable : (prefixWord ++ tailWord_3091866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091866).length < 2 ^ (prefixWord ++ tailWord_3091866).sum := by decide
  have hdescent : baseEnd_3091866 < baseStart_3091866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091919 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 6]
def baseStart_3091919 : Nat := 118140960795 + 3091919 * 2 ^ 59
def prefixEnd_3091919 : Nat := 4983230072969 + 3 ^ 40 * 3091919 * 2
def baseEnd_3091919 : Nat := 1587640591768993586393029

theorem tailTrace_3091919 : CollatzResearch.WordTrace tailWord_3091919 prefixEnd_3091919 1587640591768993586393029 := by
  unfold tailWord_3091919
  simp only [CollatzResearch.WordTrace]
  refine ⟨112771550485512995569486811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75181033657008663712991207 112771550485512995569486811)
  ·
    refine ⟨169157325728269493354230217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112771550485512995569486811 169157325728269493354230217)
    ·
      refine ⟨126867994296202120015672663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169157325728269493354230217 126867994296202120015672663)
      ·
        refine ⟨190301991444303180023508995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126867994296202120015672663 190301991444303180023508995)
        ·
          refine ⟨285452987166454770035263493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190301991444303180023508995 285452987166454770035263493)
          ·
            refine ⟨53522435093710269381611905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285452987166454770035263493 53522435093710269381611905)
            ·
              refine ⟨40141826320282702036208929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53522435093710269381611905 40141826320282702036208929)
              ·
                refine ⟨30106369740212026527156697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40141826320282702036208929 30106369740212026527156697)
                ·
                  refine ⟨22579777305159019895367523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30106369740212026527156697 22579777305159019895367523)
                  ·
                    refine ⟨33869665957738529843051285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22579777305159019895367523 33869665957738529843051285)
                    ·
                      refine ⟨1587640591768993586393029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33869665957738529843051285 1587640591768993586393029)
                      ·
                        rfl

theorem cell23_3091919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_3091919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091919 prefixEnd_3091919 := by exact prefixLift 3091919
  have htrace : WordTrace (prefixWord ++ tailWord_3091919) baseStart_3091919 baseEnd_3091919 := by
    simpa [prefixWord, tailWord_3091919, baseEnd_3091919] using wordTrace_append hprefix tailTrace_3091919
  have hstable : (prefixWord ++ tailWord_3091919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091919).length < 2 ^ (prefixWord ++ tailWord_3091919).sum := by decide
  have hdescent : baseEnd_3091919 < baseStart_3091919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091943 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_3091943 : Nat := 118140960795 + 3091943 * 2 ^ 59
def prefixEnd_3091943 : Nat := 4983230072969 + 3 ^ 40 * 3091943 * 2
def baseEnd_3091943 : Nat := 1587652915304701492492919

theorem tailTrace_3091943 : CollatzResearch.WordTrace tailWord_3091943 prefixEnd_3091943 1587652915304701492492919 := by
  unfold tailWord_3091943
  simp only [CollatzResearch.WordTrace]
  refine ⟨112772425837426047668360483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75181617224950698445573655 112772425837426047668360483)
  ·
    refine ⟨169158638756139071502540725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112772425837426047668360483 169158638756139071502540725)
    ·
      refine ⟨15858622383388037953363193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169158638756139071502540725 15858622383388037953363193)
      ·
        refine ⟨11893966787541028465022395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15858622383388037953363193 11893966787541028465022395)
        ·
          refine ⟨17840950181311542697533593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11893966787541028465022395 17840950181311542697533593)
          ·
            refine ⟨13380712635983657023150195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17840950181311542697533593 13380712635983657023150195)
            ·
              refine ⟨20071068953975485534725293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13380712635983657023150195 20071068953975485534725293)
              ·
                refine ⟨7526650857740807075521985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20071068953975485534725293 7526650857740807075521985)
                ·
                  refine ⟨5644988143305605306641489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7526650857740807075521985 5644988143305605306641489)
                  ·
                    refine ⟨4233741107479203979981117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5644988143305605306641489 4233741107479203979981117)
                    ·
                      refine ⟨1587652915304701492492919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4233741107479203979981117 1587652915304701492492919)
                      ·
                        rfl

theorem cell23_3091943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_3091943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091943 prefixEnd_3091943 := by exact prefixLift 3091943
  have htrace : WordTrace (prefixWord ++ tailWord_3091943) baseStart_3091943 baseEnd_3091943 := by
    simpa [prefixWord, tailWord_3091943, baseEnd_3091943] using wordTrace_append hprefix tailTrace_3091943
  have hstable : (prefixWord ++ tailWord_3091943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091943).length < 2 ^ (prefixWord ++ tailWord_3091943).sum := by decide
  have hdescent : baseEnd_3091943 < baseStart_3091943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091950 : List Nat := [4, 1, 2, 1, 2, 1, 2, 5, 1, 4]
def baseStart_3091950 : Nat := 118140960795 + 3091950 * 2 ^ 59
def prefixEnd_3091950 : Nat := 4983230072969 + 3 ^ 40 * 3091950 * 2
def baseEnd_3091950 : Nat := 529218836556427655035129

theorem tailTrace_3091950 : CollatzResearch.WordTrace tailWord_3091950 prefixEnd_3091950 529218836556427655035129 := by
  unfold tailWord_3091950
  simp only [CollatzResearch.WordTrace]
  refine ⟨14096585143550085982983163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75181787432267125242576869 14096585143550085982983163)
  ·
    refine ⟨21144877715325128974474745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14096585143550085982983163 21144877715325128974474745)
    ·
      refine ⟨15858658286493846730856059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21144877715325128974474745 15858658286493846730856059)
      ·
        refine ⟨23787987429740770096284089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15858658286493846730856059 23787987429740770096284089)
        ·
          refine ⟨17840990572305577572213067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23787987429740770096284089 17840990572305577572213067)
          ·
            refine ⟨26761485858458366358319601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17840990572305577572213067 26761485858458366358319601)
            ·
              refine ⟨20071114393843774768739701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26761485858458366358319601 20071114393843774768739701)
              ·
                refine ⟨1881666974422853884569347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20071114393843774768739701 1881666974422853884569347)
                ·
                  refine ⟨2822500461634280826854021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881666974422853884569347 2822500461634280826854021)
                  ·
                    refine ⟨529218836556427655035129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2822500461634280826854021 529218836556427655035129)
                    ·
                      rfl

theorem cell23_3091950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_3091950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091950 prefixEnd_3091950 := by exact prefixLift 3091950
  have htrace : WordTrace (prefixWord ++ tailWord_3091950) baseStart_3091950 baseEnd_3091950 := by
    simpa [prefixWord, tailWord_3091950, baseEnd_3091950] using wordTrace_append hprefix tailTrace_3091950
  have hstable : (prefixWord ++ tailWord_3091950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091950).length < 2 ^ (prefixWord ++ tailWord_3091950).sum := by decide
  have hdescent : baseEnd_3091950 < baseStart_3091950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091973 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 3, 1, 3]
def baseStart_3091973 : Nat := 118140960795 + 3091973 * 2 ^ 59
def prefixEnd_3091973 : Nat := 4983230072969 + 3 ^ 40 * 3091973 * 2
def baseEnd_3091973 : Nat := 1587668319724336375117781

theorem tailTrace_3091973 : CollatzResearch.WordTrace tailWord_3091973 prefixEnd_3091973 1587668319724336375117781 := by
  unfold tailWord_3091973
  simp only [CollatzResearch.WordTrace]
  refine ⟨112773520027317362791952573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75182346684878241861301715 112773520027317362791952573)
  ·
    refine ⟨42290070010244011046982215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112773520027317362791952573 42290070010244011046982215)
    ·
      refine ⟨63435105015366016570473323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42290070010244011046982215 63435105015366016570473323)
      ·
        refine ⟨95152657523049024855709985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63435105015366016570473323 95152657523049024855709985)
        ·
          refine ⟨71364493142286768641782489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95152657523049024855709985 71364493142286768641782489)
          ·
            refine ⟨53523369856715076481336867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71364493142286768641782489 53523369856715076481336867)
            ·
              refine ⟨80285054785072614722005301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53523369856715076481336867 80285054785072614722005301)
              ·
                refine ⟨7526723886100557630187997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80285054785072614722005301 7526723886100557630187997)
                ·
                  refine ⟨2822521457287709111320499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7526723886100557630187997 2822521457287709111320499)
                  ·
                    refine ⟨4233782185931563666980749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2822521457287709111320499 4233782185931563666980749)
                    ·
                      refine ⟨1587668319724336375117781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4233782185931563666980749 1587668319724336375117781)
                      ·
                        rfl

theorem cell23_3091973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_3091973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091973 prefixEnd_3091973 := by exact prefixLift 3091973
  have htrace : WordTrace (prefixWord ++ tailWord_3091973) baseStart_3091973 baseEnd_3091973 := by
    simpa [prefixWord, tailWord_3091973, baseEnd_3091973] using wordTrace_append hprefix tailTrace_3091973
  have hstable : (prefixWord ++ tailWord_3091973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091973).length < 2 ^ (prefixWord ++ tailWord_3091973).sum := by decide
  have hdescent : baseEnd_3091973 < baseStart_3091973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091976 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 3, 5]
def baseStart_3091976 : Nat := 118140960795 + 3091976 * 2 ^ 59
def prefixEnd_3091976 : Nat := 4983230072969 + 3 ^ 40 * 3091976 * 2
def baseEnd_3091976 : Nat := 529223286722099954460089

theorem tailTrace_3091976 : CollatzResearch.WordTrace tailWord_3091976 prefixEnd_3091976 529223286722099954460089 := by
  unfold tailWord_3091976
  simp only [CollatzResearch.WordTrace]
  refine ⟨56386814723153247152155891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75182419630870996202874521 56386814723153247152155891)
  ·
    refine ⟨84580222084729870728233837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56386814723153247152155891 84580222084729870728233837)
    ·
      refine ⟨31717583281773701523087689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84580222084729870728233837 31717583281773701523087689)
      ·
        refine ⟨23788187461330276142315767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31717583281773701523087689 23788187461330276142315767)
        ·
          refine ⟨35682281191995414213473651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23788187461330276142315767 35682281191995414213473651)
          ·
            refine ⟨53523421787993121320210477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35682281191995414213473651 53523421787993121320210477)
            ·
              refine ⟨20071283170497420495078929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53523421787993121320210477 20071283170497420495078929)
              ·
                refine ⟨15053462377873065371309197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20071283170497420495078929 15053462377873065371309197)
                ·
                  refine ⟨5645048391702399514240949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15053462377873065371309197 5645048391702399514240949)
                  ·
                    refine ⟨529223286722099954460089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5645048391702399514240949 529223286722099954460089)
                    ·
                      rfl

theorem cell23_3091976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_3091976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3091976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3091976 prefixEnd_3091976 := by exact prefixLift 3091976
  have htrace : WordTrace (prefixWord ++ tailWord_3091976) baseStart_3091976 baseEnd_3091976 := by
    simpa [prefixWord, tailWord_3091976, baseEnd_3091976] using wordTrace_append hprefix tailTrace_3091976
  have hstable : (prefixWord ++ tailWord_3091976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091976).length < 2 ^ (prefixWord ++ tailWord_3091976).sum := by decide
  have hdescent : baseEnd_3091976 < baseStart_3091976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092000 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 1, 5, 2]
def baseStart_3092000 : Nat := 118140960795 + 3092000 * 2 ^ 59
def prefixEnd_3092000 : Nat := 4983230072969 + 3 ^ 40 * 3092000 * 2
def baseEnd_3092000 : Nat := 1587682183702007769480157

theorem tailTrace_3092000 : CollatzResearch.WordTrace tailWord_3092000 prefixEnd_3092000 1587682183702007769480157 := by
  unfold tailWord_3092000
  simp only [CollatzResearch.WordTrace]
  refine ⟨56387252399109773201592727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75183003198813030935456969 56387252399109773201592727)
  ·
    refine ⟨84580878598664659802389091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56387252399109773201592727 84580878598664659802389091)
    ·
      refine ⟨126871317897996989703583637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84580878598664659802389091 126871317897996989703583637)
      ·
        refine ⟨5947093026468608892355483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126871317897996989703583637 5947093026468608892355483)
        ·
          refine ⟨8920639539702913338533225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5947093026468608892355483 8920639539702913338533225)
          ·
            refine ⟨6690479654777185003899919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8920639539702913338533225 6690479654777185003899919)
            ·
              refine ⟨10035719482165777505849879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6690479654777185003899919 10035719482165777505849879)
              ·
                refine ⟨15053579223248666258774819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10035719482165777505849879 15053579223248666258774819)
                ·
                  refine ⟨22580368834872999388162229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15053579223248666258774819 22580368834872999388162229)
                  ·
                    refine ⟨2116909578269343692640209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22580368834872999388162229 2116909578269343692640209)
                    ·
                      refine ⟨1587682183702007769480157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2116909578269343692640209 1587682183702007769480157)
                      ·
                        rfl

theorem cell23_3092000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_3092000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092000 prefixEnd_3092000 := by exact prefixLift 3092000
  have htrace : WordTrace (prefixWord ++ tailWord_3092000) baseStart_3092000 baseEnd_3092000 := by
    simpa [prefixWord, tailWord_3092000, baseEnd_3092000] using wordTrace_append hprefix tailTrace_3092000
  have hstable : (prefixWord ++ tailWord_3092000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092000).length < 2 ^ (prefixWord ++ tailWord_3092000).sum := by decide
  have hdescent : baseEnd_3092000 < baseStart_3092000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092016 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 5]
def baseStart_3092016 : Nat := 118140960795 + 3092016 * 2 ^ 59
def prefixEnd_3092016 : Nat := 4983230072969 + 3 ^ 40 * 3092016 * 2
def baseEnd_3092016 : Nat := 1587690399392479706880083

theorem tailTrace_3092016 : CollatzResearch.WordTrace tailWord_3092016 prefixEnd_3092016 1587690399392479706880083 := by
  unfold tailWord_3092016
  simp only [CollatzResearch.WordTrace]
  refine ⟨56387544183080790567883951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75183392244107720757178601 56387544183080790567883951)
  ·
    refine ⟨84581316274621185851825927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56387544183080790567883951 84581316274621185851825927)
    ·
      refine ⟨126871974411931778777738891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84581316274621185851825927 126871974411931778777738891)
      ·
        refine ⟨190307961617897668166608337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126871974411931778777738891 190307961617897668166608337)
        ·
          refine ⟨142730971213423251124956253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190307961617897668166608337 142730971213423251124956253)
          ·
            refine ⟨53524114205033719171858595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142730971213423251124956253 53524114205033719171858595)
            ·
              refine ⟨80286171307550578757787893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53524114205033719171858595 80286171307550578757787893)
              ·
                refine ⟨7526828560082866758542615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80286171307550578757787893 7526828560082866758542615)
                ·
                  refine ⟨11290242840124300137813923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7526828560082866758542615 11290242840124300137813923)
                  ·
                    refine ⟨16935364260186450206720885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11290242840124300137813923 16935364260186450206720885)
                    ·
                      refine ⟨1587690399392479706880083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16935364260186450206720885 1587690399392479706880083)
                      ·
                        rfl

theorem cell23_3092016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_3092016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092016 prefixEnd_3092016 := by exact prefixLift 3092016
  have htrace : WordTrace (prefixWord ++ tailWord_3092016) baseStart_3092016 baseEnd_3092016 := by
    simpa [prefixWord, tailWord_3092016, baseEnd_3092016] using wordTrace_append hprefix tailTrace_3092016
  have hstable : (prefixWord ++ tailWord_3092016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092016).length < 2 ^ (prefixWord ++ tailWord_3092016).sum := by decide
  have hdescent : baseEnd_3092016 < baseStart_3092016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092023 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 4, 4]
def baseStart_3092023 : Nat := 118140960795 + 3092023 * 2 ^ 59
def prefixEnd_3092023 : Nat := 4983230072969 + 3 ^ 40 * 3092023 * 2
def baseEnd_3092023 : Nat := 529231331252353726497517

theorem tailTrace_3092023 : CollatzResearch.WordTrace tailWord_3092023 prefixEnd_3092023 529231331252353726497517 := by
  unfold tailWord_3092023
  simp only [CollatzResearch.WordTrace]
  refine ⟨112775343677136221331272723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75183562451424147554181815 112775343677136221331272723)
  ·
    refine ⟨169163015515704331996909085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112775343677136221331272723 169163015515704331996909085)
    ·
      refine ⟨63436130818389124498840907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169163015515704331996909085 63436130818389124498840907)
      ·
        refine ⟨95154196227583686748261361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63436130818389124498840907 95154196227583686748261361)
        ·
          refine ⟨71365647170687765061196021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95154196227583686748261361 71365647170687765061196021)
          ·
            refine ⟨6690529422251977974487127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71365647170687765061196021 6690529422251977974487127)
            ·
              refine ⟨10035794133377966961730691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6690529422251977974487127 10035794133377966961730691)
              ·
                refine ⟨15053691200066950442596037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10035794133377966961730691 15053691200066950442596037)
                ·
                  refine ⟨2822567100012553207986757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15053691200066950442596037 2822567100012553207986757)
                  ·
                    refine ⟨529231331252353726497517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2822567100012553207986757 529231331252353726497517)
                    ·
                      rfl

theorem cell23_3092023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_3092023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3092023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3092023 prefixEnd_3092023 := by exact prefixLift 3092023
  have htrace : WordTrace (prefixWord ++ tailWord_3092023) baseStart_3092023 baseEnd_3092023 := by
    simpa [prefixWord, tailWord_3092023, baseEnd_3092023] using wordTrace_append hprefix tailTrace_3092023
  have hstable : (prefixWord ++ tailWord_3092023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092023).length < 2 ^ (prefixWord ++ tailWord_3092023).sum := by decide
  have hdescent : baseEnd_3092023 < baseStart_3092023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
