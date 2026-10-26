import V185TrunkScan23Chunk1189

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7050653 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_7050653 : Nat := 118140960795 + 7050653 * 2 ^ 59
def prefixEnd_7050653 : Nat := 4983230072969 + 3 ^ 40 * 7050653 * 2
def baseEnd_7050653 : Nat := 3620373917064908021412143

theorem tailTrace_7050653 : CollatzResearch.WordTrace tailWord_7050653 prefixEnd_7050653 3620373917064908021412143 := by
  unfold tailWord_7050653
  simp only [CollatzResearch.WordTrace]
  refine ⟨257158441325695811509780613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171438960883797207673187075 257158441325695811509780613)
  ·
    refine ⟨48217207748567964658083865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257158441325695811509780613 48217207748567964658083865)
    ·
      refine ⟨36162905811425973493562899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48217207748567964658083865 36162905811425973493562899)
      ·
        refine ⟨54244358717138960240344349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36162905811425973493562899 54244358717138960240344349)
        ·
          refine ⟨20341634518927110090129131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54244358717138960240344349 20341634518927110090129131)
          ·
            refine ⟨30512451778390665135193697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20341634518927110090129131 30512451778390665135193697)
            ·
              refine ⟨22884338833792998851395273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30512451778390665135193697 22884338833792998851395273)
              ·
                refine ⟨17163254125344749138546455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22884338833792998851395273 17163254125344749138546455)
                ·
                  refine ⟨25744881188017123707819683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17163254125344749138546455 25744881188017123707819683)
                  ·
                    refine ⟨38617321782025685561729525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25744881188017123707819683 38617321782025685561729525)
                    ·
                      refine ⟨3620373917064908021412143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38617321782025685561729525 3620373917064908021412143)
                      ·
                        rfl

theorem cell23_7050653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_7050653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050653 prefixEnd_7050653 := by exact prefixLift 7050653
  have htrace : WordTrace (prefixWord ++ tailWord_7050653) baseStart_7050653 baseEnd_7050653 := by
    simpa [prefixWord, tailWord_7050653, baseEnd_7050653] using wordTrace_append hprefix tailTrace_7050653
  have hstable : (prefixWord ++ tailWord_7050653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050653).length < 2 ^ (prefixWord ++ tailWord_7050653).sum := by decide
  have hdescent : baseEnd_7050653 < baseStart_7050653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050656 : List Nat := [2, 1, 1, 4, 1, 2, 4, 8]
def baseStart_7050656 : Nat := 118140960795 + 7050656 * 2 ^ 59
def prefixEnd_7050656 : Nat := 4983230072969 + 3 ^ 40 * 7050656 * 2
def baseEnd_7050656 : Nat := 134087979907661907765727

theorem tailTrace_7050656 : CollatzResearch.WordTrace tailWord_7050656 prefixEnd_7050656 134087979907661907765727 := by
  unfold tailWord_7050656
  simp only [CollatzResearch.WordTrace]
  refine ⟨128579275372342471511069911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171439033829789962014759881 128579275372342471511069911)
  ·
    refine ⟨192868913058513707266604867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128579275372342471511069911 192868913058513707266604867)
    ·
      refine ⟨289303369587770560899907301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192868913058513707266604867 289303369587770560899907301)
      ·
        refine ⟨54244381797706980168732619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289303369587770560899907301 54244381797706980168732619)
        ·
          refine ⟨81366572696560470253098929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54244381797706980168732619 81366572696560470253098929)
          ·
            refine ⟨61024929522420352689824197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81366572696560470253098929 61024929522420352689824197)
            ·
              refine ⟨11442174285453816129342037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61024929522420352689824197 11442174285453816129342037)
              ·
                refine ⟨134087979907661907765727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11442174285453816129342037 134087979907661907765727)
                ·
                  rfl

theorem cell23_7050656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 8].length) (baseStart_7050656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050656 prefixEnd_7050656 := by exact prefixLift 7050656
  have htrace : WordTrace (prefixWord ++ tailWord_7050656) baseStart_7050656 baseEnd_7050656 := by
    simpa [prefixWord, tailWord_7050656, baseEnd_7050656] using wordTrace_append hprefix tailTrace_7050656
  have hstable : (prefixWord ++ tailWord_7050656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050656).length < 2 ^ (prefixWord ++ tailWord_7050656).sum := by decide
  have hdescent : baseEnd_7050656 < baseStart_7050656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050663 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_7050663 : Nat := 118140960795 + 7050663 * 2 ^ 59
def prefixEnd_7050663 : Nat := 4983230072969 + 3 ^ 40 * 7050663 * 2
def baseEnd_7050663 : Nat := 3620379051871452982287097

theorem tailTrace_7050663 : CollatzResearch.WordTrace tailWord_7050663 prefixEnd_7050663 3620379051871452982287097 := by
  unfold tailWord_7050663
  simp only [CollatzResearch.WordTrace]
  refine ⟨257158806055659583217644643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171439204037106388811763095 257158806055659583217644643)
  ·
    refine ⟨385738209083489374826466965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257158806055659583217644643 385738209083489374826466965)
    ·
      refine ⟨18081478550788564444990639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 385738209083489374826466965 18081478550788564444990639)
      ·
        refine ⟨27122217826182846667485959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18081478550788564444990639 27122217826182846667485959)
        ·
          refine ⟨40683326739274270001228939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27122217826182846667485959 40683326739274270001228939)
          ·
            refine ⟨61024990108911405001843409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40683326739274270001228939 61024990108911405001843409)
            ·
              refine ⟨45768742581683553751382557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61024990108911405001843409 45768742581683553751382557)
              ·
                refine ⟨17163278468131332656768459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45768742581683553751382557 17163278468131332656768459)
                ·
                  refine ⟨25744917702196998985152689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17163278468131332656768459 25744917702196998985152689)
                  ·
                    refine ⟨19308688276647749238864517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25744917702196998985152689 19308688276647749238864517)
                    ·
                      refine ⟨3620379051871452982287097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19308688276647749238864517 3620379051871452982287097)
                      ·
                        rfl

theorem cell23_7050663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_7050663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050663 prefixEnd_7050663 := by exact prefixLift 7050663
  have htrace : WordTrace (prefixWord ++ tailWord_7050663) baseStart_7050663 baseEnd_7050663 := by
    simpa [prefixWord, tailWord_7050663, baseEnd_7050663] using wordTrace_append hprefix tailTrace_7050663
  have hstable : (prefixWord ++ tailWord_7050663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050663).length < 2 ^ (prefixWord ++ tailWord_7050663).sum := by decide
  have hdescent : baseEnd_7050663 < baseStart_7050663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050664 : List Nat := [2, 1, 6, 1, 3, 1, 1, 2, 1, 5]
def baseStart_7050664 : Nat := 118140960795 + 7050664 * 2 ^ 59
def prefixEnd_7050664 : Nat := 4983230072969 + 3 ^ 40 * 7050664 * 2
def baseEnd_7050664 : Nat := 1206793188450702492791531

theorem tailTrace_7050664 : CollatzResearch.WordTrace tailWord_7050664 prefixEnd_7050664 1206793188450702492791531 := by
  unfold tailWord_7050664
  simp only [CollatzResearch.WordTrace]
  refine ⟨128579421264327980194215523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171439228352437306925620697 128579421264327980194215523)
  ·
    refine ⟨192869131896491970291323285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128579421264327980194215523 192869131896491970291323285)
    ·
      refine ⟨9040740557648061107405779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 192869131896491970291323285 9040740557648061107405779)
      ·
        refine ⟨13561110836472091661108669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9040740557648061107405779 13561110836472091661108669)
        ·
          refine ⟨5085416563677034372915751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13561110836472091661108669 5085416563677034372915751)
          ·
            refine ⟨7628124845515551559373627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5085416563677034372915751 7628124845515551559373627)
            ·
              refine ⟨11442187268273327339060441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7628124845515551559373627 11442187268273327339060441)
              ·
                refine ⟨8581640451204995504295331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11442187268273327339060441 8581640451204995504295331)
                ·
                  refine ⟨12872460676807493256442997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8581640451204995504295331 12872460676807493256442997)
                  ·
                    refine ⟨1206793188450702492791531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12872460676807493256442997 1206793188450702492791531)
                    ·
                      rfl

theorem cell23_7050664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_7050664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050664 prefixEnd_7050664 := by exact prefixLift 7050664
  have htrace : WordTrace (prefixWord ++ tailWord_7050664) baseStart_7050664 baseEnd_7050664 := by
    simpa [prefixWord, tailWord_7050664, baseEnd_7050664] using wordTrace_append hprefix tailTrace_7050664
  have hstable : (prefixWord ++ tailWord_7050664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050664).length < 2 ^ (prefixWord ++ tailWord_7050664).sum := by decide
  have hdescent : baseEnd_7050664 < baseStart_7050664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050717 : List Nat := [1, 4, 3, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_7050717 : Nat := 118140960795 + 7050717 * 2 ^ 59
def prefixEnd_7050717 : Nat := 4983230072969 + 3 ^ 40 * 7050717 * 2
def baseEnd_7050717 : Nat := 3620406779826795771011849

theorem tailTrace_7050717 : CollatzResearch.WordTrace tailWord_7050717 prefixEnd_7050717 3620406779826795771011849 := by
  unfold tailWord_7050717
  simp only [CollatzResearch.WordTrace]
  refine ⟨257160775597463950440110405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171440517064975966960073603 257160775597463950440110405)
  ·
    refine ⟨48217645424524490707520701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257160775597463950440110405 48217645424524490707520701)
    ·
      refine ⟨18081617034196684015320263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48217645424524490707520701 18081617034196684015320263)
      ·
        refine ⟨27122425551295026022980395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18081617034196684015320263 27122425551295026022980395)
        ·
          refine ⟨40683638326942539034470593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27122425551295026022980395 40683638326942539034470593)
          ·
            refine ⟨30512728745206904275852945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40683638326942539034470593 30512728745206904275852945)
            ·
              refine ⟨22884546558905178206889709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30512728745206904275852945 22884546558905178206889709)
              ·
                refine ⟨8581704959589441827583641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22884546558905178206889709 8581704959589441827583641)
                ·
                  refine ⟨6436278719692081370687731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8581704959589441827583641 6436278719692081370687731)
                  ·
                    refine ⟨9654418079538122056031597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6436278719692081370687731 9654418079538122056031597)
                    ·
                      refine ⟨3620406779826795771011849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9654418079538122056031597 3620406779826795771011849)
                      ·
                        rfl

theorem cell23_7050717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_7050717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050717 prefixEnd_7050717 := by exact prefixLift 7050717
  have htrace : WordTrace (prefixWord ++ tailWord_7050717) baseStart_7050717 baseEnd_7050717 := by
    simpa [prefixWord, tailWord_7050717, baseEnd_7050717] using wordTrace_append hprefix tailTrace_7050717
  have hstable : (prefixWord ++ tailWord_7050717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050717).length < 2 ^ (prefixWord ++ tailWord_7050717).sum := by decide
  have hdescent : baseEnd_7050717 < baseStart_7050717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050744 : List Nat := [2, 1, 2, 1, 1, 7, 2, 1, 1, 3, 2]
def baseStart_7050744 : Nat := 118140960795 + 7050744 * 2 ^ 59
def prefixEnd_7050744 : Nat := 4983230072969 + 3 ^ 40 * 7050744 * 2
def baseEnd_7050744 : Nat := 3620420643804467165374225

theorem tailTrace_7050744 : CollatzResearch.WordTrace tailWord_7050744 prefixEnd_7050744 3620420643804467165374225 := by
  unfold tailWord_7050744
  simp only [CollatzResearch.WordTrace]
  refine ⟨128580880184183067025671643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171441173578910756034228857 128580880184183067025671643)
  ·
    refine ⟨192871320276274600538507465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128580880184183067025671643 192871320276274600538507465)
    ·
      refine ⟨144653490207205950403880599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192871320276274600538507465 144653490207205950403880599)
      ·
        refine ⟨216980235310808925605820899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144653490207205950403880599 216980235310808925605820899)
        ·
          refine ⟨325470352966213388408731349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216980235310808925605820899 325470352966213388408731349)
          ·
            refine ⟨7628211397645626290829641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 325470352966213388408731349 7628211397645626290829641)
            ·
              refine ⟨5721158548234219718122231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7628211397645626290829641 5721158548234219718122231)
              ·
                refine ⟨8581737822351329577183347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5721158548234219718122231 8581737822351329577183347)
                ·
                  refine ⟨12872606733526994365775021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8581737822351329577183347 12872606733526994365775021)
                  ·
                    refine ⟨4827227525072622887165633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12872606733526994365775021 4827227525072622887165633)
                    ·
                      refine ⟨3620420643804467165374225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4827227525072622887165633 3620420643804467165374225)
                      ·
                        rfl

theorem cell23_7050744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 1, 3, 2].length) (baseStart_7050744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050744 prefixEnd_7050744 := by exact prefixLift 7050744
  have htrace : WordTrace (prefixWord ++ tailWord_7050744) baseStart_7050744 baseEnd_7050744 := by
    simpa [prefixWord, tailWord_7050744, baseEnd_7050744] using wordTrace_append hprefix tailTrace_7050744
  have hstable : (prefixWord ++ tailWord_7050744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050744).length < 2 ^ (prefixWord ++ tailWord_7050744).sum := by decide
  have hdescent : baseEnd_7050744 < baseStart_7050744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050746 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 9]
def baseStart_7050746 : Nat := 118140960795 + 7050746 * 2 ^ 59
def prefixEnd_7050746 : Nat := 4983230072969 + 3 ^ 40 * 7050746 * 2
def baseEnd_7050746 : Nat := 402269074529530684172135

theorem tailTrace_7050746 : CollatzResearch.WordTrace tailWord_7050746 prefixEnd_7050746 402269074529530684172135 := by
  unfold tailWord_7050746
  simp only [CollatzResearch.WordTrace]
  refine ⟨64290458328589722098229023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171441222209572592261944061 64290458328589722098229023)
  ·
    refine ⟨96435687492884583147343535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64290458328589722098229023 96435687492884583147343535)
    ·
      refine ⟨144653531239326874721015303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96435687492884583147343535 144653531239326874721015303)
      ·
        refine ⟨216980296858990312081522955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144653531239326874721015303 216980296858990312081522955)
        ·
          refine ⟨325470445288485468122284433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216980296858990312081522955 325470445288485468122284433)
          ·
            refine ⟨244102833966364101091713325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325470445288485468122284433 244102833966364101091713325)
            ·
              refine ⟨91538562737386537909392497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244102833966364101091713325 91538562737386537909392497)
              ·
                refine ⟨68653922053039903432044373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91538562737386537909392497 68653922053039903432044373)
                ·
                  refine ⟨402269074529530684172135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68653922053039903432044373 402269074529530684172135)
                  ·
                    rfl

theorem cell23_7050746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 9].length) (baseStart_7050746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050746 prefixEnd_7050746 := by exact prefixLift 7050746
  have htrace : WordTrace (prefixWord ++ tailWord_7050746) baseStart_7050746 baseEnd_7050746 := by
    simpa [prefixWord, tailWord_7050746, baseEnd_7050746] using wordTrace_append hprefix tailTrace_7050746
  have hstable : (prefixWord ++ tailWord_7050746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050746).length < 2 ^ (prefixWord ++ tailWord_7050746).sum := by decide
  have hdescent : baseEnd_7050746 < baseStart_7050746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050830 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2]
def baseStart_7050830 : Nat := 118140960795 + 7050830 * 2 ^ 59
def prefixEnd_7050830 : Nat := 4983230072969 + 3 ^ 40 * 7050830 * 2
def baseEnd_7050830 : Nat := 3620464803140753828898829

theorem tailTrace_7050830 : CollatzResearch.WordTrace tailWord_7050830 prefixEnd_7050830 3620464803140753828898829 := by
  unfold tailWord_7050830
  simp only [CollatzResearch.WordTrace]
  refine ⟨32145612130756821342371743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171443264697369713825982629 32145612130756821342371743)
  ·
    refine ⟨48218418196135232013557615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32145612130756821342371743 48218418196135232013557615)
    ·
      refine ⟨72327627294202848020336423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48218418196135232013557615 72327627294202848020336423)
      ·
        refine ⟨108491440941304272030504635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72327627294202848020336423 108491440941304272030504635)
        ·
          refine ⟨162737161411956408045756953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108491440941304272030504635 162737161411956408045756953)
          ·
            refine ⟨122052871058967306034317715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162737161411956408045756953 122052871058967306034317715)
            ·
              refine ⟨183079306588450959051476573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122052871058967306034317715 183079306588450959051476573)
              ·
                refine ⟨68654739970669109644303715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183079306588450959051476573 68654739970669109644303715)
                ·
                  refine ⟨102982109956003664466455573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68654739970669109644303715 102982109956003664466455573)
                  ·
                    refine ⟨4827286404187671771865105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102982109956003664466455573 4827286404187671771865105)
                    ·
                      refine ⟨3620464803140753828898829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4827286404187671771865105 3620464803140753828898829)
                      ·
                        rfl

theorem cell23_7050830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_7050830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050830 prefixEnd_7050830 := by exact prefixLift 7050830
  have htrace : WordTrace (prefixWord ++ tailWord_7050830) baseStart_7050830 baseEnd_7050830 := by
    simpa [prefixWord, tailWord_7050830, baseEnd_7050830] using wordTrace_append hprefix tailTrace_7050830
  have hstable : (prefixWord ++ tailWord_7050830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050830).length < 2 ^ (prefixWord ++ tailWord_7050830).sum := by decide
  have hdescent : baseEnd_7050830 < baseStart_7050830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050873 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 6]
def baseStart_7050873 : Nat := 118140960795 + 7050873 * 2 ^ 59
def prefixEnd_7050873 : Nat := 4983230072969 + 3 ^ 40 * 7050873 * 2
def baseEnd_7050873 : Nat := 3620486882808897160661131

theorem tailTrace_7050873 : CollatzResearch.WordTrace tailWord_7050873 prefixEnd_7050873 3620486882808897160661131 := by
  unfold tailWord_7050873
  simp only [CollatzResearch.WordTrace]
  refine ⟨257166465384898789082789273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171444310256599192721859515 257166465384898789082789273)
  ·
    refine ⟨192874849038674091812091955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257166465384898789082789273 192874849038674091812091955)
    ·
      refine ⟨289312273558011137718137933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192874849038674091812091955 289312273558011137718137933)
      ·
        refine ⟨108492102584254176644301725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289312273558011137718137933 108492102584254176644301725)
        ·
          refine ⟨40684538469095316241613147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108492102584254176644301725 40684538469095316241613147)
          ·
            refine ⟨61026807703642974362419721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40684538469095316241613147 61026807703642974362419721)
            ·
              refine ⟨45770105777732230771814791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61026807703642974362419721 45770105777732230771814791)
              ·
                refine ⟨68655158666598346157722187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45770105777732230771814791 68655158666598346157722187)
                ·
                  refine ⟨102982737999897519236583281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68655158666598346157722187 102982737999897519236583281)
                  ·
                    refine ⟨77237053499923139427437461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102982737999897519236583281 77237053499923139427437461)
                    ·
                      refine ⟨3620486882808897160661131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77237053499923139427437461 3620486882808897160661131)
                      ·
                        rfl

theorem cell23_7050873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_7050873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050873 prefixEnd_7050873 := by exact prefixLift 7050873
  have htrace : WordTrace (prefixWord ++ tailWord_7050873) baseStart_7050873 baseEnd_7050873 := by
    simpa [prefixWord, tailWord_7050873, baseEnd_7050873] using wordTrace_append hprefix tailTrace_7050873
  have hstable : (prefixWord ++ tailWord_7050873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050873).length < 2 ^ (prefixWord ++ tailWord_7050873).sum := by decide
  have hdescent : baseEnd_7050873 < baseStart_7050873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050917 : List Nat := [1, 3, 1, 2, 1, 2, 6, 1, 1, 5]
def baseStart_7050917 : Nat := 118140960795 + 7050917 * 2 ^ 59
def prefixEnd_7050917 : Nat := 4983230072969 + 3 ^ 40 * 7050917 * 2
def baseEnd_7050917 : Nat := 1206836491985898329503643

theorem tailTrace_7050917 : CollatzResearch.WordTrace tailWord_7050917 prefixEnd_7050917 1206836491985898329503643 := by
  unfold tailWord_7050917
  simp only [CollatzResearch.WordTrace]
  refine ⟨257168070196739384597391005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171445380131159589731594003 257168070196739384597391005)
  ·
    refine ⟨96438026323777269224021627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257168070196739384597391005 96438026323777269224021627)
    ·
      refine ⟨144657039485665903836032441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96438026323777269224021627 144657039485665903836032441)
      ·
        refine ⟨108492779614249427877024331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144657039485665903836032441 108492779614249427877024331)
        ·
          refine ⟨162739169421374141815536497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108492779614249427877024331 162739169421374141815536497)
          ·
            refine ⟨122054377066030606361652373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162739169421374141815536497 122054377066030606361652373)
            ·
              refine ⟨5721298924970184673202455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122054377066030606361652373 5721298924970184673202455)
              ·
                refine ⟨8581948387455277009803683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5721298924970184673202455 8581948387455277009803683)
                ·
                  refine ⟨12872922581182915514705525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8581948387455277009803683 12872922581182915514705525)
                  ·
                    refine ⟨1206836491985898329503643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12872922581182915514705525 1206836491985898329503643)
                    ·
                      rfl

theorem cell23_7050917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_7050917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050917 prefixEnd_7050917 := by exact prefixLift 7050917
  have htrace : WordTrace (prefixWord ++ tailWord_7050917) baseStart_7050917 baseEnd_7050917 := by
    simpa [prefixWord, tailWord_7050917, baseEnd_7050917] using wordTrace_append hprefix tailTrace_7050917
  have hstable : (prefixWord ++ tailWord_7050917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050917).length < 2 ^ (prefixWord ++ tailWord_7050917).sum := by decide
  have hdescent : baseEnd_7050917 < baseStart_7050917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050940 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_7050940 : Nat := 118140960795 + 7050940 * 2 ^ 59
def prefixEnd_7050940 : Nat := 4983230072969 + 3 ^ 40 * 7050940 * 2
def baseEnd_7050940 : Nat := 3620521286012748398523323

theorem tailTrace_7050940 : CollatzResearch.WordTrace tailWord_7050940 prefixEnd_7050940 3620521286012748398523323 := by
  unfold tailWord_7050940
  simp only [CollatzResearch.WordTrace]
  refine ⟨128584454537828029762739137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171445939383770706350318849 128584454537828029762739137)
  ·
    refine ⟨96438340903371022322054353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128584454537828029762739137 96438340903371022322054353)
    ·
      refine ⟨72328755677528266741540765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96438340903371022322054353 72328755677528266741540765)
      ·
        refine ⟨27123283379073100028077787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72328755677528266741540765 27123283379073100028077787)
        ·
          refine ⟨40684925068609650042116681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27123283379073100028077787 40684925068609650042116681)
          ·
            refine ⟨30513693801457237531587511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40684925068609650042116681 30513693801457237531587511)
            ·
              refine ⟨45770540702185856297381267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30513693801457237531587511 45770540702185856297381267)
              ·
                refine ⟨68655811053278784446071901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45770540702185856297381267 68655811053278784446071901)
                ·
                  refine ⟨25745929144979544167276963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68655811053278784446071901 25745929144979544167276963)
                  ·
                    refine ⟨38618893717469316250915445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25745929144979544167276963 38618893717469316250915445)
                    ·
                      refine ⟨3620521286012748398523323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38618893717469316250915445 3620521286012748398523323)
                      ·
                        rfl

theorem cell23_7050940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_7050940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050940 prefixEnd_7050940 := by exact prefixLift 7050940
  have htrace : WordTrace (prefixWord ++ tailWord_7050940) baseStart_7050940 baseEnd_7050940 := by
    simpa [prefixWord, tailWord_7050940, baseEnd_7050940] using wordTrace_append hprefix tailTrace_7050940
  have hstable : (prefixWord ++ tailWord_7050940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050940).length < 2 ^ (prefixWord ++ tailWord_7050940).sum := by decide
  have hdescent : baseEnd_7050940 < baseStart_7050940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050943 : List Nat := [1, 1, 2, 2, 2, 3, 2, 10]
def baseStart_7050943 : Nat := 118140960795 + 7050943 * 2 ^ 59
def prefixEnd_7050943 : Nat := 4983230072969 + 3 ^ 40 * 7050943 * 2
def baseEnd_7050943 : Nat := 134093438016841180992067

theorem tailTrace_7050943 : CollatzResearch.WordTrace tailWord_7050943 prefixEnd_7050943 134093438016841180992067 := by
  unfold tailWord_7050943
  simp only [CollatzResearch.WordTrace]
  refine ⟨257169018494645191037837483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171446012329763460691891655 257169018494645191037837483)
  ·
    refine ⟨385753527741967786556756225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257169018494645191037837483 385753527741967786556756225)
    ·
      refine ⟨289315145806475839917567169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385753527741967786556756225 289315145806475839917567169)
      ·
        refine ⟨216986359354856879938175377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289315145806475839917567169 216986359354856879938175377)
        ·
          refine ⟨162739769516142659953631533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216986359354856879938175377 162739769516142659953631533)
          ·
            refine ⟨61027413568553497482611825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162739769516142659953631533 61027413568553497482611825)
            ·
              refine ⟨45770560176415123111958869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61027413568553497482611825 45770560176415123111958869)
              ·
                refine ⟨134093438016841180992067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45770560176415123111958869 134093438016841180992067)
                ·
                  rfl

theorem cell23_7050943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 10].length) (baseStart_7050943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050943 prefixEnd_7050943 := by exact prefixLift 7050943
  have htrace : WordTrace (prefixWord ++ tailWord_7050943) baseStart_7050943 baseEnd_7050943 := by
    simpa [prefixWord, tailWord_7050943, baseEnd_7050943] using wordTrace_append hprefix tailTrace_7050943
  have hstable : (prefixWord ++ tailWord_7050943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050943).length < 2 ^ (prefixWord ++ tailWord_7050943).sum := by decide
  have hdescent : baseEnd_7050943 < baseStart_7050943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050954 : List Nat := [3, 1, 2, 1, 5, 1, 2, 2, 1, 1, 4]
def baseStart_7050954 : Nat := 118140960795 + 7050954 * 2 ^ 59
def prefixEnd_7050954 : Nat := 4983230072969 + 3 ^ 40 * 7050954 * 2
def baseEnd_7050954 : Nat := 3620528474741911343748259

theorem tailTrace_7050954 : CollatzResearch.WordTrace tailWord_7050954 prefixEnd_7050954 3620528474741911343748259 := by
  unfold tailWord_7050954
  simp only [CollatzResearch.WordTrace]
  refine ⟨64292354924401334979121979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171446279798403559944325277 64292354924401334979121979)
  ·
    refine ⟨96438532386602002468682969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64292354924401334979121979 96438532386602002468682969)
    ·
      refine ⟨72328899289951501851512227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96438532386602002468682969 72328899289951501851512227)
      ·
        refine ⟨108493348934927252777268341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72328899289951501851512227 108493348934927252777268341)
        ·
          refine ⟨10171251462649429947868907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108493348934927252777268341 10171251462649429947868907)
          ·
            refine ⟨15256877193974144921803361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10171251462649429947868907 15256877193974144921803361)
            ·
              refine ⟨11442657895480608691352521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15256877193974144921803361 11442657895480608691352521)
              ·
                refine ⟨8581993421610456518514391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11442657895480608691352521 8581993421610456518514391)
                ·
                  refine ⟨12872990132415684777771587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8581993421610456518514391 12872990132415684777771587)
                  ·
                    refine ⟨19309485198623527166657381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12872990132415684777771587 19309485198623527166657381)
                    ·
                      refine ⟨3620528474741911343748259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19309485198623527166657381 3620528474741911343748259)
                      ·
                        rfl

theorem cell23_7050954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_7050954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050954 prefixEnd_7050954 := by exact prefixLift 7050954
  have htrace : WordTrace (prefixWord ++ tailWord_7050954) baseStart_7050954 baseEnd_7050954 := by
    simpa [prefixWord, tailWord_7050954, baseEnd_7050954] using wordTrace_append hprefix tailTrace_7050954
  have hstable : (prefixWord ++ tailWord_7050954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050954).length < 2 ^ (prefixWord ++ tailWord_7050954).sum := by decide
  have hdescent : baseEnd_7050954 < baseStart_7050954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050977 : List Nat := [1, 2, 3, 1, 6, 1, 9]
def baseStart_7050977 : Nat := 118140960795 + 7050977 * 2 ^ 59
def prefixEnd_7050977 : Nat := 4983230072969 + 3 ^ 40 * 7050977 * 2
def baseEnd_7050977 : Nat := 44698028207369935231613

theorem tailTrace_7050977 : CollatzResearch.WordTrace tailWord_7050977 prefixEnd_7050977 44698028207369935231613 := by
  unfold tailWord_7050977
  simp only [CollatzResearch.WordTrace]
  refine ⟨257170258576522014844575185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171446839051014676563050123 257170258576522014844575185)
  ·
    refine ⟨192877693932391511133431389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257170258576522014844575185 192877693932391511133431389)
    ·
      refine ⟨72329135224646816675036771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192877693932391511133431389 72329135224646816675036771)
      ·
        refine ⟨108493702836970225012555157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72329135224646816675036771 108493702836970225012555157)
        ·
          refine ⟨5085642320482979297463523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108493702836970225012555157 5085642320482979297463523)
          ·
            refine ⟨7628463480724468946195285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5085642320482979297463523 7628463480724468946195285)
            ·
              refine ⟨44698028207369935231613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7628463480724468946195285 44698028207369935231613)
              ·
                rfl

theorem cell23_7050977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 9].length) (baseStart_7050977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050977 prefixEnd_7050977 := by exact prefixLift 7050977
  have htrace : WordTrace (prefixWord ++ tailWord_7050977) baseStart_7050977 baseEnd_7050977 := by
    simpa [prefixWord, tailWord_7050977, baseEnd_7050977] using wordTrace_append hprefix tailTrace_7050977
  have hstable : (prefixWord ++ tailWord_7050977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050977).length < 2 ^ (prefixWord ++ tailWord_7050977).sum := by decide
  have hdescent : baseEnd_7050977 < baseStart_7050977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050987 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 4, 1, 3]
def baseStart_7050987 : Nat := 118140960795 + 7050987 * 2 ^ 59
def prefixEnd_7050987 : Nat := 4983230072969 + 3 ^ 40 * 7050987 * 2
def baseEnd_7050987 : Nat := 3620545419603509714635607

theorem tailTrace_7050987 : CollatzResearch.WordTrace tailWord_7050987 prefixEnd_7050987 3620545419603509714635607 := by
  unfold tailWord_7050987
  simp only [CollatzResearch.WordTrace]
  refine ⟨257170623306485786552439215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171447082204323857701626143 257170623306485786552439215)
  ·
    refine ⟨385755934959728679828658823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257170623306485786552439215 385755934959728679828658823)
    ·
      refine ⟨578633902439593019742988235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385755934959728679828658823 578633902439593019742988235)
      ·
        refine ⟨867950853659389529614482353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578633902439593019742988235 867950853659389529614482353)
        ·
          refine ⟨650963140244542147210861765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 867950853659389529614482353 650963140244542147210861765)
          ·
            refine ⟨122055588795851652602036581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 650963140244542147210861765 122055588795851652602036581)
            ·
              refine ⟨22885422899222184862881859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122055588795851652602036581 22885422899222184862881859)
              ·
                refine ⟨34328134348833277294322789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22885422899222184862881859 34328134348833277294322789)
                ·
                  refine ⟨6436525190406239492685523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34328134348833277294322789 6436525190406239492685523)
                  ·
                    refine ⟨9654787785609359239028285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6436525190406239492685523 9654787785609359239028285)
                    ·
                      refine ⟨3620545419603509714635607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9654787785609359239028285 3620545419603509714635607)
                      ·
                        rfl

theorem cell23_7050987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 1, 3].length) (baseStart_7050987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050987 prefixEnd_7050987 := by exact prefixLift 7050987
  have htrace : WordTrace (prefixWord ++ tailWord_7050987) baseStart_7050987 baseEnd_7050987 := by
    simpa [prefixWord, tailWord_7050987, baseEnd_7050987] using wordTrace_append hprefix tailTrace_7050987
  have hstable : (prefixWord ++ tailWord_7050987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050987).length < 2 ^ (prefixWord ++ tailWord_7050987).sum := by decide
  have hdescent : baseEnd_7050987 < baseStart_7050987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050990 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_7050990 : Nat := 118140960795 + 7050990 * 2 ^ 59
def prefixEnd_7050990 : Nat := 4983230072969 + 3 ^ 40 * 7050990 * 2
def baseEnd_7050990 : Nat := 1206848986681824400966031

theorem tailTrace_7050990 : CollatzResearch.WordTrace tailWord_7050990 prefixEnd_7050990 1206848986681824400966031 := by
  unfold tailWord_7050990
  simp only [CollatzResearch.WordTrace]
  refine ⟨32146341590684364758099803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171447155150316612043198949 32146341590684364758099803)
  ·
    refine ⟨48219512386026547137149705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32146341590684364758099803 48219512386026547137149705)
    ·
      refine ⟨36164634289519910352862279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48219512386026547137149705 36164634289519910352862279)
      ·
        refine ⟨54246951434279865529293419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36164634289519910352862279 54246951434279865529293419)
        ·
          refine ⟨81370427151419798293940129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54246951434279865529293419 81370427151419798293940129)
          ·
            refine ⟨61027820363564848720455097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81370427151419798293940129 61027820363564848720455097)
            ·
              refine ⟨45770865272673636540341323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61027820363564848720455097 45770865272673636540341323)
              ·
                refine ⟨68656297909010454810511985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45770865272673636540341323 68656297909010454810511985)
                ·
                  refine ⟨51492223431757841107883989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68656297909010454810511985 51492223431757841107883989)
                  ·
                    refine ⟨1206848986681824400966031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51492223431757841107883989 1206848986681824400966031)
                    ·
                      rfl

theorem cell23_7050990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_7050990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050990 prefixEnd_7050990 := by exact prefixLift 7050990
  have htrace : WordTrace (prefixWord ++ tailWord_7050990) baseStart_7050990 baseEnd_7050990 := by
    simpa [prefixWord, tailWord_7050990, baseEnd_7050990] using wordTrace_append hprefix tailTrace_7050990
  have hstable : (prefixWord ++ tailWord_7050990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050990).length < 2 ^ (prefixWord ++ tailWord_7050990).sum := by decide
  have hdescent : baseEnd_7050990 < baseStart_7050990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051004 : List Nat := [2, 2, 2, 1, 3, 1, 3, 3, 2, 1, 3]
def baseStart_7051004 : Nat := 118140960795 + 7051004 * 2 ^ 59
def prefixEnd_7051004 : Nat := 4983230072969 + 3 ^ 40 * 7051004 * 2
def baseEnd_7051004 : Nat := 3620554148774636148123029

theorem tailTrace_7051004 : CollatzResearch.WordTrace tailWord_7051004 prefixEnd_7051004 3620554148774636148123029 := by
  unfold tailWord_7051004
  simp only [CollatzResearch.WordTrace]
  refine ⟨128585621673712099227904033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171447495564949465637205377 128585621673712099227904033)
  ·
    refine ⟨96439216255284074420928025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128585621673712099227904033 96439216255284074420928025)
    ·
      refine ⟨72329412191463055815696019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96439216255284074420928025 72329412191463055815696019)
      ·
        refine ⟨108494118287194583723544029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72329412191463055815696019 108494118287194583723544029)
        ·
          refine ⟨40685294357697968896329011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108494118287194583723544029 40685294357697968896329011)
          ·
            refine ⟨61027941536546953344493517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40685294357697968896329011 61027941536546953344493517)
            ·
              refine ⟨22885478076205107504185069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61027941536546953344493517 22885478076205107504185069)
              ·
                refine ⟨8582054278576915314069401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22885478076205107504185069 8582054278576915314069401)
                ·
                  refine ⟨6436540708932686485552051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8582054278576915314069401 6436540708932686485552051)
                  ·
                    refine ⟨9654811063399029728328077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6436540708932686485552051 9654811063399029728328077)
                    ·
                      refine ⟨3620554148774636148123029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9654811063399029728328077 3620554148774636148123029)
                      ·
                        rfl

theorem cell23_7051004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_7051004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051004 prefixEnd_7051004 := by exact prefixLift 7051004
  have htrace : WordTrace (prefixWord ++ tailWord_7051004) baseStart_7051004 baseEnd_7051004 := by
    simpa [prefixWord, tailWord_7051004, baseEnd_7051004] using wordTrace_append hprefix tailTrace_7051004
  have hstable : (prefixWord ++ tailWord_7051004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051004).length < 2 ^ (prefixWord ++ tailWord_7051004).sum := by decide
  have hdescent : baseEnd_7051004 < baseStart_7051004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051054 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 2, 6]
def baseStart_7051054 : Nat := 118140960795 + 7051054 * 2 ^ 59
def prefixEnd_7051054 : Nat := 4983230072969 + 3 ^ 40 * 7051054 * 2
def baseEnd_7051054 : Nat := 1206859940935786984165933

theorem tailTrace_7051054 : CollatzResearch.WordTrace tailWord_7051054 prefixEnd_7051054 1206859940935786984165933 := by
  unfold tailWord_7051054
  simp only [CollatzResearch.WordTrace]
  refine ⟨32146633374655382124391027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171448711331495371330085477 32146633374655382124391027)
  ·
    refine ⟨48219950061983073186586541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32146633374655382124391027 48219950061983073186586541)
    ·
      refine ⟨18082481273243652444969953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48219950061983073186586541 18082481273243652444969953)
      ·
        refine ⟨13561860954932739333727465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18082481273243652444969953 13561860954932739333727465)
        ·
          refine ⟨10171395716199554500295599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13561860954932739333727465 10171395716199554500295599)
          ·
            refine ⟨15257093574299331750443399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10171395716199554500295599 15257093574299331750443399)
            ·
              refine ⟨22885640361448997625665099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15257093574299331750443399 22885640361448997625665099)
              ·
                refine ⟨34328460542173496438497649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22885640361448997625665099 34328460542173496438497649)
                ·
                  refine ⟨25746345406630122328873237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34328460542173496438497649 25746345406630122328873237)
                  ·
                    refine ⟨1206859940935786984165933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25746345406630122328873237 1206859940935786984165933)
                    ·
                      rfl

theorem cell23_7051054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_7051054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051054 prefixEnd_7051054 := by exact prefixLift 7051054
  have htrace : WordTrace (prefixWord ++ tailWord_7051054) baseStart_7051054 baseEnd_7051054 := by
    simpa [prefixWord, tailWord_7051054, baseEnd_7051054] using wordTrace_append hprefix tailTrace_7051054
  have hstable : (prefixWord ++ tailWord_7051054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051054).length < 2 ^ (prefixWord ++ tailWord_7051054).sum := by decide
  have hdescent : baseEnd_7051054 < baseStart_7051054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051057 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 2, 2, 4]
def baseStart_7051057 : Nat := 118140960795 + 7051057 * 2 ^ 59
def prefixEnd_7051057 : Nat := 4983230072969 + 3 ^ 40 * 7051057 * 2
def baseEnd_7051057 : Nat := 3620581363249324440760285

theorem tailTrace_7051057 : CollatzResearch.WordTrace tailWord_7051057 prefixEnd_7051057 3620581363249324440760285 := by
  unfold tailWord_7051057
  simp only [CollatzResearch.WordTrace]
  refine ⟨257173176416232188507487425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171448784277488125671658283 257173176416232188507487425)
  ·
    refine ⟨192879882312174141380615569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257173176416232188507487425 192879882312174141380615569)
    ·
      refine ⟨144659911734130606035461677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192879882312174141380615569 144659911734130606035461677)
      ·
        refine ⟨54247466900298977263298129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144659911734130606035461677 54247466900298977263298129)
        ·
          refine ⟨40685600175224232947473597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54247466900298977263298129 40685600175224232947473597)
          ·
            refine ⟨15257100065709087355302599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40685600175224232947473597 15257100065709087355302599)
            ·
              refine ⟨22885650098563631032953899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15257100065709087355302599 22885650098563631032953899)
              ·
                refine ⟨34328475147845446549430849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22885650098563631032953899 34328475147845446549430849)
                ·
                  refine ⟨25746356360884084912073137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34328475147845446549430849 25746356360884084912073137)
                  ·
                    refine ⟨19309767270663063684054853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25746356360884084912073137 19309767270663063684054853)
                    ·
                      refine ⟨3620581363249324440760285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19309767270663063684054853 3620581363249324440760285)
                      ·
                        rfl

theorem cell23_7051057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_7051057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051057 prefixEnd_7051057 := by exact prefixLift 7051057
  have htrace : WordTrace (prefixWord ++ tailWord_7051057) baseStart_7051057 baseEnd_7051057 := by
    simpa [prefixWord, tailWord_7051057, baseEnd_7051057] using wordTrace_append hprefix tailTrace_7051057
  have hstable : (prefixWord ++ tailWord_7051057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051057).length < 2 ^ (prefixWord ++ tailWord_7051057).sum := by decide
  have hdescent : baseEnd_7051057 < baseStart_7051057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051061 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 1, 4, 2]
def baseStart_7051061 : Nat := 118140960795 + 7051061 * 2 ^ 59
def prefixEnd_7051061 : Nat := 4983230072969 + 3 ^ 40 * 7051061 * 2
def baseEnd_7051061 : Nat := 3620583417171942425110267

theorem tailTrace_7051061 : CollatzResearch.WordTrace tailWord_7051061 prefixEnd_7051061 3620583417171942425110267 := by
  unfold tailWord_7051061
  simp only [CollatzResearch.WordTrace]
  refine ⟨257173322308217697190633037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171448881538811798127088691 257173322308217697190633037)
  ·
    refine ⟨96439995865581636446487389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257173322308217697190633037 96439995865581636446487389)
    ·
      refine ⟨36164998449593113667432771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96439995865581636446487389 36164998449593113667432771)
      ·
        refine ⟨54247497674389670501149157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36164998449593113667432771 54247497674389670501149157)
        ·
          refine ⟨10171405813948063218965467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54247497674389670501149157 10171405813948063218965467)
          ·
            refine ⟨15257108720922094828448201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10171405813948063218965467 15257108720922094828448201)
            ·
              refine ⟨11442831540691571121336151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15257108720922094828448201 11442831540691571121336151)
              ·
                refine ⟨17164247311037356682004227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11442831540691571121336151 17164247311037356682004227)
                ·
                  refine ⟨25746370966556035023006341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17164247311037356682004227 25746370966556035023006341)
                  ·
                    refine ⟨4827444556229256566813689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25746370966556035023006341 4827444556229256566813689)
                    ·
                      refine ⟨3620583417171942425110267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4827444556229256566813689 3620583417171942425110267)
                      ·
                        rfl

theorem cell23_7051061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_7051061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051061 prefixEnd_7051061 := by exact prefixLift 7051061
  have htrace : WordTrace (prefixWord ++ tailWord_7051061) baseStart_7051061 baseEnd_7051061 := by
    simpa [prefixWord, tailWord_7051061, baseEnd_7051061] using wordTrace_append hprefix tailTrace_7051061
  have hstable : (prefixWord ++ tailWord_7051061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051061).length < 2 ^ (prefixWord ++ tailWord_7051061).sum := by decide
  have hdescent : baseEnd_7051061 < baseStart_7051061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051078 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_7051078 : Nat := 118140960795 + 7051078 * 2 ^ 59
def prefixEnd_7051078 : Nat := 4983230072969 + 3 ^ 40 * 7051078 * 2
def baseEnd_7051078 : Nat := 3620592146343068858597689

theorem tailTrace_7051078 : CollatzResearch.WordTrace tailWord_7051078 prefixEnd_7051078 3620592146343068858597689 := by
  unfold tailWord_7051078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8036685698411128409187559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 171449294899437406062667925 8036685698411128409187559)
  ·
    refine ⟨12055028547616692613781339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8036685698411128409187559 12055028547616692613781339)
    ·
      refine ⟨18082542821425038920672009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12055028547616692613781339 18082542821425038920672009)
      ·
        refine ⟨13561907116068779190504007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18082542821425038920672009 13561907116068779190504007)
        ·
          refine ⟨20342860674103168785756011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13561907116068779190504007 20342860674103168785756011)
          ·
            refine ⟨30514291011154753178634017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20342860674103168785756011 30514291011154753178634017)
            ·
              refine ⟨22885718258366064883975513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30514291011154753178634017 22885718258366064883975513)
              ·
                refine ⟨17164288693774548662981635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22885718258366064883975513 17164288693774548662981635)
                ·
                  refine ⟨25746433040661822994472453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17164288693774548662981635 25746433040661822994472453)
                  ·
                    refine ⟨4827456195124091811463585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25746433040661822994472453 4827456195124091811463585)
                    ·
                      refine ⟨3620592146343068858597689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4827456195124091811463585 3620592146343068858597689)
                      ·
                        rfl

theorem cell23_7051078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_7051078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051078 prefixEnd_7051078 := by exact prefixLift 7051078
  have htrace : WordTrace (prefixWord ++ tailWord_7051078) baseStart_7051078 baseEnd_7051078 := by
    simpa [prefixWord, tailWord_7051078, baseEnd_7051078] using wordTrace_append hprefix tailTrace_7051078
  have hstable : (prefixWord ++ tailWord_7051078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051078).length < 2 ^ (prefixWord ++ tailWord_7051078).sum := by decide
  have hdescent : baseEnd_7051078 < baseStart_7051078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051095 : List Nat := [1, 1, 3, 2, 6, 1, 1, 2, 2, 2, 2]
def baseStart_7051095 : Nat := 118140960795 + 7051095 * 2 ^ 59
def prefixEnd_7051095 : Nat := 4983230072969 + 3 ^ 40 * 7051095 * 2
def baseEnd_7051095 : Nat := 3620600875514195292085111

theorem tailTrace_7051095 : CollatzResearch.WordTrace tailWord_7051095 prefixEnd_7051095 3620600875514195292085111 := by
  unfold tailWord_7051095
  simp only [CollatzResearch.WordTrace]
  refine ⟨257174562390094520997370739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171449708260063013998247159 257174562390094520997370739)
  ·
    refine ⟨385761843585141781496056109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257174562390094520997370739 385761843585141781496056109)
    ·
      refine ⟨144660691344428168061021041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385761843585141781496056109 144660691344428168061021041)
      ·
        refine ⟨108495518508321126045765781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144660691344428168061021041 108495518508321126045765781)
        ·
          refine ⟨5085727430077552783395271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108495518508321126045765781 5085727430077552783395271)
          ·
            refine ⟨7628591145116329175092907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5085727430077552783395271 7628591145116329175092907)
            ·
              refine ⟨11442886717674493762639361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7628591145116329175092907 11442886717674493762639361)
              ·
                refine ⟨8582165038255870321979521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11442886717674493762639361 8582165038255870321979521)
                ·
                  refine ⟨6436623778691902741484641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8582165038255870321979521 6436623778691902741484641)
                  ·
                    refine ⟨4827467834018927056113481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6436623778691902741484641 4827467834018927056113481)
                    ·
                      refine ⟨3620600875514195292085111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4827467834018927056113481 3620600875514195292085111)
                      ·
                        rfl

theorem cell23_7051095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_7051095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051095 prefixEnd_7051095 := by exact prefixLift 7051095
  have htrace : WordTrace (prefixWord ++ tailWord_7051095) baseStart_7051095 baseEnd_7051095 := by
    simpa [prefixWord, tailWord_7051095, baseEnd_7051095] using wordTrace_append hprefix tailTrace_7051095
  have hstable : (prefixWord ++ tailWord_7051095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051095).length < 2 ^ (prefixWord ++ tailWord_7051095).sum := by decide
  have hdescent : baseEnd_7051095 < baseStart_7051095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051117 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_7051117 : Nat := 118140960795 + 7051117 * 2 ^ 59
def prefixEnd_7051117 : Nat := 4983230072969 + 3 ^ 40 * 7051117 * 2
def baseEnd_7051117 : Nat := 3620612172088594206010009

theorem tailTrace_7051117 : CollatzResearch.WordTrace tailWord_7051117 prefixEnd_7051117 3620612172088594206010009 := by
  unfold tailWord_7051117
  simp only [CollatzResearch.WordTrace]
  refine ⟨257175364796014818754671605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171450243197343212503114403 257175364796014818754671605)
  ·
    refine ⟨24110190449626389258250463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257175364796014818754671605 24110190449626389258250463)
    ·
      refine ⟨36165285674439583887375695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24110190449626389258250463 36165285674439583887375695)
      ·
        refine ⟨54247928511659375831063543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36165285674439583887375695 54247928511659375831063543)
        ·
          refine ⟨81371892767489063746595315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54247928511659375831063543 81371892767489063746595315)
          ·
            refine ⟨122057839151233595619892973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81371892767489063746595315 122057839151233595619892973)
            ·
              refine ⟨45771689681712598357459865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122057839151233595619892973 45771689681712598357459865)
              ·
                refine ⟨34328767261284448768094899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45771689681712598357459865 34328767261284448768094899)
                ·
                  refine ⟨51493150891926673152142349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34328767261284448768094899 51493150891926673152142349)
                  ·
                    refine ⟨19309931584472502432053381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51493150891926673152142349 19309931584472502432053381)
                    ·
                      refine ⟨3620612172088594206010009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19309931584472502432053381 3620612172088594206010009)
                      ·
                        rfl

theorem cell23_7051117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_7051117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051117 prefixEnd_7051117 := by exact prefixLift 7051117
  have htrace : WordTrace (prefixWord ++ tailWord_7051117) baseStart_7051117 baseEnd_7051117 := by
    simpa [prefixWord, tailWord_7051117, baseEnd_7051117] using wordTrace_append hprefix tailTrace_7051117
  have hstable : (prefixWord ++ tailWord_7051117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051117).length < 2 ^ (prefixWord ++ tailWord_7051117).sum := by decide
  have hdescent : baseEnd_7051117 < baseStart_7051117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051157 : List Nat := [1, 3, 2, 1, 1, 3, 2, 4, 6]
def baseStart_7051157 : Nat := 118140960795 + 7051157 * 2 ^ 59
def prefixEnd_7051157 : Nat := 4983230072969 + 3 ^ 40 * 7051157 * 2
def baseEnd_7051157 : Nat := 402292523479419338834425

theorem tailTrace_7051157 : CollatzResearch.WordTrace tailWord_7051157 prefixEnd_7051157 402292523479419338834425 := by
  unfold tailWord_7051157
  simp only [CollatzResearch.WordTrace]
  refine ⟨257176823715869905586127725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171451215810579937057418483 257176823715869905586127725)
  ·
    refine ⟨96441308893451214594797897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257176823715869905586127725 96441308893451214594797897)
    ·
      refine ⟨72330981670088410946098423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96441308893451214594797897 72330981670088410946098423)
      ·
        refine ⟨108496472505132616419147635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72330981670088410946098423 108496472505132616419147635)
        ·
          refine ⟨162744708757698924628721453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108496472505132616419147635 162744708757698924628721453)
          ·
            refine ⟨61029265784137096735770545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162744708757698924628721453 61029265784137096735770545)
            ·
              refine ⟨45771949338102822551827909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61029265784137096735770545 45771949338102822551827909)
              ·
                refine ⟨8582240500894279228467733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45771949338102822551827909 8582240500894279228467733)
                ·
                  refine ⟨402292523479419338834425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8582240500894279228467733 402292523479419338834425)
                  ·
                    rfl

theorem cell23_7051157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 6].length) (baseStart_7051157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051157 prefixEnd_7051157 := by exact prefixLift 7051157
  have htrace : WordTrace (prefixWord ++ tailWord_7051157) baseStart_7051157 baseEnd_7051157 := by
    simpa [prefixWord, tailWord_7051157, baseEnd_7051157] using wordTrace_append hprefix tailTrace_7051157
  have hstable : (prefixWord ++ tailWord_7051157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051157).length < 2 ^ (prefixWord ++ tailWord_7051157).sum := by decide
  have hdescent : baseEnd_7051157 < baseStart_7051157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051158 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_7051158 : Nat := 118140960795 + 7051158 * 2 ^ 59
def prefixEnd_7051158 : Nat := 4983230072969 + 3 ^ 40 * 7051158 * 2
def baseEnd_7051158 : Nat := 3620633224795428545597321

theorem tailTrace_7051158 : CollatzResearch.WordTrace tailWord_7051158 prefixEnd_7051158 3620633224795428545597321 := by
  unfold tailWord_7051158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16073553761804142672307133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171451240125910855171276085 16073553761804142672307133)
  ·
    refine ⟨6027582660676553502115175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16073553761804142672307133 6027582660676553502115175)
    ·
      refine ⟨9041373991014830253172763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6027582660676553502115175 9041373991014830253172763)
      ·
        refine ⟨13562060986522245379759145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9041373991014830253172763 13562060986522245379759145)
        ·
          refine ⟨10171545739891684034819359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13562060986522245379759145 10171545739891684034819359)
          ·
            refine ⟨15257318609837526052229039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10171545739891684034819359 15257318609837526052229039)
            ·
              refine ⟨22885977914756289078343559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15257318609837526052229039 22885977914756289078343559)
              ·
                refine ⟨34328966872134433617515339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22885977914756289078343559 34328966872134433617515339)
                ·
                  refine ⟨51493450308201650426273009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34328966872134433617515339 51493450308201650426273009)
                  ·
                    refine ⟨38620087731151237819704757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51493450308201650426273009 38620087731151237819704757)
                    ·
                      refine ⟨3620633224795428545597321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38620087731151237819704757 3620633224795428545597321)
                      ·
                        rfl

theorem cell23_7051158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_7051158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051158 prefixEnd_7051158 := by exact prefixLift 7051158
  have htrace : WordTrace (prefixWord ++ tailWord_7051158) baseStart_7051158 baseEnd_7051158 := by
    simpa [prefixWord, tailWord_7051158, baseEnd_7051158] using wordTrace_append hprefix tailTrace_7051158
  have hstable : (prefixWord ++ tailWord_7051158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051158).length < 2 ^ (prefixWord ++ tailWord_7051158).sum := by decide
  have hdescent : baseEnd_7051158 < baseStart_7051158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051187 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 3, 5]
def baseStart_7051187 : Nat := 118140960795 + 7051187 * 2 ^ 59
def prefixEnd_7051187 : Nat := 4983230072969 + 3 ^ 40 * 7051187 * 2
def baseEnd_7051187 : Nat := 1206882705244802977378229

theorem tailTrace_7051187 : CollatzResearch.WordTrace tailWord_7051187 prefixEnd_7051187 1206882705244802977378229 := by
  unfold tailWord_7051187
  simp only [CollatzResearch.WordTrace]
  refine ⟨257177917905761220709719815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171451945270507480473146543 257177917905761220709719815)
  ·
    refine ⟨385766876858641831064579723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257177917905761220709719815 385766876858641831064579723)
    ·
      refine ⟨578650315287962746596869585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385766876858641831064579723 578650315287962746596869585)
      ·
        refine ⟨433987736465972059947652189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578650315287962746596869585 433987736465972059947652189)
        ·
          refine ⟨162745401174739522480369571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433987736465972059947652189 162745401174739522480369571)
          ·
            refine ⟨244118101762109283720554357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162745401174739522480369571 244118101762109283720554357)
            ·
              refine ⟨22886072040197745348801971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244118101762109283720554357 22886072040197745348801971)
              ·
                refine ⟨34329108060296618023202957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22886072040197745348801971 34329108060296618023202957)
                ·
                  refine ⟨12873415522611231758701109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34329108060296618023202957 12873415522611231758701109)
                  ·
                    refine ⟨1206882705244802977378229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12873415522611231758701109 1206882705244802977378229)
                    ·
                      rfl

theorem cell23_7051187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 5].length) (baseStart_7051187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051187 prefixEnd_7051187 := by exact prefixLift 7051187
  have htrace : WordTrace (prefixWord ++ tailWord_7051187) baseStart_7051187 baseEnd_7051187 := by
    simpa [prefixWord, tailWord_7051187, baseEnd_7051187] using wordTrace_append hprefix tailTrace_7051187
  have hstable : (prefixWord ++ tailWord_7051187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051187).length < 2 ^ (prefixWord ++ tailWord_7051187).sum := by decide
  have hdescent : baseEnd_7051187 < baseStart_7051187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051268 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 4, 4]
def baseStart_7051268 : Nat := 118140960795 + 7051268 * 2 ^ 59
def prefixEnd_7051268 : Nat := 4983230072969 + 3 ^ 40 * 7051268 * 2
def baseEnd_7051268 : Nat := 1206896569222474371740605

theorem tailTrace_7051268 : CollatzResearch.WordTrace tailWord_7051268 prefixEnd_7051268 1206896569222474371740605 := by
  unfold tailWord_7051268
  simp only [CollatzResearch.WordTrace]
  refine ⟨128590436109233885771709229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171453914812311847695612305 128590436109233885771709229)
  ·
    refine ⟨48221413540962707164390961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128590436109233885771709229 48221413540962707164390961)
    ·
      refine ⟨36166060155722030373293221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48221413540962707164390961 36166060155722030373293221)
      ·
        refine ⟨6781136279197880694992479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36166060155722030373293221 6781136279197880694992479)
        ·
          refine ⟨10171704418796821042488719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6781136279197880694992479 10171704418796821042488719)
          ·
            refine ⟨15257556628195231563733079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10171704418796821042488719 15257556628195231563733079)
            ·
              refine ⟨22886334942292847345599619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15257556628195231563733079 22886334942292847345599619)
              ·
                refine ⟨34329502413439271018399429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22886334942292847345599619 34329502413439271018399429)
                ·
                  refine ⟨6436781702519863315949893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34329502413439271018399429 6436781702519863315949893)
                  ·
                    refine ⟨1206896569222474371740605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6436781702519863315949893 1206896569222474371740605)
                    ·
                      rfl

theorem cell23_7051268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_7051268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051268 prefixEnd_7051268 := by exact prefixLift 7051268
  have htrace : WordTrace (prefixWord ++ tailWord_7051268) baseStart_7051268 baseEnd_7051268 := by
    simpa [prefixWord, tailWord_7051268, baseEnd_7051268] using wordTrace_append hprefix tailTrace_7051268
  have hstable : (prefixWord ++ tailWord_7051268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051268).length < 2 ^ (prefixWord ++ tailWord_7051268).sum := by decide
  have hdescent : baseEnd_7051268 < baseStart_7051268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051307 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 4, 6]
def baseStart_7051307 : Nat := 118140960795 + 7051307 * 2 ^ 59
def prefixEnd_7051307 : Nat := 4983230072969 + 3 ^ 40 * 7051307 * 2
def baseEnd_7051307 : Nat := 1206903244470982820878045

theorem tailTrace_7051307 : CollatzResearch.WordTrace tailWord_7051307 prefixEnd_7051307 1206903244470982820878045 := by
  unfold tailWord_7051307
  simp only [CollatzResearch.WordTrace]
  refine ⟨257182294665326481204088175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171454863110217654136058783 257182294665326481204088175)
  ·
    refine ⟨385773441997989721806132263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257182294665326481204088175 385773441997989721806132263)
    ·
      refine ⟨578660162996984582709198395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385773441997989721806132263 578660162996984582709198395)
      ·
        refine ⟨867990244495476874063797593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578660162996984582709198395 867990244495476874063797593)
        ·
          refine ⟨650992683371607655547848195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 867990244495476874063797593 650992683371607655547848195)
          ·
            refine ⟨976489025057411483321772293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650992683371607655547848195 976489025057411483321772293)
            ·
              refine ⟨183091692198264653122832305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 976489025057411483321772293 183091692198264653122832305)
              ·
                refine ⟨137318769148698489842124229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183091692198264653122832305 137318769148698489842124229)
                ·
                  refine ⟨25747269215380966845398293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137318769148698489842124229 25747269215380966845398293)
                  ·
                    refine ⟨1206903244470982820878045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25747269215380966845398293 1206903244470982820878045)
                    ·
                      rfl

theorem cell23_7051307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 6].length) (baseStart_7051307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051307 prefixEnd_7051307 := by exact prefixLift 7051307
  have htrace : WordTrace (prefixWord ++ tailWord_7051307) baseStart_7051307 baseEnd_7051307 := by
    simpa [prefixWord, tailWord_7051307, baseEnd_7051307] using wordTrace_append hprefix tailTrace_7051307
  have hstable : (prefixWord ++ tailWord_7051307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051307).length < 2 ^ (prefixWord ++ tailWord_7051307).sum := by decide
  have hdescent : baseEnd_7051307 < baseStart_7051307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051347 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 7]
def baseStart_7051347 : Nat := 118140960795 + 7051347 * 2 ^ 59
def prefixEnd_7051347 : Nat := 4983230072969 + 3 ^ 40 * 7051347 * 2
def baseEnd_7051347 : Nat := 3620730272639128306133951

theorem tailTrace_7051347 : CollatzResearch.WordTrace tailWord_7051347 prefixEnd_7051347 3620730272639128306133951 := by
  unfold tailWord_7051347
  simp only [CollatzResearch.WordTrace]
  refine ⟨257183753585181568035544295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171455835723454378690362863 257183753585181568035544295)
  ·
    refine ⟨385775630377772352053316443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257183753585181568035544295 385775630377772352053316443)
    ·
      refine ⟨578663445566658528079974665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385775630377772352053316443 578663445566658528079974665)
      ·
        refine ⟨433997584174993896059980999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578663445566658528079974665 433997584174993896059980999)
        ·
          refine ⟨650996376262490844089971499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433997584174993896059980999 650996376262490844089971499)
          ·
            refine ⟨976494564393736266134957249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650996376262490844089971499 976494564393736266134957249)
            ·
              refine ⟨732370923295302199601217937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976494564393736266134957249 732370923295302199601217937)
              ·
                refine ⟨549278192471476649700913453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 732370923295302199601217937 549278192471476649700913453)
                ·
                  refine ⟨205979322176803743637842545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 549278192471476649700913453 205979322176803743637842545)
                  ·
                    refine ⟨154484491632602807728381909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 205979322176803743637842545 154484491632602807728381909)
                    ·
                      refine ⟨3620730272639128306133951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154484491632602807728381909 3620730272639128306133951)
                      ·
                        rfl

theorem cell23_7051347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_7051347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051347 prefixEnd_7051347 := by exact prefixLift 7051347
  have htrace : WordTrace (prefixWord ++ tailWord_7051347) baseStart_7051347 baseEnd_7051347 := by
    simpa [prefixWord, tailWord_7051347, baseEnd_7051347] using wordTrace_append hprefix tailTrace_7051347
  have hstable : (prefixWord ++ tailWord_7051347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051347).length < 2 ^ (prefixWord ++ tailWord_7051347).sum := by decide
  have hdescent : baseEnd_7051347 < baseStart_7051347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051382 : List Nat := [5, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2]
def baseStart_7051382 : Nat := 118140960795 + 7051382 * 2 ^ 59
def prefixEnd_7051382 : Nat := 4983230072969 + 3 ^ 40 * 7051382 * 2
def baseEnd_7051382 : Nat := 3620748244462035669196291

theorem tailTrace_7051382 : CollatzResearch.WordTrace tailWord_7051382 prefixEnd_7051382 3620748244462035669196291 := by
  unfold tailWord_7051382
  simp only [CollatzResearch.WordTrace]
  refine ⟨16074064383753423063316775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171456686760036512675378933 16074064383753423063316775)
  ·
    refine ⟨24111096575630134594975163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16074064383753423063316775 24111096575630134594975163)
    ·
      refine ⟨36166644863445201892462745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24111096575630134594975163 36166644863445201892462745)
      ·
        refine ⟨27124983647583901419347059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36166644863445201892462745 27124983647583901419347059)
        ·
          refine ⟨40687475471375852129020589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27124983647583901419347059 40687475471375852129020589)
          ·
            refine ⟨15257803301765944548382721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40687475471375852129020589 15257803301765944548382721)
            ·
              refine ⟨11443352476324458411287041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15257803301765944548382721 11443352476324458411287041)
              ·
                refine ⟨8582514357243343808465281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11443352476324458411287041 8582514357243343808465281)
                ·
                  refine ⟨6436885767932507856348961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8582514357243343808465281 6436885767932507856348961)
                  ·
                    refine ⟨4827664325949380892261721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6436885767932507856348961 4827664325949380892261721)
                    ·
                      refine ⟨3620748244462035669196291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4827664325949380892261721 3620748244462035669196291)
                      ·
                        rfl

theorem cell23_7051382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_7051382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051382 prefixEnd_7051382 := by exact prefixLift 7051382
  have htrace : WordTrace (prefixWord ++ tailWord_7051382) baseStart_7051382 baseEnd_7051382 := by
    simpa [prefixWord, tailWord_7051382, baseEnd_7051382] using wordTrace_append hprefix tailTrace_7051382
  have hstable : (prefixWord ++ tailWord_7051382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051382).length < 2 ^ (prefixWord ++ tailWord_7051382).sum := by decide
  have hdescent : baseEnd_7051382 < baseStart_7051382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051388 : List Nat := [2, 2, 2, 1, 1, 4, 4, 2, 5]
def baseStart_7051388 : Nat := 118140960795 + 7051388 * 2 ^ 59
def prefixEnd_7051388 : Nat := 4983230072969 + 3 ^ 40 * 7051388 * 2
def baseEnd_7051388 : Nat := 402305702816218071746807

theorem tailTrace_7051388 : CollatzResearch.WordTrace tailWord_7051388 prefixEnd_7051388 402305702816218071746807 := by
  unfold tailWord_7051388
  simp only [CollatzResearch.WordTrace]
  refine ⟨128592624489016516018893409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171456832652022021358524545 128592624489016516018893409)
  ·
    refine ⟨96444468366762387014170057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128592624489016516018893409 96444468366762387014170057)
    ·
      refine ⟨72333351275071790260627543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96444468366762387014170057 72333351275071790260627543)
      ·
        refine ⟨108500026912607685390941315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72333351275071790260627543 108500026912607685390941315)
        ·
          refine ⟨162750040368911528086411973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108500026912607685390941315 162750040368911528086411973)
          ·
            refine ⟨30515632569170911516202245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162750040368911528086411973 30515632569170911516202245)
            ·
              refine ⟨5721681106719545909287921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30515632569170911516202245 5721681106719545909287921)
              ·
                refine ⟨4291260830039659431965941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5721681106719545909287921 4291260830039659431965941)
                ·
                  refine ⟨402305702816218071746807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4291260830039659431965941 402305702816218071746807)
                  ·
                    rfl

theorem cell23_7051388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 5].length) (baseStart_7051388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051388 prefixEnd_7051388 := by exact prefixLift 7051388
  have htrace : WordTrace (prefixWord ++ tailWord_7051388) baseStart_7051388 baseEnd_7051388 := by
    simpa [prefixWord, tailWord_7051388, baseEnd_7051388] using wordTrace_append hprefix tailTrace_7051388
  have hstable : (prefixWord ++ tailWord_7051388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051388).length < 2 ^ (prefixWord ++ tailWord_7051388).sum := by decide
  have hdescent : baseEnd_7051388 < baseStart_7051388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051421 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_7051421 : Nat := 118140960795 + 7051421 * 2 ^ 59
def prefixEnd_7051421 : Nat := 4983230072969 + 3 ^ 40 * 7051421 * 2
def baseEnd_7051421 : Nat := 3620768270207561016608611

theorem tailTrace_7051421 : CollatzResearch.WordTrace tailWord_7051421 prefixEnd_7051421 3620768270207561016608611 := by
  unfold tailWord_7051421
  simp only [CollatzResearch.WordTrace]
  refine ⟨257186452586913478673738117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171457635057942319115825411 257186452586913478673738117)
  ·
    refine ⟨48222459860046277251325897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257186452586913478673738117 48222459860046277251325897)
    ·
      refine ⟨36166844895034707938494423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48222459860046277251325897 36166844895034707938494423)
      ·
        refine ⟨54250267342552061907741635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36166844895034707938494423 54250267342552061907741635)
        ·
          refine ⟨81375401013828092861612453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54250267342552061907741635 81375401013828092861612453)
          ·
            refine ⟨15257887690092767411552335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81375401013828092861612453 15257887690092767411552335)
            ·
              refine ⟨22886831535139151117328503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15257887690092767411552335 22886831535139151117328503)
              ·
                refine ⟨34330247302708726675992755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22886831535139151117328503 34330247302708726675992755)
                ·
                  refine ⟨51495370954063090013989133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34330247302708726675992755 51495370954063090013989133)
                  ·
                    refine ⟨19310764107773658755245925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51495370954063090013989133 19310764107773658755245925)
                    ·
                      refine ⟨3620768270207561016608611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19310764107773658755245925 3620768270207561016608611)
                      ·
                        rfl

theorem cell23_7051421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_7051421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051421 prefixEnd_7051421 := by exact prefixLift 7051421
  have htrace : WordTrace (prefixWord ++ tailWord_7051421) baseStart_7051421 baseEnd_7051421 := by
    simpa [prefixWord, tailWord_7051421, baseEnd_7051421] using wordTrace_append hprefix tailTrace_7051421
  have hstable : (prefixWord ++ tailWord_7051421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051421).length < 2 ^ (prefixWord ++ tailWord_7051421).sum := by decide
  have hdescent : baseEnd_7051421 < baseStart_7051421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051448 : List Nat := [2, 1, 2, 1, 2, 1, 3, 6, 1, 4]
def baseStart_7051448 : Nat := 118140960795 + 7051448 * 2 ^ 59
def prefixEnd_7051448 : Nat := 4983230072969 + 3 ^ 40 * 7051448 * 2
def baseEnd_7051448 : Nat := 1206927378061744136990329

theorem tailTrace_7051448 : CollatzResearch.WordTrace tailWord_7051448 prefixEnd_7051448 1206927378061744136990329 := by
  unfold tailWord_7051448
  simp only [CollatzResearch.WordTrace]
  refine ⟨128593718678907831142485499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171458291571877108189980665 128593718678907831142485499)
  ·
    refine ⟨192890578018361746713728249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128593718678907831142485499 192890578018361746713728249)
    ·
      refine ⟨144667933513771310035296187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192890578018361746713728249 144667933513771310035296187)
      ·
        refine ⟨217001900270656965052944281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144667933513771310035296187 217001900270656965052944281)
        ·
          refine ⟨162751425202992723789708211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217001900270656965052944281 162751425202992723789708211)
          ·
            refine ⟨244127137804489085684562317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162751425202992723789708211 244127137804489085684562317)
            ·
              refine ⟨91547676676683407131710869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244127137804489085684562317 91547676676683407131710869)
              ·
                refine ⟨4291297344219534709298947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91547676676683407131710869 4291297344219534709298947)
                ·
                  refine ⟨6436946016329302063948421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4291297344219534709298947 6436946016329302063948421)
                  ·
                    refine ⟨1206927378061744136990329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6436946016329302063948421 1206927378061744136990329)
                    ·
                      rfl

theorem cell23_7051448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_7051448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051448 prefixEnd_7051448 := by exact prefixLift 7051448
  have htrace : WordTrace (prefixWord ++ tailWord_7051448) baseStart_7051448 baseEnd_7051448 := by
    simpa [prefixWord, tailWord_7051448, baseEnd_7051448] using wordTrace_append hprefix tailTrace_7051448
  have hstable : (prefixWord ++ tailWord_7051448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051448).length < 2 ^ (prefixWord ++ tailWord_7051448).sum := by decide
  have hdescent : baseEnd_7051448 < baseStart_7051448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051464 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_7051464 : Nat := 118140960795 + 7051464 * 2 ^ 59
def prefixEnd_7051464 : Nat := 4983230072969 + 3 ^ 40 * 7051464 * 2
def baseEnd_7051464 : Nat := 3620790349875704348370913

theorem tailTrace_7051464 : CollatzResearch.WordTrace tailWord_7051464 prefixEnd_7051464 3620790349875704348370913 := by
  unfold tailWord_7051464
  simp only [CollatzResearch.WordTrace]
  refine ⟨128594010462878848508776723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171458680617171798011702297 128594010462878848508776723)
  ·
    refine ⟨192891015694318272763165085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128594010462878848508776723 192891015694318272763165085)
    ·
      refine ⟨72334130885369352286186907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192891015694318272763165085 72334130885369352286186907)
      ·
        refine ⟨108501196328054028429280361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72334130885369352286186907 108501196328054028429280361)
        ·
          refine ⟨81375897246040521321960271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108501196328054028429280361 81375897246040521321960271)
          ·
            refine ⟨122063845869060781982940407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81375897246040521321960271 122063845869060781982940407)
            ·
              refine ⟨183095768803591172974410611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122063845869060781982940407 183095768803591172974410611)
              ·
                refine ⟨274643653205386759461615917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183095768803591172974410611 274643653205386759461615917)
                ·
                  refine ⟨102991369952020034798105969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274643653205386759461615917 102991369952020034798105969)
                  ·
                    refine ⟨77243527464015026098579477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102991369952020034798105969 77243527464015026098579477)
                    ·
                      refine ⟨3620790349875704348370913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77243527464015026098579477 3620790349875704348370913)
                      ·
                        rfl

theorem cell23_7051464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_7051464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051464 prefixEnd_7051464 := by exact prefixLift 7051464
  have htrace : WordTrace (prefixWord ++ tailWord_7051464) baseStart_7051464 baseEnd_7051464 := by
    simpa [prefixWord, tailWord_7051464, baseEnd_7051464] using wordTrace_append hprefix tailTrace_7051464
  have hstable : (prefixWord ++ tailWord_7051464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051464).length < 2 ^ (prefixWord ++ tailWord_7051464).sum := by decide
  have hdescent : baseEnd_7051464 < baseStart_7051464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051478 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_7051478 : Nat := 118140960795 + 7051478 * 2 ^ 59
def prefixEnd_7051478 : Nat := 4983230072969 + 3 ^ 40 * 7051478 * 2
def baseEnd_7051478 : Nat := 402310837622763032621761

theorem tailTrace_7051478 : CollatzResearch.WordTrace tailWord_7051478 prefixEnd_7051478 402310837622763032621761 := by
  unfold tailWord_7051478
  simp only [CollatzResearch.WordTrace]
  refine ⟨16074283221731686088035193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171459021031804651605708725 16074283221731686088035193)
  ·
    refine ⟨12055712416298764566026395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16074283221731686088035193 12055712416298764566026395)
    ·
      refine ⟨18083568624448146849039593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12055712416298764566026395 18083568624448146849039593)
      ·
        refine ⟨13562676468336110136779695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18083568624448146849039593 13562676468336110136779695)
        ·
          refine ⟨20344014702504165205169543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13562676468336110136779695 20344014702504165205169543)
          ·
            refine ⟨30516022053756247807754315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20344014702504165205169543 30516022053756247807754315)
            ·
              refine ⟨45774033080634371711631473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30516022053756247807754315 45774033080634371711631473)
              ·
                refine ⟨34330524810475778783723605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45774033080634371711631473 34330524810475778783723605)
                ·
                  refine ⟨402310837622763032621761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34330524810475778783723605 402310837622763032621761)
                  ·
                    rfl

theorem cell23_7051478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_7051478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051478 prefixEnd_7051478 := by exact prefixLift 7051478
  have htrace : WordTrace (prefixWord ++ tailWord_7051478) baseStart_7051478 baseEnd_7051478 := by
    simpa [prefixWord, tailWord_7051478, baseEnd_7051478] using wordTrace_append hprefix tailTrace_7051478
  have hstable : (prefixWord ++ tailWord_7051478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051478).length < 2 ^ (prefixWord ++ tailWord_7051478).sum := by decide
  have hdescent : baseEnd_7051478 < baseStart_7051478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051505 : List Nat := [1, 2, 2, 2, 2, 1, 2, 6, 1, 1, 3]
def baseStart_7051505 : Nat := 118140960795 + 7051505 * 2 ^ 59
def prefixEnd_7051505 : Nat := 4983230072969 + 3 ^ 40 * 7051505 * 2
def baseEnd_7051505 : Nat := 3620811402582538687958225

theorem tailTrace_7051505 : CollatzResearch.WordTrace tailWord_7051505 prefixEnd_7051505 3620811402582538687958225 := by
  unfold tailWord_7051505
  simp only [CollatzResearch.WordTrace]
  refine ⟨257189516318609161019795969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171459677545739440679863979 257189516318609161019795969)
  ·
    refine ⟨192892137238956870764846977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257189516318609161019795969 192892137238956870764846977)
    ·
      refine ⟨144669102929217653073635233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192892137238956870764846977 144669102929217653073635233)
      ·
        refine ⟨108501827196913239805226425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144669102929217653073635233 108501827196913239805226425)
        ·
          refine ⟨81376370397684929853919819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108501827196913239805226425 81376370397684929853919819)
          ·
            refine ⟨122064555596527394780879729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81376370397684929853919819 122064555596527394780879729)
            ·
              refine ⟨91548416697395546085659797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122064555596527394780879729 91548416697395546085659797)
              ·
                refine ⟨4291332032690416222765303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91548416697395546085659797 4291332032690416222765303)
                ·
                  refine ⟨6436998049035624334147955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4291332032690416222765303 6436998049035624334147955)
                  ·
                    refine ⟨9655497073553436501221933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6436998049035624334147955 9655497073553436501221933)
                    ·
                      refine ⟨3620811402582538687958225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9655497073553436501221933 3620811402582538687958225)
                      ·
                        rfl

theorem cell23_7051505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_7051505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051505 prefixEnd_7051505 := by exact prefixLift 7051505
  have htrace : WordTrace (prefixWord ++ tailWord_7051505) baseStart_7051505 baseEnd_7051505 := by
    simpa [prefixWord, tailWord_7051505, baseEnd_7051505] using wordTrace_append hprefix tailTrace_7051505
  have hstable : (prefixWord ++ tailWord_7051505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051505).length < 2 ^ (prefixWord ++ tailWord_7051505).sum := by decide
  have hdescent : baseEnd_7051505 < baseStart_7051505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051521 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 1, 6]
def baseStart_7051521 : Nat := 118140960795 + 7051521 * 2 ^ 59
def prefixEnd_7051521 : Nat := 4983230072969 + 3 ^ 40 * 7051521 * 2
def baseEnd_7051521 : Nat := 1206939872757670208452717

theorem tailTrace_7051521 : CollatzResearch.WordTrace tailWord_7051521 prefixEnd_7051521 1206939872757670208452717 := by
  unfold tailWord_7051521
  simp only [CollatzResearch.WordTrace]
  refine ⟨257190099886551195752378417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171460066591034130501585611 257190099886551195752378417)
  ·
    refine ⟨192892574914913396814283813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257190099886551195752378417 192892574914913396814283813)
    ·
      refine ⟨36167357796546261902678215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192892574914913396814283813 36167357796546261902678215)
      ·
        refine ⟨54251036694819392854017323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36167357796546261902678215 54251036694819392854017323)
        ·
          refine ⟨81376555042229089281025985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54251036694819392854017323 81376555042229089281025985)
          ·
            refine ⟨61032416281671816960769489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81376555042229089281025985 61032416281671816960769489)
            ·
              refine ⟨45774312211253862720577117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61032416281671816960769489 45774312211253862720577117)
              ·
                refine ⟨17165367079220198520216419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45774312211253862720577117 17165367079220198520216419)
                ·
                  refine ⟨25748050618830297780324629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17165367079220198520216419 25748050618830297780324629)
                  ·
                    refine ⟨1206939872757670208452717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25748050618830297780324629 1206939872757670208452717)
                    ·
                      rfl

theorem cell23_7051521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_7051521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051521 prefixEnd_7051521 := by exact prefixLift 7051521
  have htrace : WordTrace (prefixWord ++ tailWord_7051521) baseStart_7051521 baseEnd_7051521 := by
    simpa [prefixWord, tailWord_7051521, baseEnd_7051521] using wordTrace_append hprefix tailTrace_7051521
  have hstable : (prefixWord ++ tailWord_7051521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051521).length < 2 ^ (prefixWord ++ tailWord_7051521).sum := by decide
  have hdescent : baseEnd_7051521 < baseStart_7051521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051528 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_7051528 : Nat := 118140960795 + 7051528 * 2 ^ 59
def prefixEnd_7051528 : Nat := 4983230072969 + 3 ^ 40 * 7051528 * 2
def baseEnd_7051528 : Nat := 3620823212637592097970619

theorem tailTrace_7051528 : CollatzResearch.WordTrace tailWord_7051528 prefixEnd_7051528 3620823212637592097970619 := by
  unfold tailWord_7051528
  simp only [CollatzResearch.WordTrace]
  refine ⟨128595177598762917973941619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171460236798350557298588825 128595177598762917973941619)
  ·
    refine ⟨192892766398144376960912429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128595177598762917973941619 192892766398144376960912429)
    ·
      refine ⟨72334787399304141360342161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192892766398144376960912429 72334787399304141360342161)
      ·
        refine ⟨54251090549478106020256621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72334787399304141360342161 54251090549478106020256621)
        ·
          refine ⟨20344158956054289757596233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54251090549478106020256621 20344158956054289757596233)
          ·
            refine ⟨15258119217040717318197175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20344158956054289757596233 15258119217040717318197175)
            ·
              refine ⟨22887178825561075977295763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15258119217040717318197175 22887178825561075977295763)
              ·
                refine ⟨34330768238341613965943645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22887178825561075977295763 34330768238341613965943645)
                ·
                  refine ⟨12874038089378105237228867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34330768238341613965943645 12874038089378105237228867)
                  ·
                    refine ⟨19311057134067157855843301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12874038089378105237228867 19311057134067157855843301)
                    ·
                      refine ⟨3620823212637592097970619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19311057134067157855843301 3620823212637592097970619)
                      ·
                        rfl

theorem cell23_7051528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_7051528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051528 prefixEnd_7051528 := by exact prefixLift 7051528
  have htrace : WordTrace (prefixWord ++ tailWord_7051528) baseStart_7051528 baseEnd_7051528 := by
    simpa [prefixWord, tailWord_7051528, baseEnd_7051528] using wordTrace_append hprefix tailTrace_7051528
  have hstable : (prefixWord ++ tailWord_7051528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051528).length < 2 ^ (prefixWord ++ tailWord_7051528).sum := by decide
  have hdescent : baseEnd_7051528 < baseStart_7051528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051541 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_7051541 : Nat := 118140960795 + 7051541 * 2 ^ 59
def prefixEnd_7051541 : Nat := 4983230072969 + 3 ^ 40 * 7051541 * 2
def baseEnd_7051541 : Nat := 3620829887886100547108059

theorem tailTrace_7051541 : CollatzResearch.WordTrace tailWord_7051541 prefixEnd_7051541 3620829887886100547108059 := by
  unfold tailWord_7051541
  simp only [CollatzResearch.WordTrace]
  refine ⟨257190829346478739168106477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171460552897652492778737651 257190829346478739168106477)
  ·
    refine ⟨96446561004929527188039929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257190829346478739168106477 96446561004929527188039929)
    ·
      refine ⟨72334920753697145391029947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96446561004929527188039929 72334920753697145391029947)
      ·
        refine ⟨108502381130545718086544921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72334920753697145391029947 108502381130545718086544921)
        ·
          refine ⟨81376785847909288564908691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108502381130545718086544921 81376785847909288564908691)
          ·
            refine ⟨122065178771863932847363037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81376785847909288564908691 122065178771863932847363037)
            ·
              refine ⟨45774442039448974817761139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122065178771863932847363037 45774442039448974817761139)
              ·
                refine ⟨68661663059173462226641709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45774442039448974817761139 68661663059173462226641709)
                ·
                  refine ⟨25748123647190048334990641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68661663059173462226641709 25748123647190048334990641)
                  ·
                    refine ⟨19311092735392536251242981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25748123647190048334990641 19311092735392536251242981)
                    ·
                      refine ⟨3620829887886100547108059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19311092735392536251242981 3620829887886100547108059)
                      ·
                        rfl

theorem cell23_7051541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_7051541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051541 prefixEnd_7051541 := by exact prefixLift 7051541
  have htrace : WordTrace (prefixWord ++ tailWord_7051541) baseStart_7051541 baseEnd_7051541 := by
    simpa [prefixWord, tailWord_7051541, baseEnd_7051541] using wordTrace_append hprefix tailTrace_7051541
  have hstable : (prefixWord ++ tailWord_7051541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051541).length < 2 ^ (prefixWord ++ tailWord_7051541).sum := by decide
  have hdescent : baseEnd_7051541 < baseStart_7051541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051578 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3]
def baseStart_7051578 : Nat := 118140960795 + 7051578 * 2 ^ 59
def prefixEnd_7051578 : Nat := 4983230072969 + 3 ^ 40 * 7051578 * 2
def baseEnd_7051578 : Nat := 3620848886670316902345389

theorem tailTrace_7051578 : CollatzResearch.WordTrace tailWord_7051578 prefixEnd_7051578 3620848886670316902345389 := by
  unfold tailWord_7051578
  simp only [CollatzResearch.WordTrace]
  refine ⟨64298044711836173621800847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171461452564896462991468925 64298044711836173621800847)
  ·
    refine ⟨96447067067754260432701271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64298044711836173621800847 96447067067754260432701271)
    ·
      refine ⟨144670600601631390649051907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96447067067754260432701271 144670600601631390649051907)
      ·
        refine ⟨217005900902447085973577861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144670600601631390649051907 217005900902447085973577861)
        ·
          refine ⟨40688606419208828620045849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217005900902447085973577861 40688606419208828620045849)
          ·
            refine ⟨30516454814406621465034387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40688606419208828620045849 30516454814406621465034387)
            ·
              refine ⟨45774682221609932197551581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30516454814406621465034387 45774682221609932197551581)
              ·
                refine ⟨17165505833103724574081843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45774682221609932197551581 17165505833103724574081843)
                ·
                  refine ⟨25748258749655586861122765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17165505833103724574081843 25748258749655586861122765)
                  ·
                    refine ⟨9655597031120845072921037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25748258749655586861122765 9655597031120845072921037)
                    ·
                      refine ⟨3620848886670316902345389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9655597031120845072921037 3620848886670316902345389)
                      ·
                        rfl

theorem cell23_7051578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_7051578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051578 prefixEnd_7051578 := by exact prefixLift 7051578
  have htrace : WordTrace (prefixWord ++ tailWord_7051578) baseStart_7051578 baseEnd_7051578 := by
    simpa [prefixWord, tailWord_7051578, baseEnd_7051578] using wordTrace_append hprefix tailTrace_7051578
  have hstable : (prefixWord ++ tailWord_7051578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051578).length < 2 ^ (prefixWord ++ tailWord_7051578).sum := by decide
  have hdescent : baseEnd_7051578 < baseStart_7051578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051585 : List Nat := [1, 2, 5, 2, 2, 1, 3, 7]
def baseStart_7051585 : Nat := 118140960795 + 7051585 * 2 ^ 59
def prefixEnd_7051585 : Nat := 4983230072969 + 3 ^ 40 * 7051585 * 2
def baseEnd_7051585 : Nat := 134105647445736976850291

theorem tailTrace_7051585 : CollatzResearch.WordTrace tailWord_7051585 prefixEnd_7051585 134105647445736976850291 := by
  unfold tailWord_7051585
  simp only [CollatzResearch.WordTrace]
  refine ⟨257192434158319334682708209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171461622772212889788472139 257192434158319334682708209)
  ·
    refine ⟨192894325618739501012031157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257192434158319334682708209 192894325618739501012031157)
    ·
      refine ⟨18083843026756828219877921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192894325618739501012031157 18083843026756828219877921)
      ·
        refine ⟨13562882270067621164908441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18083843026756828219877921 13562882270067621164908441)
        ·
          refine ⟨10172161702550715873681331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13562882270067621164908441 10172161702550715873681331)
          ·
            refine ⟨15258242553826073810521997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10172161702550715873681331 15258242553826073810521997)
            ·
              refine ⟨5721840957684777678945749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15258242553826073810521997 5721840957684777678945749)
              ·
                refine ⟨134105647445736976850291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5721840957684777678945749 134105647445736976850291)
                ·
                  rfl

theorem cell23_7051585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 7].length) (baseStart_7051585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051585 prefixEnd_7051585 := by exact prefixLift 7051585
  have htrace : WordTrace (prefixWord ++ tailWord_7051585) baseStart_7051585 baseEnd_7051585 := by
    simpa [prefixWord, tailWord_7051585, baseEnd_7051585] using wordTrace_append hprefix tailTrace_7051585
  have hstable : (prefixWord ++ tailWord_7051585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051585).length < 2 ^ (prefixWord ++ tailWord_7051585).sum := by decide
  have hdescent : baseEnd_7051585 < baseStart_7051585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051591 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_7051591 : Nat := 118140960795 + 7051591 * 2 ^ 59
def prefixEnd_7051591 : Nat := 4983230072969 + 3 ^ 40 * 7051591 * 2
def baseEnd_7051591 : Nat := 3620855561918825351482829

theorem tailTrace_7051591 : CollatzResearch.WordTrace tailWord_7051591 prefixEnd_7051591 3620855561918825351482829 := by
  unfold tailWord_7051591
  simp only [CollatzResearch.WordTrace]
  refine ⟨257192652996297597707426627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171461768664198398471617751 257192652996297597707426627)
  ·
    refine ⟨385788979494446396561139941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257192652996297597707426627 385788979494446396561139941)
    ·
      refine ⟨72335433655208699355213739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385788979494446396561139941 72335433655208699355213739)
      ·
        refine ⟨108503150482813049032820609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72335433655208699355213739 108503150482813049032820609)
        ·
          refine ⟨81377362862109786774615457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108503150482813049032820609 81377362862109786774615457)
          ·
            refine ⟨61033022146582340080961593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81377362862109786774615457 61033022146582340080961593)
            ·
              refine ⟨45774766609936755060721195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61033022146582340080961593 45774766609936755060721195)
              ·
                refine ⟨68662149914905132591081793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45774766609936755060721195 68662149914905132591081793)
                ·
                  refine ⟨51496612436178849443311345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68662149914905132591081793 51496612436178849443311345)
                  ·
                    refine ⟨38622459327134137082483509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51496612436178849443311345 38622459327134137082483509)
                    ·
                      refine ⟨3620855561918825351482829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38622459327134137082483509 3620855561918825351482829)
                      ·
                        rfl

theorem cell23_7051591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_7051591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051591 prefixEnd_7051591 := by exact prefixLift 7051591
  have htrace : WordTrace (prefixWord ++ tailWord_7051591) baseStart_7051591 baseEnd_7051591 := by
    simpa [prefixWord, tailWord_7051591, baseEnd_7051591] using wordTrace_append hprefix tailTrace_7051591
  have hstable : (prefixWord ++ tailWord_7051591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051591).length < 2 ^ (prefixWord ++ tailWord_7051591).sum := by decide
  have hdescent : baseEnd_7051591 < baseStart_7051591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051631 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 4]
def baseStart_7051631 : Nat := 118140960795 + 7051631 * 2 ^ 59
def prefixEnd_7051631 : Nat := 4983230072969 + 3 ^ 40 * 7051631 * 2
def baseEnd_7051631 : Nat := 3620876101145005194982645

theorem tailTrace_7051631 : CollatzResearch.WordTrace tailWord_7051631 prefixEnd_7051631 3620876101145005194982645 := by
  unfold tailWord_7051631
  simp only [CollatzResearch.WordTrace]
  refine ⟨257194111916152684538882747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171462741277435123025921831 257194111916152684538882747)
  ·
    refine ⟨385791167874229026808324121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257194111916152684538882747 385791167874229026808324121)
    ·
      refine ⟨289343375905671770106243091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385791167874229026808324121 289343375905671770106243091)
      ·
        refine ⟨434015063858507655159364637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289343375905671770106243091 434015063858507655159364637)
        ·
          refine ⟨162755648946940370684761739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434015063858507655159364637 162755648946940370684761739)
          ·
            refine ⟨244133473420410556027142609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162755648946940370684761739 244133473420410556027142609)
            ·
              refine ⟨183100105065307917020356957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244133473420410556027142609 183100105065307917020356957)
              ·
                refine ⟨68662539399490468882633859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183100105065307917020356957 68662539399490468882633859)
                ·
                  refine ⟨102993809099235703323950789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68662539399490468882633859 102993809099235703323950789)
                  ·
                    refine ⟨19311339206106694373240773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102993809099235703323950789 19311339206106694373240773)
                    ·
                      refine ⟨3620876101145005194982645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19311339206106694373240773 3620876101145005194982645)
                      ·
                        rfl

theorem cell23_7051631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_7051631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051631 prefixEnd_7051631 := by exact prefixLift 7051631
  have htrace : WordTrace (prefixWord ++ tailWord_7051631) baseStart_7051631 baseEnd_7051631 := by
    simpa [prefixWord, tailWord_7051631, baseEnd_7051631] using wordTrace_append hprefix tailTrace_7051631
  have hstable : (prefixWord ++ tailWord_7051631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051631).length < 2 ^ (prefixWord ++ tailWord_7051631).sum := by decide
  have hdescent : baseEnd_7051631 < baseStart_7051631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051690 : List Nat := [3, 1, 6, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_7051690 : Nat := 118140960795 + 7051690 * 2 ^ 59
def prefixEnd_7051690 : Nat := 4983230072969 + 3 ^ 40 * 7051690 * 2
def baseEnd_7051690 : Nat := 3620906396503620464144875

theorem tailTrace_7051690 : CollatzResearch.WordTrace tailWord_7051690 prefixEnd_7051690 3620906396503620464144875 := by
  unfold tailWord_7051690
  simp only [CollatzResearch.WordTrace]
  refine ⟨64299065955734734403820131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171464175881959291743520349 64299065955734734403820131)
  ·
    refine ⟨96448598933602101605730197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64299065955734734403820131 96448598933602101605730197)
    ·
      refine ⟨4521028075012598512768603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96448598933602101605730197 4521028075012598512768603)
      ·
        refine ⟨6781542112518897769152905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521028075012598512768603 6781542112518897769152905)
        ·
          refine ⟨5086156584389173326864679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6781542112518897769152905 5086156584389173326864679)
          ·
            refine ⟨7629234876583759990297019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5086156584389173326864679 7629234876583759990297019)
            ·
              refine ⟨11443852314875639985445529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7629234876583759990297019 11443852314875639985445529)
              ·
                refine ⟨8582889236156729989084147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11443852314875639985445529 8582889236156729989084147)
                ·
                  refine ⟨12874333854235094983626221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8582889236156729989084147 12874333854235094983626221)
                  ·
                    refine ⟨4827875195338160618859833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12874333854235094983626221 4827875195338160618859833)
                    ·
                      refine ⟨3620906396503620464144875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4827875195338160618859833 3620906396503620464144875)
                      ·
                        rfl

theorem cell23_7051690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_7051690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051690 prefixEnd_7051690 := by exact prefixLift 7051690
  have htrace : WordTrace (prefixWord ++ tailWord_7051690) baseStart_7051690 baseEnd_7051690 := by
    simpa [prefixWord, tailWord_7051690, baseEnd_7051690] using wordTrace_append hprefix tailTrace_7051690
  have hstable : (prefixWord ++ tailWord_7051690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051690).length < 2 ^ (prefixWord ++ tailWord_7051690).sum := by decide
  have hdescent : baseEnd_7051690 < baseStart_7051690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051705 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 2, 5]
def baseStart_7051705 : Nat := 118140960795 + 7051705 * 2 ^ 59
def prefixEnd_7051705 : Nat := 4983230072969 + 3 ^ 40 * 7051705 * 2
def baseEnd_7051705 : Nat := 1206971366237812635152435

theorem tailTrace_7051705 : CollatzResearch.WordTrace tailWord_7051705 prefixEnd_7051705 1206971366237812635152435 := by
  unfold tailWord_7051705
  simp only [CollatzResearch.WordTrace]
  refine ⟨257196810917884595177076569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171464540611923063451384379 257196810917884595177076569)
  ·
    refine ⟨192897608188413446382807427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257196810917884595177076569 192897608188413446382807427)
    ·
      refine ⟨289346412282620169574211141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192897608188413446382807427 289346412282620169574211141)
      ·
        refine ⟨54252452302991281795164589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289346412282620169574211141 54252452302991281795164589)
        ·
          refine ⟨20344669613621730673186721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54252452302991281795164589 20344669613621730673186721)
          ·
            refine ⟨15258502210216298004890041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20344669613621730673186721 15258502210216298004890041)
            ·
              refine ⟨11443876657662223503667531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15258502210216298004890041 11443876657662223503667531)
              ·
                refine ⟨17165814986493335255501297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11443876657662223503667531 17165814986493335255501297)
                ·
                  refine ⟨12874361239870001441625973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17165814986493335255501297 12874361239870001441625973)
                  ·
                    refine ⟨1206971366237812635152435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12874361239870001441625973 1206971366237812635152435)
                    ·
                      rfl

theorem cell23_7051705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 5].length) (baseStart_7051705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051705 prefixEnd_7051705 := by exact prefixLift 7051705
  have htrace : WordTrace (prefixWord ++ tailWord_7051705) baseStart_7051705 baseEnd_7051705 := by
    simpa [prefixWord, tailWord_7051705, baseEnd_7051705] using wordTrace_append hprefix tailTrace_7051705
  have hstable : (prefixWord ++ tailWord_7051705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051705).length < 2 ^ (prefixWord ++ tailWord_7051705).sum := by decide
  have hdescent : baseEnd_7051705 < baseStart_7051705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051711 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 9]
def baseStart_7051711 : Nat := 118140960795 + 7051711 * 2 ^ 59
def prefixEnd_7051711 : Nat := 4983230072969 + 3 ^ 40 * 7051711 * 2
def baseEnd_7051711 : Nat := 3620917179597364881982277

theorem tailTrace_7051711 : CollatzResearch.WordTrace tailWord_7051711 prefixEnd_7051711 3620917179597364881982277 := by
  unfold tailWord_7051711
  simp only [CollatzResearch.WordTrace]
  refine ⟨257197029755862858201794987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171464686503908572134529991 257197029755862858201794987)
  ·
    refine ⟨385795544633794287302692481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257197029755862858201794987 385795544633794287302692481)
    ·
      refine ⟨289346658475345715477019361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385795544633794287302692481 289346658475345715477019361)
      ·
        refine ⟨217009993856509286607764521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289346658475345715477019361 217009993856509286607764521)
        ·
          refine ⟨162757495392381964955823391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217009993856509286607764521 162757495392381964955823391)
          ·
            refine ⟨244136243088572947433735087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162757495392381964955823391 244136243088572947433735087)
            ·
              refine ⟨366204364632859421150602631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244136243088572947433735087 366204364632859421150602631)
              ·
                refine ⟨549306546949289131725903947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366204364632859421150602631 549306546949289131725903947)
                ·
                  refine ⟨823959820423933697588855921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549306546949289131725903947 823959820423933697588855921)
                  ·
                    refine ⟨617969865317950273191641941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 823959820423933697588855921 617969865317950273191641941)
                    ·
                      refine ⟨3620917179597364881982277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 617969865317950273191641941 3620917179597364881982277)
                      ·
                        rfl

theorem cell23_7051711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_7051711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051711 prefixEnd_7051711 := by exact prefixLift 7051711
  have htrace : WordTrace (prefixWord ++ tailWord_7051711) baseStart_7051711 baseEnd_7051711 := by
    simpa [prefixWord, tailWord_7051711, baseEnd_7051711] using wordTrace_append hprefix tailTrace_7051711
  have hstable : (prefixWord ++ tailWord_7051711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051711).length < 2 ^ (prefixWord ++ tailWord_7051711).sum := by decide
  have hdescent : baseEnd_7051711 < baseStart_7051711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051731 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 14]
def baseStart_7051731 : Nat := 118140960795 + 7051731 * 2 ^ 59
def prefixEnd_7051731 : Nat := 4983230072969 + 3 ^ 40 * 7051731 * 2
def baseEnd_7051731 : Nat := 402325272134494978192465

theorem tailTrace_7051731 : CollatzResearch.WordTrace tailWord_7051731 prefixEnd_7051731 402325272134494978192465 := by
  unfold tailWord_7051731
  simp only [CollatzResearch.WordTrace]
  refine ⟨257197759215790401617523047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171465172810526934411682031 257197759215790401617523047)
  ·
    refine ⟨385796638823685602426284571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257197759215790401617523047 385796638823685602426284571)
    ·
      refine ⟨578694958235528403639426857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385796638823685602426284571 578694958235528403639426857)
      ·
        refine ⟨434021218676646302729570143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578694958235528403639426857 434021218676646302729570143)
        ·
          refine ⟨651031828014969454094355215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434021218676646302729570143 651031828014969454094355215)
          ·
            refine ⟨976547742022454181141532823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651031828014969454094355215 976547742022454181141532823)
            ·
              refine ⟨1464821613033681271712299235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976547742022454181141532823 1464821613033681271712299235)
              ·
                refine ⟨2197232419550521907568448853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1464821613033681271712299235 2197232419550521907568448853)
                ·
                  refine ⟨402325272134494978192465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 14 2197232419550521907568448853 402325272134494978192465)
                  ·
                    rfl

theorem cell23_7051731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 14].length) (baseStart_7051731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051731 prefixEnd_7051731 := by exact prefixLift 7051731
  have htrace : WordTrace (prefixWord ++ tailWord_7051731) baseStart_7051731 baseEnd_7051731 := by
    simpa [prefixWord, tailWord_7051731, baseEnd_7051731] using wordTrace_append hprefix tailTrace_7051731
  have hstable : (prefixWord ++ tailWord_7051731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051731).length < 2 ^ (prefixWord ++ tailWord_7051731).sum := by decide
  have hdescent : baseEnd_7051731 < baseStart_7051731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051762 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 1, 4, 3]
def baseStart_7051762 : Nat := 118140960795 + 7051762 * 2 ^ 59
def prefixEnd_7051762 : Nat := 4983230072969 + 3 ^ 40 * 7051762 * 2
def baseEnd_7051762 : Nat := 3620943367110744182444543

theorem tailTrace_7051762 : CollatzResearch.WordTrace tailWord_7051762 prefixEnd_7051762 3620943367110744182444543 := by
  unfold tailWord_7051762
  simp only [CollatzResearch.WordTrace]
  refine ⟨64299722469669523477975385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171465926585785395941267693 64299722469669523477975385)
  ·
    refine ⟨48224791852252142608481539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64299722469669523477975385 48224791852252142608481539)
    ·
      refine ⟨72337187778378213912722309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48224791852252142608481539 72337187778378213912722309)
      ·
        refine ⟨13563222708445915108635433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72337187778378213912722309 13563222708445915108635433)
        ·
          refine ⟨10172417031334436331476575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13563222708445915108635433 10172417031334436331476575)
          ·
            refine ⟨15258625547001654497214863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10172417031334436331476575 15258625547001654497214863)
            ·
              refine ⟨22887938320502481745822295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15258625547001654497214863 22887938320502481745822295)
              ·
                refine ⟨34331907480753722618733443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22887938320502481745822295 34331907480753722618733443)
                ·
                  refine ⟨51497861221130583928100165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34331907480753722618733443 51497861221130583928100165)
                  ·
                    refine ⟨9655848978961984486518781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51497861221130583928100165 9655848978961984486518781)
                    ·
                      refine ⟨3620943367110744182444543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9655848978961984486518781 3620943367110744182444543)
                      ·
                        rfl

theorem cell23_7051762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_7051762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051762 prefixEnd_7051762 := by exact prefixLift 7051762
  have htrace : WordTrace (prefixWord ++ tailWord_7051762) baseStart_7051762 baseEnd_7051762 := by
    simpa [prefixWord, tailWord_7051762, baseEnd_7051762] using wordTrace_append hprefix tailTrace_7051762
  have hstable : (prefixWord ++ tailWord_7051762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051762).length < 2 ^ (prefixWord ++ tailWord_7051762).sum := by decide
  have hdescent : baseEnd_7051762 < baseStart_7051762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051775 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 5, 1, 3]
def baseStart_7051775 : Nat := 118140960795 + 7051775 * 2 ^ 59
def prefixEnd_7051775 : Nat := 4983230072969 + 3 ^ 40 * 7051775 * 2
def baseEnd_7051775 : Nat := 3620950042359252631581983

theorem tailTrace_7051775 : CollatzResearch.WordTrace tailWord_7051775 prefixEnd_7051775 3620950042359252631581983 := by
  unfold tailWord_7051775
  simp only [CollatzResearch.WordTrace]
  refine ⟨257199364027630997132124779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171466242685087331421416519 257199364027630997132124779)
  ·
    refine ⟨385799046041446495698187169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257199364027630997132124779 385799046041446495698187169)
    ·
      refine ⟨289349284531084871773640377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385799046041446495698187169 289349284531084871773640377)
      ·
        refine ⟨217011963398313653830230283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289349284531084871773640377 217011963398313653830230283)
        ·
          refine ⟨325517945097470480745345425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217011963398313653830230283 325517945097470480745345425)
          ·
            refine ⟨244138458823102860559009069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325517945097470480745345425 244138458823102860559009069)
            ·
              refine ⟨91551922058663572709628401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244138458823102860559009069 91551922058663572709628401)
              ·
                refine ⟨68663941543997679532221301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91551922058663572709628401 68663941543997679532221301)
                ·
                  refine ⟨6437244519749782456145747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68663941543997679532221301 6437244519749782456145747)
                  ·
                    refine ⟨9655866779624673684218621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6437244519749782456145747 9655866779624673684218621)
                    ·
                      refine ⟨3620950042359252631581983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9655866779624673684218621 3620950042359252631581983)
                      ·
                        rfl

theorem cell23_7051775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_7051775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051775 prefixEnd_7051775 := by exact prefixLift 7051775
  have htrace : WordTrace (prefixWord ++ tailWord_7051775) baseStart_7051775 baseEnd_7051775 := by
    simpa [prefixWord, tailWord_7051775, baseEnd_7051775] using wordTrace_append hprefix tailTrace_7051775
  have hstable : (prefixWord ++ tailWord_7051775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051775).length < 2 ^ (prefixWord ++ tailWord_7051775).sum := by decide
  have hdescent : baseEnd_7051775 < baseStart_7051775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051799 : List Nat := [1, 1, 3, 6, 1, 1, 3, 1, 6]
def baseStart_7051799 : Nat := 118140960795 + 7051799 * 2 ^ 59
def prefixEnd_7051799 : Nat := 4983230072969 + 3 ^ 40 * 7051799 * 2
def baseEnd_7051799 : Nat := 402329151766106726409097

theorem tailTrace_7051799 : CollatzResearch.WordTrace tailWord_7051799 prefixEnd_7051799 402329151766106726409097 := by
  unfold tailWord_7051799
  simp only [CollatzResearch.WordTrace]
  refine ⟨257200239379544049230998451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171466826253029366153998967 257200239379544049230998451)
  ·
    refine ⟨385800359069316073846497677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257200239379544049230998451 385800359069316073846497677)
    ·
      refine ⟨144675134650993527692436629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385800359069316073846497677 144675134650993527692436629)
      ·
        refine ⟨6781646936765321610582967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 144675134650993527692436629 6781646936765321610582967)
        ·
          refine ⟨10172470405147982415874451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6781646936765321610582967 10172470405147982415874451)
          ·
            refine ⟨15258705607721973623811677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10172470405147982415874451 15258705607721973623811677)
            ·
              refine ⟨5722014602895740108929379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15258705607721973623811677 5722014602895740108929379)
              ·
                refine ⟨8583021904343610163394069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5722014602895740108929379 8583021904343610163394069)
                ·
                  refine ⟨402329151766106726409097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8583021904343610163394069 402329151766106726409097)
                  ·
                    rfl

theorem cell23_7051799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 6].length) (baseStart_7051799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051799 prefixEnd_7051799 := by exact prefixLift 7051799
  have htrace : WordTrace (prefixWord ++ tailWord_7051799) baseStart_7051799 baseEnd_7051799 := by
    simpa [prefixWord, tailWord_7051799, baseEnd_7051799] using wordTrace_append hprefix tailTrace_7051799
  have hstable : (prefixWord ++ tailWord_7051799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051799).length < 2 ^ (prefixWord ++ tailWord_7051799).sum := by decide
  have hdescent : baseEnd_7051799 < baseStart_7051799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051825 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 4, 4]
def baseStart_7051825 : Nat := 118140960795 + 7051825 * 2 ^ 59
def prefixEnd_7051825 : Nat := 4983230072969 + 3 ^ 40 * 7051825 * 2
def baseEnd_7051825 : Nat := 1206991905463992478652251

theorem tailTrace_7051825 : CollatzResearch.WordTrace tailWord_7051825 prefixEnd_7051825 1206991905463992478652251 := by
  unfold tailWord_7051825
  simp only [CollatzResearch.WordTrace]
  refine ⟨257201187677449855671444929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171467458451633237114296619 257201187677449855671444929)
  ·
    refine ⟨192900890758087391753583697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257201187677449855671444929 192900890758087391753583697)
    ·
      refine ⟨144675668068565543815187773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192900890758087391753583697 144675668068565543815187773)
      ·
        refine ⟨54253375525712078930695415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144675668068565543815187773 54253375525712078930695415)
        ·
          refine ⟨81380063288568118396043123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54253375525712078930695415 81380063288568118396043123)
          ·
            refine ⟨122070094932852177594064685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81380063288568118396043123 122070094932852177594064685)
            ·
              refine ⟨45776285599819566597774257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122070094932852177594064685 45776285599819566597774257)
              ·
                refine ⟨34332214199864674948330693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45776285599819566597774257 34332214199864674948330693)
                ·
                  refine ⟨6437290162474626552812005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34332214199864674948330693 6437290162474626552812005)
                  ·
                    refine ⟨1206991905463992478652251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6437290162474626552812005 1206991905463992478652251)
                    ·
                      rfl

theorem cell23_7051825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_7051825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051825 prefixEnd_7051825 := by exact prefixLift 7051825
  have htrace : WordTrace (prefixWord ++ tailWord_7051825) baseStart_7051825 baseEnd_7051825 := by
    simpa [prefixWord, tailWord_7051825, baseEnd_7051825] using wordTrace_append hprefix tailTrace_7051825
  have hstable : (prefixWord ++ tailWord_7051825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051825).length < 2 ^ (prefixWord ++ tailWord_7051825).sum := by decide
  have hdescent : baseEnd_7051825 < baseStart_7051825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051870 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_7051870 : Nat := 118140960795 + 7051870 * 2 ^ 59
def prefixEnd_7051870 : Nat := 4983230072969 + 3 ^ 40 * 7051870 * 2
def baseEnd_7051870 : Nat := 3620998823021429759894047

theorem tailTrace_7051870 : CollatzResearch.WordTrace tailWord_7051870 prefixEnd_7051870 3620998823021429759894047 := by
  unfold tailWord_7051870
  simp only [CollatzResearch.WordTrace]
  refine ⟨32150353620285853544604133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171468552641524552237888709 32150353620285853544604133)
  ·
    refine ⟨6028191303803597539613275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32150353620285853544604133 6028191303803597539613275)
    ·
      refine ⟨9042286955705396309419913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6028191303803597539613275 9042286955705396309419913)
      ·
        refine ⟨6781715216779047232064935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9042286955705396309419913 6781715216779047232064935)
        ·
          refine ⟨10172572825168570848097403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6781715216779047232064935 10172572825168570848097403)
          ·
            refine ⟨15258859237752856272146105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10172572825168570848097403 15258859237752856272146105)
            ·
              refine ⟨11444144428314642204109579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15258859237752856272146105 11444144428314642204109579)
              ·
                refine ⟨17166216642471963306164369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11444144428314642204109579 17166216642471963306164369)
                ·
                  refine ⟨12874662481853972479623277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17166216642471963306164369 12874662481853972479623277)
                  ·
                    refine ⟨4827998430695239679858729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12874662481853972479623277 4827998430695239679858729)
                    ·
                      refine ⟨3620998823021429759894047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4827998430695239679858729 3620998823021429759894047)
                      ·
                        rfl

theorem cell23_7051870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_7051870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051870 prefixEnd_7051870 := by exact prefixLift 7051870
  have htrace : WordTrace (prefixWord ++ tailWord_7051870) baseStart_7051870 baseEnd_7051870 := by
    simpa [prefixWord, tailWord_7051870, baseEnd_7051870] using wordTrace_append hprefix tailTrace_7051870
  have hstable : (prefixWord ++ tailWord_7051870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051870).length < 2 ^ (prefixWord ++ tailWord_7051870).sum := by decide
  have hdescent : baseEnd_7051870 < baseStart_7051870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051882 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_7051882 : Nat := 118140960795 + 7051882 * 2 ^ 59
def prefixEnd_7051882 : Nat := 4983230072969 + 3 ^ 40 * 7051882 * 2
def baseEnd_7051882 : Nat := 3621004984789283712943991

theorem tailTrace_7051882 : CollatzResearch.WordTrace tailWord_7051882 prefixEnd_7051882 3621004984789283712943991 := by
  unfold tailWord_7051882
  simp only [CollatzResearch.WordTrace]
  refine ⟨64300816659560838601567475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171468844425495569604179933 64300816659560838601567475)
  ·
    refine ⟨96451224989341257902351213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64300816659560838601567475 96451224989341257902351213)
    ·
      refine ⟨36169209371002971713381705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96451224989341257902351213 36169209371002971713381705)
      ·
        refine ⟨27126907028252228785036279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36169209371002971713381705 27126907028252228785036279)
        ·
          refine ⟨40690360542378343177554419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27126907028252228785036279 40690360542378343177554419)
          ·
            refine ⟨61035540813567514766331629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40690360542378343177554419 61035540813567514766331629)
            ·
              refine ⟨22888327805087818037374361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61035540813567514766331629 22888327805087818037374361)
              ·
                refine ⟨17166245853815863528030771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22888327805087818037374361 17166245853815863528030771)
                ·
                  refine ⟨25749368780723795292046157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17166245853815863528030771 25749368780723795292046157)
                  ·
                    refine ⟨9656013292771423234517309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25749368780723795292046157 9656013292771423234517309)
                    ·
                      refine ⟨3621004984789283712943991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9656013292771423234517309 3621004984789283712943991)
                      ·
                        rfl

theorem cell23_7051882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_7051882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051882 prefixEnd_7051882 := by exact prefixLift 7051882
  have htrace : WordTrace (prefixWord ++ tailWord_7051882) baseStart_7051882 baseEnd_7051882 := by
    simpa [prefixWord, tailWord_7051882, baseEnd_7051882] using wordTrace_append hprefix tailTrace_7051882
  have hstable : (prefixWord ++ tailWord_7051882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051882).length < 2 ^ (prefixWord ++ tailWord_7051882).sum := by decide
  have hdescent : baseEnd_7051882 < baseStart_7051882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051886 : List Nat := [4, 1, 2, 2, 2, 2, 3, 1, 1, 2, 3]
def baseStart_7051886 : Nat := 118140960795 + 7051886 * 2 ^ 59
def prefixEnd_7051886 : Nat := 4983230072969 + 3 ^ 40 * 7051886 * 2
def baseEnd_7051886 : Nat := 3621007038711901697293973

theorem tailTrace_7051886 : CollatzResearch.WordTrace tailWord_7051886 prefixEnd_7051886 3621007038711901697293973 := by
  unfold tailWord_7051886
  simp only [CollatzResearch.WordTrace]
  refine ⟨32150426566278607886176939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171468941686819242059610341 32150426566278607886176939)
  ·
    refine ⟨48225639849417911829265409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32150426566278607886176939 48225639849417911829265409)
    ·
      refine ⟨36169229887063433871949057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48225639849417911829265409 36169229887063433871949057)
      ·
        refine ⟨27126922415297575403961793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36169229887063433871949057 27126922415297575403961793)
        ·
          refine ⟨20345191811473181552971345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27126922415297575403961793 20345191811473181552971345)
          ·
            refine ⟨15258893858604886164728509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20345191811473181552971345 15258893858604886164728509)
            ·
              refine ⟨5722085196976832311773191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15258893858604886164728509 5722085196976832311773191)
              ·
                refine ⟨8583127795465248467659787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5722085196976832311773191 8583127795465248467659787)
                ·
                  refine ⟨12874691693197872701489681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8583127795465248467659787 12874691693197872701489681)
                  ·
                    refine ⟨9656018769898404526117261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12874691693197872701489681 9656018769898404526117261)
                    ·
                      refine ⟨3621007038711901697293973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9656018769898404526117261 3621007038711901697293973)
                      ·
                        rfl

theorem cell23_7051886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_7051886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051886 prefixEnd_7051886 := by exact prefixLift 7051886
  have htrace : WordTrace (prefixWord ++ tailWord_7051886) baseStart_7051886 baseEnd_7051886 := by
    simpa [prefixWord, tailWord_7051886, baseEnd_7051886] using wordTrace_append hprefix tailTrace_7051886
  have hstable : (prefixWord ++ tailWord_7051886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051886).length < 2 ^ (prefixWord ++ tailWord_7051886).sum := by decide
  have hdescent : baseEnd_7051886 < baseStart_7051886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051905 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_7051905 : Nat := 118140960795 + 7051905 * 2 ^ 59
def prefixEnd_7051905 : Nat := 4983230072969 + 3 ^ 40 * 7051905 * 2
def baseEnd_7051905 : Nat := 3621016794844337122956385

theorem tailTrace_7051905 : CollatzResearch.WordTrace tailWord_7051905 prefixEnd_7051905 3621016794844337122956385 := by
  unfold tailWord_7051905
  simp only [CollatzResearch.WordTrace]
  refine ⟨257204105517160029334357169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171469403678106686222904779 257204105517160029334357169)
  ·
    refine ⟨192903079137870022000767877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257204105517160029334357169 192903079137870022000767877)
    ·
      refine ⟨36169327338350629125143977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192903079137870022000767877 36169327338350629125143977)
      ·
        refine ⟨27126995503762971843857983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36169327338350629125143977 27126995503762971843857983)
        ·
          refine ⟨40690493255644457765786975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27126995503762971843857983 40690493255644457765786975)
          ·
            refine ⟨61035739883466686648680463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40690493255644457765786975 61035739883466686648680463)
            ·
              refine ⟨91553609825200029973020695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61035739883466686648680463 91553609825200029973020695)
              ·
                refine ⟨137330414737800044959531043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91553609825200029973020695 137330414737800044959531043)
                ·
                  refine ⟨205995622106700067439296565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137330414737800044959531043 205995622106700067439296565)
                  ·
                    refine ⟨19312089572503131322434053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 205995622106700067439296565 19312089572503131322434053)
                    ·
                      refine ⟨3621016794844337122956385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19312089572503131322434053 3621016794844337122956385)
                      ·
                        rfl

theorem cell23_7051905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_7051905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051905 prefixEnd_7051905 := by exact prefixLift 7051905
  have htrace : WordTrace (prefixWord ++ tailWord_7051905) baseStart_7051905 baseEnd_7051905 := by
    simpa [prefixWord, tailWord_7051905, baseEnd_7051905] using wordTrace_append hprefix tailTrace_7051905
  have hstable : (prefixWord ++ tailWord_7051905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051905).length < 2 ^ (prefixWord ++ tailWord_7051905).sum := by decide
  have hdescent : baseEnd_7051905 < baseStart_7051905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051943 : List Nat := [1, 1, 6, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_7051943 : Nat := 118140960795 + 7051943 * 2 ^ 59
def prefixEnd_7051943 : Nat := 4983230072969 + 3 ^ 40 * 7051943 * 2
def baseEnd_7051943 : Nat := 3621036307109207974281211

theorem tailTrace_7051943 : CollatzResearch.WordTrace tailWord_7051943 prefixEnd_7051943 3621036307109207974281211 := by
  unfold tailWord_7051943
  simp only [CollatzResearch.WordTrace]
  refine ⟨257205491491022361824240483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171470327660681574549493655 257205491491022361824240483)
  ·
    refine ⟨385808237236533542736360725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257205491491022361824240483 385808237236533542736360725)
    ·
      refine ⟨18084761120462509815766909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 385808237236533542736360725 18084761120462509815766909)
      ·
        refine ⟨6781785420173441180912591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18084761120462509815766909 6781785420173441180912591)
        ·
          refine ⟨10172678130260161771368887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6781785420173441180912591 10172678130260161771368887)
          ·
            refine ⟨15259017195390242657053331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10172678130260161771368887 15259017195390242657053331)
            ·
              refine ⟨22888525793085363985579997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15259017195390242657053331 22888525793085363985579997)
              ·
                refine ⟨8583197172407011494592499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22888525793085363985579997 8583197172407011494592499)
                ·
                  refine ⟨12874795758610517241888749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8583197172407011494592499 12874795758610517241888749)
                  ·
                    refine ⟨4828048409478943965708281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12874795758610517241888749 4828048409478943965708281)
                    ·
                      refine ⟨3621036307109207974281211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4828048409478943965708281 3621036307109207974281211)
                      ·
                        rfl

theorem cell23_7051943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_7051943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051943 prefixEnd_7051943 := by exact prefixLift 7051943
  have htrace : WordTrace (prefixWord ++ tailWord_7051943) baseStart_7051943 baseEnd_7051943 := by
    simpa [prefixWord, tailWord_7051943, baseEnd_7051943] using wordTrace_append hprefix tailTrace_7051943
  have hstable : (prefixWord ++ tailWord_7051943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051943).length < 2 ^ (prefixWord ++ tailWord_7051943).sum := by decide
  have hdescent : baseEnd_7051943 < baseStart_7051943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051962 : List Nat := [3, 1, 1, 1, 2, 3, 1, 6, 5]
def baseStart_7051962 : Nat := 118140960795 + 7051962 * 2 ^ 59
def prefixEnd_7051962 : Nat := 4983230072969 + 3 ^ 40 * 7051962 * 2
def baseEnd_7051962 : Nat := 402338451471293711104847

theorem tailTrace_7051962 : CollatzResearch.WordTrace tailWord_7051962 prefixEnd_7051962 402338451471293711104847 := by
  unfold tailWord_7051962
  simp only [CollatzResearch.WordTrace]
  refine ⟨64301546119488382017295535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171470789651969018712788093 64301546119488382017295535)
  ·
    refine ⟨96452319179232573025943303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64301546119488382017295535 96452319179232573025943303)
    ·
      refine ⟨144678478768848859538914955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96452319179232573025943303 144678478768848859538914955)
      ·
        refine ⟨217017718153273289308372433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144678478768848859538914955 217017718153273289308372433)
        ·
          refine ⟨162763288614954966981279325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217017718153273289308372433 162763288614954966981279325)
          ·
            refine ⟨61036233230608112617979747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162763288614954966981279325 61036233230608112617979747)
            ·
              refine ⟨91554349845912168926969621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61036233230608112617979747 91554349845912168926969621)
              ·
                refine ⟨4291610149027132918451701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91554349845912168926969621 4291610149027132918451701)
                ·
                  refine ⟨402338451471293711104847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4291610149027132918451701 402338451471293711104847)
                  ·
                    rfl

theorem cell23_7051962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 5].length) (baseStart_7051962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051962 prefixEnd_7051962 := by exact prefixLift 7051962
  have htrace : WordTrace (prefixWord ++ tailWord_7051962) baseStart_7051962 baseEnd_7051962 := by
    simpa [prefixWord, tailWord_7051962, baseEnd_7051962] using wordTrace_append hprefix tailTrace_7051962
  have hstable : (prefixWord ++ tailWord_7051962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051962).length < 2 ^ (prefixWord ++ tailWord_7051962).sum := by decide
  have hdescent : baseEnd_7051962 < baseStart_7051962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051975 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 6, 5]
def baseStart_7051975 : Nat := 118140960795 + 7051975 * 2 ^ 59
def prefixEnd_7051975 : Nat := 4983230072969 + 3 ^ 40 * 7051975 * 2
def baseEnd_7051975 : Nat := 1207017579496717283027021

theorem tailTrace_7051975 : CollatzResearch.WordTrace tailWord_7051975 prefixEnd_7051975 1207017579496717283027021 := by
  unfold tailWord_7051975
  simp only [CollatzResearch.WordTrace]
  refine ⟨257206658626906431289405379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171471105751270954192936919 257206658626906431289405379)
  ·
    refine ⟨385809987940359646934108069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257206658626906431289405379 385809987940359646934108069)
    ·
      refine ⟨72339372738817433800145263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385809987940359646934108069 72339372738817433800145263)
      ·
        refine ⟨108509059108226150700217895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72339372738817433800145263 108509059108226150700217895)
        ·
          refine ⟨162763588662339226050326843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108509059108226150700217895 162763588662339226050326843)
          ·
            refine ⟨244145382993508839075490265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162763588662339226050326843 244145382993508839075490265)
            ·
              refine ⟨183109037245131629306617699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244145382993508839075490265 183109037245131629306617699)
              ·
                refine ⟨274663555867697443959926549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183109037245131629306617699 274663555867697443959926549)
                ·
                  refine ⟨12874854181298317685621557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 274663555867697443959926549 12874854181298317685621557)
                  ·
                    refine ⟨1207017579496717283027021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12874854181298317685621557 1207017579496717283027021)
                    ·
                      rfl

theorem cell23_7051975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_7051975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051975 prefixEnd_7051975 := by exact prefixLift 7051975
  have htrace : WordTrace (prefixWord ++ tailWord_7051975) baseStart_7051975 baseEnd_7051975 := by
    simpa [prefixWord, tailWord_7051975, baseEnd_7051975] using wordTrace_append hprefix tailTrace_7051975
  have hstable : (prefixWord ++ tailWord_7051975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051975).length < 2 ^ (prefixWord ++ tailWord_7051975).sum := by decide
  have hdescent : baseEnd_7051975 < baseStart_7051975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051996 : List Nat := [2, 2, 5, 1, 1, 1, 3, 3, 5]
def baseStart_7051996 : Nat := 118140960795 + 7051996 * 2 ^ 59
def prefixEnd_7051996 : Nat := 4983230072969 + 3 ^ 40 * 7051996 * 2
def baseEnd_7051996 : Nat := 402340391287099585213163

theorem tailTrace_7051996 : CollatzResearch.WordTrace tailWord_7051996 prefixEnd_7051996 402340391287099585213163 := by
  unfold tailWord_7051996
  simp only [CollatzResearch.WordTrace]
  refine ⟨128603712279915175937959921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171471616373220234583946561 128603712279915175937959921)
  ·
    refine ⟨96452784209936381953469941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128603712279915175937959921 96452784209936381953469941)
    ·
      refine ⟨9042448519681535808137807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96452784209936381953469941 9042448519681535808137807)
      ·
        refine ⟨13563672779522303712206711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9042448519681535808137807 13563672779522303712206711)
        ·
          refine ⟨20345509169283455568310067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13563672779522303712206711 20345509169283455568310067)
          ·
            refine ⟨30518263753925183352465101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20345509169283455568310067 30518263753925183352465101)
            ·
              refine ⟨11444348907721943757174413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30518263753925183352465101 11444348907721943757174413)
              ·
                refine ⟨4291630840395728908940405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11444348907721943757174413 4291630840395728908940405)
                ·
                  refine ⟨402340391287099585213163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4291630840395728908940405 402340391287099585213163)
                  ·
                    rfl

theorem cell23_7051996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 5].length) (baseStart_7051996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051996 prefixEnd_7051996 := by exact prefixLift 7051996
  have htrace : WordTrace (prefixWord ++ tailWord_7051996) baseStart_7051996 baseEnd_7051996 := by
    simpa [prefixWord, tailWord_7051996, baseEnd_7051996] using wordTrace_append hprefix tailTrace_7051996
  have hstable : (prefixWord ++ tailWord_7051996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051996).length < 2 ^ (prefixWord ++ tailWord_7051996).sum := by decide
  have hdescent : baseEnd_7051996 < baseStart_7051996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052025 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 6]
def baseStart_7052025 : Nat := 118140960795 + 7052025 * 2 ^ 59
def prefixEnd_7052025 : Nat := 4983230072969 + 3 ^ 40 * 7052025 * 2
def baseEnd_7052025 : Nat := 3621078412522876653455833

theorem tailTrace_7052025 : CollatzResearch.WordTrace tailWord_7052025 prefixEnd_7052025 3621078412522876653455833 := by
  unfold tailWord_7052025
  simp only [CollatzResearch.WordTrace]
  refine ⟨257208482276725289828725529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171472321517816859885817019 257208482276725289828725529)
  ·
    refine ⟨192906361707543967371544147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257208482276725289828725529 192906361707543967371544147)
    ·
      refine ⟨289359542561315951057316221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192906361707543967371544147 289359542561315951057316221)
      ·
        refine ⟨108509828460493481646493583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289359542561315951057316221 108509828460493481646493583)
        ·
          refine ⟨162764742690740222469740375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108509828460493481646493583 162764742690740222469740375)
          ·
            refine ⟨244147114036110333704610563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162764742690740222469740375 244147114036110333704610563)
            ·
              refine ⟨366220671054165500556915845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244147114036110333704610563 366220671054165500556915845)
              ·
                refine ⟨68666375822656031354421721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366220671054165500556915845 68666375822656031354421721)
                ·
                  refine ⟨51499781866992023515816291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68666375822656031354421721 51499781866992023515816291)
                  ·
                    refine ⟨77249672800488035273724437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51499781866992023515816291 77249672800488035273724437)
                    ·
                      refine ⟨3621078412522876653455833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77249672800488035273724437 3621078412522876653455833)
                      ·
                        rfl

theorem cell23_7052025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_7052025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052025 prefixEnd_7052025 := by exact prefixLift 7052025
  have htrace : WordTrace (prefixWord ++ tailWord_7052025) baseStart_7052025 baseEnd_7052025 := by
    simpa [prefixWord, tailWord_7052025, baseEnd_7052025] using wordTrace_append hprefix tailTrace_7052025
  have hstable : (prefixWord ++ tailWord_7052025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052025).length < 2 ^ (prefixWord ++ tailWord_7052025).sum := by decide
  have hdescent : baseEnd_7052025 < baseStart_7052025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052072 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_7052072 : Nat := 118140960795 + 7052072 * 2 ^ 59
def prefixEnd_7052072 : Nat := 4983230072969 + 3 ^ 40 * 7052072 * 2
def baseEnd_7052072 : Nat := 3621102546113637969568117

theorem tailTrace_7052072 : CollatzResearch.WordTrace tailWord_7052072 prefixEnd_7052072 3621102546113637969568117 := by
  unfold tailWord_7052072
  simp only [CollatzResearch.WordTrace]
  refine ⟨128605098253777508427843235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171473464338370011237124313 128605098253777508427843235)
  ·
    refine ⟨192907647380666262641764853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128605098253777508427843235 192907647380666262641764853)
    ·
      refine ⟨18085091941937462122665455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192907647380666262641764853 18085091941937462122665455)
      ·
        refine ⟨27127637912906193183998183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18085091941937462122665455 27127637912906193183998183)
        ·
          refine ⟨40691456869359289775997275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27127637912906193183998183 40691456869359289775997275)
          ·
            refine ⟨61037185304038934663995913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40691456869359289775997275 61037185304038934663995913)
            ·
              refine ⟨45777888978029200997996935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61037185304038934663995913 45777888978029200997996935)
              ·
                refine ⟨68666833467043801496995403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45777888978029200997996935 68666833467043801496995403)
                ·
                  refine ⟨103000250200565702245493105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68666833467043801496995403 103000250200565702245493105)
                  ·
                    refine ⟨77250187650424276684119829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103000250200565702245493105 77250187650424276684119829)
                    ·
                      refine ⟨3621102546113637969568117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77250187650424276684119829 3621102546113637969568117)
                      ·
                        rfl

theorem cell23_7052072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_7052072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052072 prefixEnd_7052072 := by exact prefixLift 7052072
  have htrace : WordTrace (prefixWord ++ tailWord_7052072) baseStart_7052072 baseEnd_7052072 := by
    simpa [prefixWord, tailWord_7052072, baseEnd_7052072] using wordTrace_append hprefix tailTrace_7052072
  have hstable : (prefixWord ++ tailWord_7052072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052072).length < 2 ^ (prefixWord ++ tailWord_7052072).sum := by decide
  have hdescent : baseEnd_7052072 < baseStart_7052072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052075 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 7]
def baseStart_7052075 : Nat := 118140960795 + 7052075 * 2 ^ 59
def prefixEnd_7052075 : Nat := 4983230072969 + 3 ^ 40 * 7052075 * 2
def baseEnd_7052075 : Nat := 3621104086555601457830603

theorem tailTrace_7052075 : CollatzResearch.WordTrace tailWord_7052075 prefixEnd_7052075 3621104086555601457830603 := by
  unfold tailWord_7052075
  simp only [CollatzResearch.WordTrace]
  refine ⟨257210305926544148368045679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171473537284362765578697119 257210305926544148368045679)
  ·
    refine ⟨385815458889816222552068519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257210305926544148368045679 385815458889816222552068519)
    ·
      refine ⟨578723188334724333828102779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385815458889816222552068519 578723188334724333828102779)
      ·
        refine ⟨868084782502086500742154169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578723188334724333828102779 868084782502086500742154169)
        ·
          refine ⟨651063586876564875556615627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 868084782502086500742154169 651063586876564875556615627)
          ·
            refine ⟨976595380314847313334923441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651063586876564875556615627 976595380314847313334923441)
            ·
              refine ⟨732446535236135485001192581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976595380314847313334923441 732446535236135485001192581)
              ·
                refine ⟨137333725356775403437723609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 732446535236135485001192581 137333725356775403437723609)
                ·
                  refine ⟨103000294017581552578292707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137333725356775403437723609 103000294017581552578292707)
                  ·
                    refine ⟨154500441026372328867439061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103000294017581552578292707 154500441026372328867439061)
                    ·
                      refine ⟨3621104086555601457830603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154500441026372328867439061 3621104086555601457830603)
                      ·
                        rfl

theorem cell23_7052075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 7].length) (baseStart_7052075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052075 prefixEnd_7052075 := by exact prefixLift 7052075
  have htrace : WordTrace (prefixWord ++ tailWord_7052075) baseStart_7052075 baseEnd_7052075 := by
    simpa [prefixWord, tailWord_7052075, baseEnd_7052075] using wordTrace_append hprefix tailTrace_7052075
  have hstable : (prefixWord ++ tailWord_7052075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052075).length < 2 ^ (prefixWord ++ tailWord_7052075).sum := by decide
  have hdescent : baseEnd_7052075 < baseStart_7052075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052082 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_7052082 : Nat := 118140960795 + 7052082 * 2 ^ 59
def prefixEnd_7052082 : Nat := 4983230072969 + 3 ^ 40 * 7052082 * 2
def baseEnd_7052082 : Nat := 1207035893640060976814357

theorem tailTrace_7052082 : CollatzResearch.WordTrace tailWord_7052082 prefixEnd_7052082 1207035893640060976814357 := by
  unfold tailWord_7052082
  simp only [CollatzResearch.WordTrace]
  refine ⟨64302640309379697140887625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171473707491679192375700333 64302640309379697140887625)
  ·
    refine ⟨48226980232034772855665719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64302640309379697140887625 48226980232034772855665719)
    ·
      refine ⟨72340470348052159283498579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48226980232034772855665719 72340470348052159283498579)
      ·
        refine ⟨108510705522078238925247869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72340470348052159283498579 108510705522078238925247869)
        ·
          refine ⟨40691514570779339596967951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108510705522078238925247869 40691514570779339596967951)
          ·
            refine ⟨61037271856169009395451927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40691514570779339596967951 61037271856169009395451927)
            ·
              refine ⟨91555907784253514093177891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61037271856169009395451927 91555907784253514093177891)
              ·
                refine ⟨137333861676380271139766837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91555907784253514093177891 137333861676380271139766837)
                ·
                  refine ⟨12875049532160650419353141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137333861676380271139766837 12875049532160650419353141)
                  ·
                    refine ⟨1207035893640060976814357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12875049532160650419353141 1207035893640060976814357)
                    ·
                      rfl

theorem cell23_7052082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_7052082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052082 prefixEnd_7052082 := by exact prefixLift 7052082
  have htrace : WordTrace (prefixWord ++ tailWord_7052082) baseStart_7052082 baseEnd_7052082 := by
    simpa [prefixWord, tailWord_7052082, baseEnd_7052082] using wordTrace_append hprefix tailTrace_7052082
  have hstable : (prefixWord ++ tailWord_7052082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052082).length < 2 ^ (prefixWord ++ tailWord_7052082).sum := by decide
  have hdescent : baseEnd_7052082 < baseStart_7052082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052100 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_7052100 : Nat := 118140960795 + 7052100 * 2 ^ 59
def prefixEnd_7052100 : Nat := 4983230072969 + 3 ^ 40 * 7052100 * 2
def baseEnd_7052100 : Nat := 3621116923571963860017989

theorem tailTrace_7052100 : CollatzResearch.WordTrace tailWord_7052100 prefixEnd_7052100 3621116923571963860017989 := by
  unfold tailWord_7052100
  simp only [CollatzResearch.WordTrace]
  refine ⟨128605608875726788818852877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171474145167635718425137169 128605608875726788818852877)
  ·
    refine ⟨48227103328397545807069829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128605608875726788818852877 48227103328397545807069829)
    ·
      refine ⟨9042581874074539838825593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48227103328397545807069829 9042581874074539838825593)
      ·
        refine ⟨6781936405555904879119195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9042581874074539838825593 6781936405555904879119195)
        ·
          refine ⟨10172904608333857318678793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6781936405555904879119195 10172904608333857318678793)
          ·
            refine ⟨7629678456250392989009095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10172904608333857318678793 7629678456250392989009095)
            ·
              refine ⟨11444517684375589483513643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7629678456250392989009095 11444517684375589483513643)
              ·
                refine ⟨17166776526563384225270465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11444517684375589483513643 17166776526563384225270465)
                ·
                  refine ⟨12875082394922538168952849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17166776526563384225270465 12875082394922538168952849)
                  ·
                    refine ⟨9656311796191903626714637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12875082394922538168952849 9656311796191903626714637)
                    ·
                      refine ⟨3621116923571963860017989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9656311796191903626714637 3621116923571963860017989)
                      ·
                        rfl

theorem cell23_7052100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_7052100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052100 prefixEnd_7052100 := by exact prefixLift 7052100
  have htrace : WordTrace (prefixWord ++ tailWord_7052100) baseStart_7052100 baseEnd_7052100 := by
    simpa [prefixWord, tailWord_7052100, baseEnd_7052100] using wordTrace_append hprefix tailTrace_7052100
  have hstable : (prefixWord ++ tailWord_7052100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052100).length < 2 ^ (prefixWord ++ tailWord_7052100).sum := by decide
  have hdescent : baseEnd_7052100 < baseStart_7052100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052112 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 1, 6]
def baseStart_7052112 : Nat := 118140960795 + 7052112 * 2 ^ 59
def prefixEnd_7052112 : Nat := 4983230072969 + 3 ^ 40 * 7052112 * 2
def baseEnd_7052112 : Nat := 1207041028446605937689311

theorem tailTrace_7052112 : CollatzResearch.WordTrace tailWord_7052112 prefixEnd_7052112 1207041028446605937689311 := by
  unfold tailWord_7052112
  simp only [CollatzResearch.WordTrace]
  refine ⟨128605827713705051843571295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171474436951606735791428393 128605827713705051843571295)
  ·
    refine ⟨192908741570557577765356943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128605827713705051843571295 192908741570557577765356943)
    ·
      refine ⟨289363112355836366648035415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192908741570557577765356943 289363112355836366648035415)
      ·
        refine ⟨434044668533754549972053123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289363112355836366648035415 434044668533754549972053123)
        ·
          refine ⟨651067002800631824958079685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434044668533754549972053123 651067002800631824958079685)
          ·
            refine ⟨122075063025118467179639941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 651067002800631824958079685 122075063025118467179639941)
            ·
              refine ⟨22889074317209712596182489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122075063025118467179639941 22889074317209712596182489)
              ·
                refine ⟨17166805737907284447136867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22889074317209712596182489 17166805737907284447136867)
                ·
                  refine ⟨25750208606860926670705301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17166805737907284447136867 25750208606860926670705301)
                  ·
                    refine ⟨1207041028446605937689311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25750208606860926670705301 1207041028446605937689311)
                    ·
                      rfl

theorem cell23_7052112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 1, 6].length) (baseStart_7052112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052112 prefixEnd_7052112 := by exact prefixLift 7052112
  have htrace : WordTrace (prefixWord ++ tailWord_7052112) baseStart_7052112 baseEnd_7052112 := by
    simpa [prefixWord, tailWord_7052112, baseEnd_7052112] using wordTrace_append hprefix tailTrace_7052112
  have hstable : (prefixWord ++ tailWord_7052112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052112).length < 2 ^ (prefixWord ++ tailWord_7052112).sum := by decide
  have hdescent : baseEnd_7052112 < baseStart_7052112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052116 : List Nat := [2, 4, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_7052116 : Nat := 118140960795 + 7052116 * 2 ^ 59
def prefixEnd_7052116 : Nat := 4983230072969 + 3 ^ 40 * 7052116 * 2
def baseEnd_7052116 : Nat := 1207041713087478599139305

theorem tailTrace_7052116 : CollatzResearch.WordTrace tailWord_7052116 prefixEnd_7052116 1207041713087478599139305 := by
  unfold tailWord_7052116
  simp only [CollatzResearch.WordTrace]
  refine ⟨128605900659697806185144101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171474534212930408246858801 128605900659697806185144101)
  ·
    refine ⟨24113606373693338659714519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128605900659697806185144101 24113606373693338659714519)
    ·
      refine ⟨36170409560540007989571779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24113606373693338659714519 36170409560540007989571779)
      ·
        refine ⟨54255614340810011984357669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36170409560540007989571779 54255614340810011984357669)
        ·
          refine ⟨10172927688901877247067063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54255614340810011984357669 10172927688901877247067063)
          ·
            refine ⟨15259391533352815870600595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10172927688901877247067063 15259391533352815870600595)
            ·
              refine ⟨22889087300029223805900893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15259391533352815870600595 22889087300029223805900893)
              ·
                refine ⟨8583407737510958927212835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22889087300029223805900893 8583407737510958927212835)
                ·
                  refine ⟨12875111606266438390819253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8583407737510958927212835 12875111606266438390819253)
                  ·
                    refine ⟨1207041713087478599139305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12875111606266438390819253 1207041713087478599139305)
                    ·
                      rfl

theorem cell23_7052116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_7052116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052116 prefixEnd_7052116 := by exact prefixLift 7052116
  have htrace : WordTrace (prefixWord ++ tailWord_7052116) baseStart_7052116 baseEnd_7052116 := by
    simpa [prefixWord, tailWord_7052116, baseEnd_7052116] using wordTrace_append hprefix tailTrace_7052116
  have hstable : (prefixWord ++ tailWord_7052116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052116).length < 2 ^ (prefixWord ++ tailWord_7052116).sum := by decide
  have hdescent : baseEnd_7052116 < baseStart_7052116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052129 : List Nat := [1, 2, 3, 1, 1, 1, 2, 6, 2, 4]
def baseStart_7052129 : Nat := 118140960795 + 7052129 * 2 ^ 59
def prefixEnd_7052129 : Nat := 4983230072969 + 3 ^ 40 * 7052129 * 2
def baseEnd_7052129 : Nat := 1207043938170314748851785

theorem tailTrace_7052129 : CollatzResearch.WordTrace tailWord_7052129 prefixEnd_7052129 1207043938170314748851785 := by
  unfold tailWord_7052129
  simp only [CollatzResearch.WordTrace]
  refine ⟨257212275468348515590511441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171474850312232343727007627 257212275468348515590511441)
  ·
    refine ⟨192909206601261386692883581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257212275468348515590511441 192909206601261386692883581)
    ·
      refine ⟨72340952475473020009831343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192909206601261386692883581 72340952475473020009831343)
      ·
        refine ⟨108511428713209530014747015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72340952475473020009831343 108511428713209530014747015)
        ·
          refine ⟨162767143069814295022120523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108511428713209530014747015 162767143069814295022120523)
          ·
            refine ⟨244150714604721442533180785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162767143069814295022120523 244150714604721442533180785)
            ·
              refine ⟨183113035953541081899885589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244150714604721442533180785 183113035953541081899885589)
              ·
                refine ⟨8583423560322238214057137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 183113035953541081899885589 8583423560322238214057137)
                ·
                  refine ⟨6437567670241678660542853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8583423560322238214057137 6437567670241678660542853)
                  ·
                    refine ⟨1207043938170314748851785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6437567670241678660542853 1207043938170314748851785)
                    ·
                      rfl

theorem cell23_7052129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_7052129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052129 prefixEnd_7052129 := by exact prefixLift 7052129
  have htrace : WordTrace (prefixWord ++ tailWord_7052129) baseStart_7052129 baseEnd_7052129 := by
    simpa [prefixWord, tailWord_7052129, baseEnd_7052129] using wordTrace_append hprefix tailTrace_7052129
  have hstable : (prefixWord ++ tailWord_7052129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052129).length < 2 ^ (prefixWord ++ tailWord_7052129).sum := by decide
  have hdescent : baseEnd_7052129 < baseStart_7052129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052149 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_7052149 : Nat := 118140960795 + 7052149 * 2 ^ 59
def prefixEnd_7052149 : Nat := 4983230072969 + 3 ^ 40 * 7052149 * 2
def baseEnd_7052149 : Nat := 3621142084124034168305263

theorem tailTrace_7052149 : CollatzResearch.WordTrace tailWord_7052149 prefixEnd_7052149 3621142084124034168305263 := by
  unfold tailWord_7052149
  simp only [CollatzResearch.WordTrace]
  refine ⟨257213004928276059006239501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171475336618850706004159667 257213004928276059006239501)
  ·
    refine ⟨96454876848103522127339813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257213004928276059006239501 96454876848103522127339813)
    ·
      refine ⟨18085289409019410398876215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96454876848103522127339813 18085289409019410398876215)
      ·
        refine ⟨27127934113529115598314323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18085289409019410398876215 27127934113529115598314323)
        ·
          refine ⟨40691901170293673397471485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27127934113529115598314323 40691901170293673397471485)
          ·
            refine ⟨15259462938860127524051807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40691901170293673397471485 15259462938860127524051807)
            ·
              refine ⟨22889194408290191286077711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15259462938860127524051807 22889194408290191286077711)
              ·
                refine ⟨34333791612435286929116567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22889194408290191286077711 34333791612435286929116567)
                ·
                  refine ⟨51500687418652930393674851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34333791612435286929116567 51500687418652930393674851)
                  ·
                    refine ⟨77251031127979395590512277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51500687418652930393674851 77251031127979395590512277)
                    ·
                      refine ⟨3621142084124034168305263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77251031127979395590512277 3621142084124034168305263)
                      ·
                        rfl

theorem cell23_7052149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_7052149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052149 prefixEnd_7052149 := by exact prefixLift 7052149
  have htrace : WordTrace (prefixWord ++ tailWord_7052149) baseStart_7052149 baseEnd_7052149 := by
    simpa [prefixWord, tailWord_7052149, baseEnd_7052149] using wordTrace_append hprefix tailTrace_7052149
  have hstable : (prefixWord ++ tailWord_7052149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052149).length < 2 ^ (prefixWord ++ tailWord_7052149).sum := by decide
  have hdescent : baseEnd_7052149 < baseStart_7052149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052196 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 3, 3, 2]
def baseStart_7052196 : Nat := 118140960795 + 7052196 * 2 ^ 59
def prefixEnd_7052196 : Nat := 4983230072969 + 3 ^ 40 * 7052196 * 2
def baseEnd_7052196 : Nat := 3621166217714795484417547

theorem tailTrace_7052196 : CollatzResearch.WordTrace tailWord_7052196 prefixEnd_7052196 3621166217714795484417547 := by
  unfold tailWord_7052196
  simp only [CollatzResearch.WordTrace]
  refine ⟨128607359579552893016600221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171476479439403857355466961 128607359579552893016600221)
  ·
    refine ⟨48227759842332334881225083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128607359579552893016600221 48227759842332334881225083)
    ·
      refine ⟨72341639763498502321837625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48227759842332334881225083 72341639763498502321837625)
      ·
        refine ⟨54256229822623876741378219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72341639763498502321837625 54256229822623876741378219)
        ·
          refine ⟨81384344733935815112067329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54256229822623876741378219 81384344733935815112067329)
          ·
            refine ⟨61038258550451861334050497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81384344733935815112067329 61038258550451861334050497)
            ·
              refine ⟨45778693912838896000537873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61038258550451861334050497 45778693912838896000537873)
              ·
                refine ⟨34334020434629172000403405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45778693912838896000537873 34334020434629172000403405)
                ·
                  refine ⟨12875257662985939500151277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34334020434629172000403405 12875257662985939500151277)
                  ·
                    refine ⟨4828221623619727312556729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12875257662985939500151277 4828221623619727312556729)
                    ·
                      refine ⟨3621166217714795484417547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4828221623619727312556729 3621166217714795484417547)
                      ·
                        rfl

theorem cell23_7052196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_7052196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052196 prefixEnd_7052196 := by exact prefixLift 7052196
  have htrace : WordTrace (prefixWord ++ tailWord_7052196) baseStart_7052196 baseEnd_7052196 := by
    simpa [prefixWord, tailWord_7052196, baseEnd_7052196] using wordTrace_append hprefix tailTrace_7052196
  have hstable : (prefixWord ++ tailWord_7052196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052196).length < 2 ^ (prefixWord ++ tailWord_7052196).sum := by decide
  have hdescent : baseEnd_7052196 < baseStart_7052196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052336 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 3]
def baseStart_7052336 : Nat := 118140960795 + 7052336 * 2 ^ 59
def prefixEnd_7052336 : Nat := 4983230072969 + 3 ^ 40 * 7052336 * 2
def baseEnd_7052336 : Nat := 3621238105006424936666903

theorem tailTrace_7052336 : CollatzResearch.WordTrace tailWord_7052336 prefixEnd_7052336 3621238105006424936666903 := by
  unfold tailWord_7052336
  simp only [CollatzResearch.WordTrace]
  refine ⟨128609912689299294971648431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171479883585732393295531241 128609912689299294971648431)
  ·
    refine ⟨192914869033948942457472647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128609912689299294971648431 192914869033948942457472647)
    ·
      refine ⟨289372303550923413686208971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192914869033948942457472647 289372303550923413686208971)
      ·
        refine ⟨434058455326385120529313457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289372303550923413686208971 434058455326385120529313457)
        ·
          refine ⟨325543841494788840396985093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434058455326385120529313457 325543841494788840396985093)
          ·
            refine ⟨61039470280272907574434705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 325543841494788840396985093 61039470280272907574434705)
            ·
              refine ⟨45779602710204680680826029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61039470280272907574434705 45779602710204680680826029)
              ·
                refine ⟨17167351016326755255309761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45779602710204680680826029 17167351016326755255309761)
                ·
                  refine ⟨12875513262245066441482321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17167351016326755255309761 12875513262245066441482321)
                  ·
                    refine ⟨9656634946683799831111741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12875513262245066441482321 9656634946683799831111741)
                    ·
                      refine ⟨3621238105006424936666903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9656634946683799831111741 3621238105006424936666903)
                      ·
                        rfl

theorem cell23_7052336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 3].length) (baseStart_7052336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052336 prefixEnd_7052336 := by exact prefixLift 7052336
  have htrace : WordTrace (prefixWord ++ tailWord_7052336) baseStart_7052336 baseEnd_7052336 := by
    simpa [prefixWord, tailWord_7052336, baseEnd_7052336] using wordTrace_append hprefix tailTrace_7052336
  have hstable : (prefixWord ++ tailWord_7052336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052336).length < 2 ^ (prefixWord ++ tailWord_7052336).sum := by decide
  have hdescent : baseEnd_7052336 < baseStart_7052336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052360 : List Nat := [2, 1, 3, 1, 1, 1, 7, 2, 1, 4]
def baseStart_7052360 : Nat := 118140960795 + 7052360 * 2 ^ 59
def prefixEnd_7052360 : Nat := 4983230072969 + 3 ^ 40 * 7052360 * 2
def baseEnd_7052360 : Nat := 1207083476180710947588931

theorem tailTrace_7052360 : CollatzResearch.WordTrace tailWord_7052360 prefixEnd_7052360 1207083476180710947588931 := by
  unfold tailWord_7052360
  simp only [CollatzResearch.WordTrace]
  refine ⟨128610350365255821021085267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171480467153674428028113689 128610350365255821021085267)
  ·
    refine ⟨192915525547883731531627901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128610350365255821021085267 192915525547883731531627901)
    ·
      refine ⟨72343322080456399324360463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192915525547883731531627901 72343322080456399324360463)
      ·
        refine ⟨108514983120684598986540695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72343322080456399324360463 108514983120684598986540695)
        ·
          refine ⟨162772474681026898479811043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108514983120684598986540695 162772474681026898479811043)
          ·
            refine ⟨244158712021540347719716565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162772474681026898479811043 244158712021540347719716565)
            ·
              refine ⟨5722469813004851899680857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 244158712021540347719716565 5722469813004851899680857)
              ·
                refine ⟨4291852359753638924760643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5722469813004851899680857 4291852359753638924760643)
                ·
                  refine ⟨6437778539630458387140965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4291852359753638924760643 6437778539630458387140965)
                  ·
                    refine ⟨1207083476180710947588931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6437778539630458387140965 1207083476180710947588931)
                    ·
                      rfl

theorem cell23_7052360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_7052360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052360 prefixEnd_7052360 := by exact prefixLift 7052360
  have htrace : WordTrace (prefixWord ++ tailWord_7052360) baseStart_7052360 baseEnd_7052360 := by
    simpa [prefixWord, tailWord_7052360, baseEnd_7052360] using wordTrace_append hprefix tailTrace_7052360
  have hstable : (prefixWord ++ tailWord_7052360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052360).length < 2 ^ (prefixWord ++ tailWord_7052360).sum := by decide
  have hdescent : baseEnd_7052360 < baseStart_7052360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052393 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 2, 3, 2]
def baseStart_7052393 : Nat := 118140960795 + 7052393 * 2 ^ 59
def prefixEnd_7052393 : Nat := 4983230072969 + 3 ^ 40 * 7052393 * 2
def baseEnd_7052393 : Nat := 3621267373403731213654141

theorem tailTrace_7052393 : CollatzResearch.WordTrace tailWord_7052393 prefixEnd_7052393 3621267373403731213654141 := by
  unfold tailWord_7052393
  simp only [CollatzResearch.WordTrace]
  refine ⟨257221904339392088678121833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171481269559594725785414555 257221904339392088678121833)
  ·
    refine ⟨192916428254544066508591375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257221904339392088678121833 192916428254544066508591375)
    ·
      refine ⟨289374642381816099762887063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192916428254544066508591375 289374642381816099762887063)
      ·
        refine ⟨434061963572724149644330595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289374642381816099762887063 434061963572724149644330595)
        ·
          refine ⟨651092945359086224466495893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434061963572724149644330595 651092945359086224466495893)
          ·
            refine ⟨30519981813707166771866995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 651092945359086224466495893 30519981813707166771866995)
            ·
              refine ⟨45779972720560750157800493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30519981813707166771866995 45779972720560750157800493)
              ·
                refine ⟨17167489770210281309175185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45779972720560750157800493 17167489770210281309175185)
                ·
                  refine ⟨12875617327657710981881389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17167489770210281309175185 12875617327657710981881389)
                  ·
                    refine ⟨4828356497871641618205521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12875617327657710981881389 4828356497871641618205521)
                    ·
                      refine ⟨3621267373403731213654141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4828356497871641618205521 3621267373403731213654141)
                      ·
                        rfl

theorem cell23_7052393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 3, 2].length) (baseStart_7052393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052393 prefixEnd_7052393 := by exact prefixLift 7052393
  have htrace : WordTrace (prefixWord ++ tailWord_7052393) baseStart_7052393 baseEnd_7052393 := by
    simpa [prefixWord, tailWord_7052393, baseEnd_7052393] using wordTrace_append hprefix tailTrace_7052393
  have hstable : (prefixWord ++ tailWord_7052393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052393).length < 2 ^ (prefixWord ++ tailWord_7052393).sum := by decide
  have hdescent : baseEnd_7052393 < baseStart_7052393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052400 : List Nat := [2, 1, 1, 1, 5, 1, 2, 5, 1, 1, 3]
def baseStart_7052400 : Nat := 118140960795 + 7052400 * 2 ^ 59
def prefixEnd_7052400 : Nat := 4983230072969 + 3 ^ 40 * 7052400 * 2
def baseEnd_7052400 : Nat := 3621270967768312686266609

theorem tailTrace_7052400 : CollatzResearch.WordTrace tailWord_7052400 prefixEnd_7052400 3621270967768312686266609 := by
  unfold tailWord_7052400
  simp only [CollatzResearch.WordTrace]
  refine ⟨128611079825183364436813327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171481439766911152582417769 128611079825183364436813327)
  ·
    refine ⟨192916619737775046655219991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128611079825183364436813327 192916619737775046655219991)
    ·
      refine ⟨289374929606662569982829987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192916619737775046655219991 289374929606662569982829987)
      ·
        refine ⟨434062394409993854974244981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289374929606662569982829987 434062394409993854974244981)
        ·
          refine ⟨40693349475936923903835467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 434062394409993854974244981 40693349475936923903835467)
          ·
            refine ⟨61040024213905385855753201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40693349475936923903835467 61040024213905385855753201)
            ·
              refine ⟨45780018160429039391814901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61040024213905385855753201 45780018160429039391814901)
              ·
                refine ⟨4291876702540222442982647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45780018160429039391814901 4291876702540222442982647)
                ·
                  refine ⟨6437815053810333664473971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4291876702540222442982647 6437815053810333664473971)
                  ·
                    refine ⟨9656722580715500496710957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6437815053810333664473971 9656722580715500496710957)
                    ·
                      refine ⟨3621270967768312686266609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9656722580715500496710957 3621270967768312686266609)
                      ·
                        rfl

theorem cell23_7052400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 1, 1, 3].length) (baseStart_7052400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052400 prefixEnd_7052400 := by exact prefixLift 7052400
  have htrace : WordTrace (prefixWord ++ tailWord_7052400) baseStart_7052400 baseEnd_7052400 := by
    simpa [prefixWord, tailWord_7052400, baseEnd_7052400] using wordTrace_append hprefix tailTrace_7052400
  have hstable : (prefixWord ++ tailWord_7052400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052400).length < 2 ^ (prefixWord ++ tailWord_7052400).sum := by decide
  have hdescent : baseEnd_7052400 < baseStart_7052400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052416 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 4, 4]
def baseStart_7052416 : Nat := 118140960795 + 7052416 * 2 ^ 59
def prefixEnd_7052416 : Nat := 4983230072969 + 3 ^ 40 * 7052416 * 2
def baseEnd_7052416 : Nat := 1207093061152928207888845

theorem tailTrace_7052416 : CollatzResearch.WordTrace tailWord_7052416 prefixEnd_7052416 1207093061152928207888845 := by
  unfold tailWord_7052416
  simp only [CollatzResearch.WordTrace]
  refine ⟨128611371609154381803104551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171481828812205842404139401 128611371609154381803104551)
  ·
    refine ⟨192917057413731572704656827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128611371609154381803104551 192917057413731572704656827)
    ·
      refine ⟨289375586120597359056985241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192917057413731572704656827 289375586120597359056985241)
      ·
        refine ⟨217031689590448019292738931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289375586120597359056985241 217031689590448019292738931)
        ·
          refine ⟨325547534385672028939108397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217031689590448019292738931 325547534385672028939108397)
          ·
            refine ⟨122080325394627010852165649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325547534385672028939108397 122080325394627010852165649)
            ·
              refine ⟨91560244045970258139124237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122080325394627010852165649 91560244045970258139124237)
              ·
                refine ⟨34335091517238846802171589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91560244045970258139124237 34335091517238846802171589)
                ·
                  refine ⟨6437829659482283775407173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34335091517238846802171589 6437829659482283775407173)
                  ·
                    refine ⟨1207093061152928207888845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6437829659482283775407173 1207093061152928207888845)
                    ·
                      rfl

theorem cell23_7052416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 4, 4].length) (baseStart_7052416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052416 prefixEnd_7052416 := by exact prefixLift 7052416
  have htrace : WordTrace (prefixWord ++ tailWord_7052416) baseStart_7052416 baseEnd_7052416 := by
    simpa [prefixWord, tailWord_7052416, baseEnd_7052416] using wordTrace_append hprefix tailTrace_7052416
  have hstable : (prefixWord ++ tailWord_7052416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052416).length < 2 ^ (prefixWord ++ tailWord_7052416).sum := by decide
  have hdescent : baseEnd_7052416 < baseStart_7052416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052417 : List Nat := [1, 2, 4, 2, 2, 2, 1, 4, 1, 1, 3]
def baseStart_7052417 : Nat := 118140960795 + 7052417 * 2 ^ 59
def prefixEnd_7052417 : Nat := 4983230072969 + 3 ^ 40 * 7052417 * 2
def baseEnd_7052417 : Nat := 3621279696939439119754031

theorem tailTrace_7052417 : CollatzResearch.WordTrace tailWord_7052417 prefixEnd_7052417 3621279696939439119754031 := by
  unfold tailWord_7052417
  simp only [CollatzResearch.WordTrace]
  refine ⟨257222779691305140776995505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171481853127536760517997003 257222779691305140776995505)
  ·
    refine ⟨192917084768478855582746629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257222779691305140776995505 192917084768478855582746629)
    ·
      refine ⟨36171953394089785421764993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192917084768478855582746629 36171953394089785421764993)
      ·
        refine ⟨27128965045567339066323745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36171953394089785421764993 27128965045567339066323745)
        ·
          refine ⟨20346723784175504299742809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27128965045567339066323745 20346723784175504299742809)
          ·
            refine ⟨15260042838131628224807107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20346723784175504299742809 15260042838131628224807107)
            ·
              refine ⟨22890064257197442337210661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15260042838131628224807107 22890064257197442337210661)
              ·
                refine ⟨4291887048224520438226999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22890064257197442337210661 4291887048224520438226999)
                ·
                  refine ⟨6437830572336780657340499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4291887048224520438226999 6437830572336780657340499)
                  ·
                    refine ⟨9656745858505170986010749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6437830572336780657340499 9656745858505170986010749)
                    ·
                      refine ⟨3621279696939439119754031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9656745858505170986010749 3621279696939439119754031)
                      ·
                        rfl

theorem cell23_7052417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_7052417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052417 prefixEnd_7052417 := by exact prefixLift 7052417
  have htrace : WordTrace (prefixWord ++ tailWord_7052417) baseStart_7052417 baseEnd_7052417 := by
    simpa [prefixWord, tailWord_7052417, baseEnd_7052417] using wordTrace_append hprefix tailTrace_7052417
  have hstable : (prefixWord ++ tailWord_7052417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052417).length < 2 ^ (prefixWord ++ tailWord_7052417).sum := by decide
  have hdescent : baseEnd_7052417 < baseStart_7052417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052426 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_7052426 : Nat := 118140960795 + 7052426 * 2 ^ 59
def prefixEnd_7052426 : Nat := 4983230072969 + 3 ^ 40 * 7052426 * 2
def baseEnd_7052426 : Nat := 3621284318265329584541489

theorem tailTrace_7052426 : CollatzResearch.WordTrace tailWord_7052426 prefixEnd_7052426 3621284318265329584541489 := by
  unfold tailWord_7052426
  simp only [CollatzResearch.WordTrace]
  refine ⟨64305776987068133828518283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171482071965515023542715421 64305776987068133828518283)
  ·
    refine ⟨96458665480602200742777425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64305776987068133828518283 96458665480602200742777425)
    ·
      refine ⟨72343999110451650557083069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96458665480602200742777425 72343999110451650557083069)
      ·
        refine ⟨27128999666419368958906151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72343999110451650557083069 27128999666419368958906151)
        ·
          refine ⟨40693499499629053438359227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27128999666419368958906151 40693499499629053438359227)
          ·
            refine ⟨61040249249443580157538841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40693499499629053438359227 61040249249443580157538841)
            ·
              refine ⟨45780186937082685118154131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61040249249443580157538841 45780186937082685118154131)
              ·
                refine ⟨68670280405624027677231197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45780186937082685118154131 68670280405624027677231197)
                ·
                  refine ⟨25751355152109010378961699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68670280405624027677231197 25751355152109010378961699)
                  ·
                    refine ⟨38627032728163515568442549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25751355152109010378961699 38627032728163515568442549)
                    ·
                      refine ⟨3621284318265329584541489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38627032728163515568442549 3621284318265329584541489)
                      ·
                        rfl

theorem cell23_7052426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_7052426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052426 prefixEnd_7052426 := by exact prefixLift 7052426
  have htrace : WordTrace (prefixWord ++ tailWord_7052426) baseStart_7052426 baseEnd_7052426 := by
    simpa [prefixWord, tailWord_7052426, baseEnd_7052426] using wordTrace_append hprefix tailTrace_7052426
  have hstable : (prefixWord ++ tailWord_7052426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052426).length < 2 ^ (prefixWord ++ tailWord_7052426).sum := by decide
  have hdescent : baseEnd_7052426 < baseStart_7052426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052440 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 5, 2, 2]
def baseStart_7052440 : Nat := 118140960795 + 7052440 * 2 ^ 59
def prefixEnd_7052440 : Nat := 4983230072969 + 3 ^ 40 * 7052440 * 2
def baseEnd_7052440 : Nat := 3621291506994492529766425

theorem tailTrace_7052440 : CollatzResearch.WordTrace tailWord_7052440 prefixEnd_7052440 3621291506994492529766425 := by
  unfold tailWord_7052440
  simp only [CollatzResearch.WordTrace]
  refine ⟨128611809285110907852541387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171482412380147877136721849 128611809285110907852541387)
  ·
    refine ⟨192917713927666361778812081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128611809285110907852541387 192917713927666361778812081)
    ·
      refine ⟨144688285445749771334109061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192917713927666361778812081 144688285445749771334109061)
      ·
        refine ⟨27129053521078082125145449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144688285445749771334109061 27129053521078082125145449)
        ·
          refine ⟨20346790140808561593859087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27129053521078082125145449 20346790140808561593859087)
          ·
            refine ⟨30520185211212842390788631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20346790140808561593859087 30520185211212842390788631)
            ·
              refine ⟨45780277816819263586182947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30520185211212842390788631 45780277816819263586182947)
              ·
                refine ⟨68670416725228895379274421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45780277816819263586182947 68670416725228895379274421)
                ·
                  refine ⟨6437851567990208941806977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68670416725228895379274421 6437851567990208941806977)
                  ·
                    refine ⟨4828388675992656706355233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6437851567990208941806977 4828388675992656706355233)
                    ·
                      refine ⟨3621291506994492529766425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4828388675992656706355233 3621291506994492529766425)
                      ·
                        rfl

theorem cell23_7052440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_7052440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052440 prefixEnd_7052440 := by exact prefixLift 7052440
  have htrace : WordTrace (prefixWord ++ tailWord_7052440) baseStart_7052440 baseEnd_7052440 := by
    simpa [prefixWord, tailWord_7052440, baseEnd_7052440] using wordTrace_append hprefix tailTrace_7052440
  have hstable : (prefixWord ++ tailWord_7052440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052440).length < 2 ^ (prefixWord ++ tailWord_7052440).sum := by decide
  have hdescent : baseEnd_7052440 < baseStart_7052440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052483 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 3, 3, 2]
def baseStart_7052483 : Nat := 118140960795 + 7052483 * 2 ^ 59
def prefixEnd_7052483 : Nat := 4983230072969 + 3 ^ 40 * 7052483 * 2
def baseEnd_7052483 : Nat := 3621313586662635861528727

theorem tailTrace_7052483 : CollatzResearch.WordTrace tailWord_7052483 prefixEnd_7052483 3621313586662635861528727 := by
  unfold tailWord_7052483
  simp only [CollatzResearch.WordTrace]
  refine ⟨257225186909066034048898103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171483457939377356032598735 257225186909066034048898103)
  ·
    refine ⟨385837780363599051073347155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257225186909066034048898103 385837780363599051073347155)
    ·
      refine ⟨578756670545398576610020733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385837780363599051073347155 578756670545398576610020733)
      ·
        refine ⟨217033751454524466228757775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 578756670545398576610020733 217033751454524466228757775)
        ·
          refine ⟨325550627181786699343136663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217033751454524466228757775 325550627181786699343136663)
          ·
            refine ⟨488325940772680049014704995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325550627181786699343136663 488325940772680049014704995)
            ·
              refine ⟨732488911159020073522057493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488325940772680049014704995 732488911159020073522057493)
              ·
                refine ⟨34335417710579065946346445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 732488911159020073522057493 34335417710579065946346445)
                ·
                  refine ⟨12875781641467149729879917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34335417710579065946346445 12875781641467149729879917)
                  ·
                    refine ⟨4828418115550181148704969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12875781641467149729879917 4828418115550181148704969)
                    ·
                      refine ⟨3621313586662635861528727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4828418115550181148704969 3621313586662635861528727)
                      ·
                        rfl

theorem cell23_7052483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 3, 2].length) (baseStart_7052483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052483 prefixEnd_7052483 := by exact prefixLift 7052483
  have htrace : WordTrace (prefixWord ++ tailWord_7052483) baseStart_7052483 baseEnd_7052483 := by
    simpa [prefixWord, tailWord_7052483, baseEnd_7052483] using wordTrace_append hprefix tailTrace_7052483
  have hstable : (prefixWord ++ tailWord_7052483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052483).length < 2 ^ (prefixWord ++ tailWord_7052483).sum := by decide
  have hdescent : baseEnd_7052483 < baseStart_7052483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052490 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 1, 3, 3]
def baseStart_7052490 : Nat := 118140960795 + 7052490 * 2 ^ 59
def prefixEnd_7052490 : Nat := 4983230072969 + 3 ^ 40 * 7052490 * 2
def baseEnd_7052490 : Nat := 3621317181027217334141195

theorem tailTrace_7052490 : CollatzResearch.WordTrace tailWord_7052490 prefixEnd_7052490 3621317181027217334141195 := by
  unfold tailWord_7052490
  simp only [CollatzResearch.WordTrace]
  refine ⟨64306360555010168561100731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171483628146693782829601949 64306360555010168561100731)
  ·
    refine ⟨96459540832515252841651097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64306360555010168561100731 96459540832515252841651097)
    ·
      refine ⟨72344655624386439631238323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96459540832515252841651097 72344655624386439631238323)
      ·
        refine ⟨108516983436579659446857485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72344655624386439631238323 108516983436579659446857485)
        ·
          refine ⟨40693868788717372292571557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108516983436579659446857485 40693868788717372292571557)
          ·
            refine ⟨7630100397884507304857167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40693868788717372292571557 7630100397884507304857167)
            ·
              refine ⟨11445150596826760957285751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7630100397884507304857167 11445150596826760957285751)
              ·
                refine ⟨17167725895240141435928627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11445150596826760957285751 17167725895240141435928627)
                ·
                  refine ⟨25751588842860212153892941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17167725895240141435928627 25751588842860212153892941)
                  ·
                    refine ⟨9656845816072579557709853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25751588842860212153892941 9656845816072579557709853)
                    ·
                      refine ⟨3621317181027217334141195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9656845816072579557709853 3621317181027217334141195)
                      ·
                        rfl

theorem cell23_7052490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_7052490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052490 prefixEnd_7052490 := by exact prefixLift 7052490
  have htrace : WordTrace (prefixWord ++ tailWord_7052490) baseStart_7052490 baseEnd_7052490 := by
    simpa [prefixWord, tailWord_7052490, baseEnd_7052490] using wordTrace_append hprefix tailTrace_7052490
  have hstable : (prefixWord ++ tailWord_7052490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052490).length < 2 ^ (prefixWord ++ tailWord_7052490).sum := by decide
  have hdescent : baseEnd_7052490 < baseStart_7052490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052516 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_7052516 : Nat := 118140960795 + 7052516 * 2 ^ 59
def prefixEnd_7052516 : Nat := 4983230072969 + 3 ^ 40 * 7052516 * 2
def baseEnd_7052516 : Nat := 3621330531524234232416075

theorem tailTrace_7052516 : CollatzResearch.WordTrace tailWord_7052516 prefixEnd_7052516 3621330531524234232416075 := by
  unfold tailWord_7052516
  simp only [CollatzResearch.WordTrace]
  refine ⟨128613195258973240342424701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171484260345297653789899601 128613195258973240342424701)
  ·
    refine ⟨48229948222114965128409263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128613195258973240342424701 48229948222114965128409263)
    ·
      refine ⟨72344922333172447692613895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48229948222114965128409263 72344922333172447692613895)
      ·
        refine ⟨108517383499758671538920843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72344922333172447692613895 108517383499758671538920843)
        ·
          refine ⟨162776075249638007308381265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108517383499758671538920843 162776075249638007308381265)
          ·
            refine ⟨122082056437228505481285949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162776075249638007308381265 122082056437228505481285949)
            ·
              refine ⟨45780771163960689555482231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122082056437228505481285949 45780771163960689555482231)
              ·
                refine ⟨68671156745941034333223347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45780771163960689555482231 68671156745941034333223347)
                ·
                  refine ⟨103006735118911551499835021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68671156745941034333223347 103006735118911551499835021)
                  ·
                    refine ⟨38627525669591831812438133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103006735118911551499835021 38627525669591831812438133)
                    ·
                      refine ⟨3621330531524234232416075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38627525669591831812438133 3621330531524234232416075)
                      ·
                        rfl

theorem cell23_7052516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_7052516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052516 prefixEnd_7052516 := by exact prefixLift 7052516
  have htrace : WordTrace (prefixWord ++ tailWord_7052516) baseStart_7052516 baseEnd_7052516 := by
    simpa [prefixWord, tailWord_7052516, baseEnd_7052516] using wordTrace_append hprefix tailTrace_7052516
  have hstable : (prefixWord ++ tailWord_7052516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052516).length < 2 ^ (prefixWord ++ tailWord_7052516).sum := by decide
  have hdescent : baseEnd_7052516 < baseStart_7052516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052547 : List Nat := [1, 1, 1, 3, 2, 5, 1, 3, 2, 2, 2]
def baseStart_7052547 : Nat := 118140960795 + 7052547 * 2 ^ 59
def prefixEnd_7052547 : Nat := 4983230072969 + 3 ^ 40 * 7052547 * 2
def baseEnd_7052547 : Nat := 3621346449424523611128433

theorem tailTrace_7052547 : CollatzResearch.WordTrace tailWord_7052547 prefixEnd_7052547 3621346449424523611128433 := by
  unfold tailWord_7052547
  simp only [CollatzResearch.WordTrace]
  refine ⟨257227521180834172979227895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171485014120556115319485263 257227521180834172979227895)
  ·
    refine ⟨385841281771251259468841843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257227521180834172979227895 385841281771251259468841843)
    ·
      refine ⟨578761922656876889203262765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385841281771251259468841843 578761922656876889203262765)
      ·
        refine ⟨217035720996328833451223537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 578761922656876889203262765 217035720996328833451223537)
        ·
          refine ⟨162776790747246625088417653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217035720996328833451223537 162776790747246625088417653)
          ·
            refine ⟨15260324132554371102039155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162776790747246625088417653 15260324132554371102039155)
            ·
              refine ⟨22890486198831556653058733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15260324132554371102039155 22890486198831556653058733)
              ·
                refine ⟨8583932324561833744897025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22890486198831556653058733 8583932324561833744897025)
                ·
                  refine ⟨6437949243421375308672769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8583932324561833744897025 6437949243421375308672769)
                  ·
                    refine ⟨4828461932566031481504577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6437949243421375308672769 4828461932566031481504577)
                    ·
                      refine ⟨3621346449424523611128433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4828461932566031481504577 3621346449424523611128433)
                      ·
                        rfl

theorem cell23_7052547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 2, 2].length) (baseStart_7052547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052547 prefixEnd_7052547 := by exact prefixLift 7052547
  have htrace : WordTrace (prefixWord ++ tailWord_7052547) baseStart_7052547 baseEnd_7052547 := by
    simpa [prefixWord, tailWord_7052547, baseEnd_7052547] using wordTrace_append hprefix tailTrace_7052547
  have hstable : (prefixWord ++ tailWord_7052547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052547).length < 2 ^ (prefixWord ++ tailWord_7052547).sum := by decide
  have hdescent : baseEnd_7052547 < baseStart_7052547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052593 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 1, 2, 5]
def baseStart_7052593 : Nat := 118140960795 + 7052593 * 2 ^ 59
def prefixEnd_7052593 : Nat := 4983230072969 + 3 ^ 40 * 7052593 * 2
def baseEnd_7052593 : Nat := 3621370069534630431153221

theorem tailTrace_7052593 : CollatzResearch.WordTrace tailWord_7052593 prefixEnd_7052593 3621370069534630431153221 := by
  unfold tailWord_7052593
  simp only [CollatzResearch.WordTrace]
  refine ⟨257229198938667522835402433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171486132625778348556934955 257229198938667522835402433)
  ·
    refine ⟨192921899204000642126551825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257229198938667522835402433 192921899204000642126551825)
    ·
      refine ⟨144691424403000481594913869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192921899204000642126551825 144691424403000481594913869)
      ·
        refine ⟨54259284151125180598092701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144691424403000481594913869 54259284151125180598092701)
        ·
          refine ⟨20347231556671942724284763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54259284151125180598092701 20347231556671942724284763)
          ·
            refine ⟨30520847335007914086427145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20347231556671942724284763 30520847335007914086427145)
            ·
              refine ⟨22890635501255935564820359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30520847335007914086427145 22890635501255935564820359)
              ·
                refine ⟨34335953251883903347230539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22890635501255935564820359 34335953251883903347230539)
                ·
                  refine ⟨51503929877825855020845809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34335953251883903347230539 51503929877825855020845809)
                  ·
                    refine ⟨38627947408369391265634357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51503929877825855020845809 38627947408369391265634357)
                    ·
                      refine ⟨3621370069534630431153221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38627947408369391265634357 3621370069534630431153221)
                      ·
                        rfl

theorem cell23_7052593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_7052593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052593 prefixEnd_7052593 := by exact prefixLift 7052593
  have htrace : WordTrace (prefixWord ++ tailWord_7052593) baseStart_7052593 baseEnd_7052593 := by
    simpa [prefixWord, tailWord_7052593, baseEnd_7052593] using wordTrace_append hprefix tailTrace_7052593
  have hstable : (prefixWord ++ tailWord_7052593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052593).length < 2 ^ (prefixWord ++ tailWord_7052593).sum := by decide
  have hdescent : baseEnd_7052593 < baseStart_7052593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052620 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 2, 1, 4]
def baseStart_7052620 : Nat := 118140960795 + 7052620 * 2 ^ 59
def prefixEnd_7052620 : Nat := 4983230072969 + 3 ^ 40 * 7052620 * 2
def baseEnd_7052620 : Nat := 3621383933512301825515597

theorem tailTrace_7052620 : CollatzResearch.WordTrace tailWord_7052620 prefixEnd_7052620 3621383933512301825515597 := by
  unfold tailWord_7052620
  simp only [CollatzResearch.WordTrace]
  refine ⟨128615091854784853223317657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171486789139713137631090209 128615091854784853223317657)
  ·
    refine ⟨96461318891088639917488243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128615091854784853223317657 96461318891088639917488243)
    ·
      refine ⟨144691978336632959876232365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96461318891088639917488243 144691978336632959876232365)
      ·
        refine ⟨54259491876237359953587137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144691978336632959876232365 54259491876237359953587137)
        ·
          refine ⟨40694618907178019965190353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54259491876237359953587137 40694618907178019965190353)
          ·
            refine ⟨30520964180383514973892765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40694618907178019965190353 30520964180383514973892765)
            ·
              refine ⟨11445361567643818115209787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30520964180383514973892765 11445361567643818115209787)
              ·
                refine ⟨17168042351465727172814681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11445361567643818115209787 17168042351465727172814681)
                ·
                  refine ⟨12876031763599295379611011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17168042351465727172814681 12876031763599295379611011)
                  ·
                    refine ⟨19314047645398943069416517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12876031763599295379611011 19314047645398943069416517)
                    ·
                      refine ⟨3621383933512301825515597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19314047645398943069416517 3621383933512301825515597)
                      ·
                        rfl

theorem cell23_7052620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_7052620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052620 prefixEnd_7052620 := by exact prefixLift 7052620
  have htrace : WordTrace (prefixWord ++ tailWord_7052620) baseStart_7052620 baseEnd_7052620 := by
    simpa [prefixWord, tailWord_7052620, baseEnd_7052620] using wordTrace_append hprefix tailTrace_7052620
  have hstable : (prefixWord ++ tailWord_7052620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052620).length < 2 ^ (prefixWord ++ tailWord_7052620).sum := by decide
  have hdescent : baseEnd_7052620 < baseStart_7052620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052643 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 8]
def baseStart_7052643 : Nat := 118140960795 + 7052643 * 2 ^ 59
def prefixEnd_7052643 : Nat := 4983230072969 + 3 ^ 40 * 7052643 * 2
def baseEnd_7052643 : Nat := 402377304840817248391999

theorem tailTrace_7052643 : CollatzResearch.WordTrace tailWord_7052643 prefixEnd_7052643 402377304840817248391999 := by
  unfold tailWord_7052643
  simp only [CollatzResearch.WordTrace]
  refine ⟨257231022588486381374722583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171487348392324254249815055 257231022588486381374722583)
  ·
    refine ⟨385846533882729572062083875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257231022588486381374722583 385846533882729572062083875)
    ·
      refine ⟨578769800824094358093125813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385846533882729572062083875 578769800824094358093125813)
      ·
        refine ⟨54259668827258846071230545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 578769800824094358093125813 54259668827258846071230545)
        ·
          refine ⟨40694751620444134553422909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54259668827258846071230545 40694751620444134553422909)
          ·
            refine ⟨15260531857666550457533591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40694751620444134553422909 15260531857666550457533591)
            ·
              refine ⟨22890797786499825686300387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15260531857666550457533591 22890797786499825686300387)
              ·
                refine ⟨34336196679749738529450581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22890797786499825686300387 34336196679749738529450581)
                ·
                  refine ⟨402377304840817248391999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34336196679749738529450581 402377304840817248391999)
                  ·
                    rfl

theorem cell23_7052643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 8].length) (baseStart_7052643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052643 prefixEnd_7052643 := by exact prefixLift 7052643
  have htrace : WordTrace (prefixWord ++ tailWord_7052643) baseStart_7052643 baseEnd_7052643 := by
    simpa [prefixWord, tailWord_7052643, baseEnd_7052643] using wordTrace_append hprefix tailTrace_7052643
  have hstable : (prefixWord ++ tailWord_7052643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052643).length < 2 ^ (prefixWord ++ tailWord_7052643).sum := by decide
  have hdescent : baseEnd_7052643 < baseStart_7052643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052647 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 3, 4]
def baseStart_7052647 : Nat := 118140960795 + 7052647 * 2 ^ 59
def prefixEnd_7052647 : Nat := 4983230072969 + 3 ^ 40 * 7052647 * 2
def baseEnd_7052647 : Nat := 1207132599163324406625991

theorem tailTrace_7052647 : CollatzResearch.WordTrace tailWord_7052647 prefixEnd_7052647 1207132599163324406625991 := by
  unfold tailWord_7052647
  simp only [CollatzResearch.WordTrace]
  refine ⟨257231168480471890057868195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171487445653647926705245463 257231168480471890057868195)
  ·
    refine ⟨385846752720707835086802293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257231168480471890057868195 385846752720707835086802293)
    ·
      refine ⟨36173133067566359539387715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 385846752720707835086802293 36173133067566359539387715)
      ·
        refine ⟨54259699601349539309081573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36173133067566359539387715 54259699601349539309081573)
        ·
          refine ⟨10173693675253038620452795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54259699601349539309081573 10173693675253038620452795)
          ·
            refine ⟨15260540512879557930679193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10173693675253038620452795 15260540512879557930679193)
            ·
              refine ⟨11445405384659668448009395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15260540512879557930679193 11445405384659668448009395)
              ·
                refine ⟨17168108076989502672014093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11445405384659668448009395 17168108076989502672014093)
                ·
                  refine ⟨6438040528871063502005285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17168108076989502672014093 6438040528871063502005285)
                  ·
                    refine ⟨1207132599163324406625991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6438040528871063502005285 1207132599163324406625991)
                    ·
                      rfl

theorem cell23_7052647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_7052647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052647 prefixEnd_7052647 := by exact prefixLift 7052647
  have htrace : WordTrace (prefixWord ++ tailWord_7052647) baseStart_7052647 baseEnd_7052647 := by
    simpa [prefixWord, tailWord_7052647, baseEnd_7052647] using wordTrace_append hprefix tailTrace_7052647
  have hstable : (prefixWord ++ tailWord_7052647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052647).length < 2 ^ (prefixWord ++ tailWord_7052647).sum := by decide
  have hdescent : baseEnd_7052647 < baseStart_7052647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052681 : List Nat := [1, 2, 1, 1, 8, 1, 1, 3, 1, 4]
def baseStart_7052681 : Nat := 118140960795 + 7052681 * 2 ^ 59
def prefixEnd_7052681 : Nat := 4983230072969 + 3 ^ 40 * 7052681 * 2
def baseEnd_7052681 : Nat := 1207138418610742028950939

theorem tailTrace_7052681 : CollatzResearch.WordTrace tailWord_7052681 prefixEnd_7052681 1207138418610742028950939 := by
  unfold tailWord_7052681
  simp only [CollatzResearch.WordTrace]
  refine ⟨257232408562348713864605897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171488272374899142576403931 257232408562348713864605897)
  ·
    refine ⟨192924306421761535398454423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257232408562348713864605897 192924306421761535398454423)
    ·
      refine ⟨289386459632642303097681635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192924306421761535398454423 289386459632642303097681635)
      ·
        refine ⟨434079689448963454646522453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289386459632642303097681635 434079689448963454646522453)
        ·
          refine ⟨5086871360730040484138935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 434079689448963454646522453 5086871360730040484138935)
          ·
            refine ⟨7630307041095060726208403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5086871360730040484138935 7630307041095060726208403)
            ·
              refine ⟨11445460561642591089312605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7630307041095060726208403 11445460561642591089312605)
              ·
                refine ⟨4292047710615971658492227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11445460561642591089312605 4292047710615971658492227)
                ·
                  refine ⟨6438071565923957487738341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4292047710615971658492227 6438071565923957487738341)
                  ·
                    refine ⟨1207138418610742028950939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6438071565923957487738341 1207138418610742028950939)
                    ·
                      rfl

theorem cell23_7052681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 1, 4].length) (baseStart_7052681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052681 prefixEnd_7052681 := by exact prefixLift 7052681
  have htrace : WordTrace (prefixWord ++ tailWord_7052681) baseStart_7052681 baseEnd_7052681 := by
    simpa [prefixWord, tailWord_7052681, baseEnd_7052681] using wordTrace_append hprefix tailTrace_7052681
  have hstable : (prefixWord ++ tailWord_7052681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052681).length < 2 ^ (prefixWord ++ tailWord_7052681).sum := by decide
  have hdescent : baseEnd_7052681 < baseStart_7052681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052697 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 2, 3, 2]
def baseStart_7052697 : Nat := 118140960795 + 7052697 * 2 ^ 59
def prefixEnd_7052697 : Nat := 4983230072969 + 3 ^ 40 * 7052697 * 2
def baseEnd_7052697 : Nat := 3621423471522698024252743

theorem tailTrace_7052697 : CollatzResearch.WordTrace tailWord_7052697 prefixEnd_7052697 3621423471522698024252743 := by
  unfold tailWord_7052697
  simp only [CollatzResearch.WordTrace]
  refine ⟨257232992130290748597188345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171488661420193832398125563 257232992130290748597188345)
  ·
    refine ⟨192924744097718061447891259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257232992130290748597188345 192924744097718061447891259)
    ·
      refine ⟨289387116146577092171836889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192924744097718061447891259 289387116146577092171836889)
      ·
        refine ⟨217040337109932819128877667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289387116146577092171836889 217040337109932819128877667)
        ·
          refine ⟨325560505664899228693316501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217040337109932819128877667 325560505664899228693316501)
          ·
            refine ⟨15260648703042151344999211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 325560505664899228693316501 15260648703042151344999211)
            ·
              refine ⟨22890973054563227017498817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15260648703042151344999211 22890973054563227017498817)
              ·
                refine ⟨17168229790922420263124113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22890973054563227017498817 17168229790922420263124113)
                ·
                  refine ⟨12876172343191815197343085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17168229790922420263124113 12876172343191815197343085)
                  ·
                    refine ⟨4828564628696930699003657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12876172343191815197343085 4828564628696930699003657)
                    ·
                      refine ⟨3621423471522698024252743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4828564628696930699003657 3621423471522698024252743)
                      ·
                        rfl

theorem cell23_7052697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 3, 2].length) (baseStart_7052697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052697 prefixEnd_7052697 := by exact prefixLift 7052697
  have htrace : WordTrace (prefixWord ++ tailWord_7052697) baseStart_7052697 baseEnd_7052697 := by
    simpa [prefixWord, tailWord_7052697, baseEnd_7052697] using wordTrace_append hprefix tailTrace_7052697
  have hstable : (prefixWord ++ tailWord_7052697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052697).length < 2 ^ (prefixWord ++ tailWord_7052697).sum := by decide
  have hdescent : baseEnd_7052697 < baseStart_7052697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052713 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 1, 8, 3]
def baseStart_7052713 : Nat := 118140960795 + 7052713 * 2 ^ 59
def prefixEnd_7052713 : Nat := 4983230072969 + 3 ^ 40 * 7052713 * 2
def baseEnd_7052713 : Nat := 3621431687213169961652669

theorem tailTrace_7052713 : CollatzResearch.WordTrace tailWord_7052713 prefixEnd_7052713 3621431687213169961652669 := by
  unfold tailWord_7052713
  simp only [CollatzResearch.WordTrace]
  refine ⟨257233575698232783329770793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171489050465488522219847195 257233575698232783329770793)
  ·
    refine ⟨192925181773674587497328095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257233575698232783329770793 192925181773674587497328095)
    ·
      refine ⟨289387772660511881245992143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192925181773674587497328095 289387772660511881245992143)
      ·
        refine ⟨434081658990767821868988215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289387772660511881245992143 434081658990767821868988215)
        ·
          refine ⟨651122488486151732803482323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434081658990767821868988215 651122488486151732803482323)
          ·
            refine ⟨976683732729227599205223485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651122488486151732803482323 976683732729227599205223485)
            ·
              refine ⟨366256399773460349701958807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 976683732729227599205223485 366256399773460349701958807)
              ·
                refine ⟨549384599660190524552938211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366256399773460349701958807 549384599660190524552938211)
                ·
                  refine ⟨824076899490285786829407317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549384599660190524552938211 824076899490285786829407317)
                  ·
                    refine ⟨9657151165901786564407117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 824076899490285786829407317 9657151165901786564407117)
                    ·
                      refine ⟨3621431687213169961652669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9657151165901786564407117 3621431687213169961652669)
                      ·
                        rfl

theorem cell23_7052713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 8, 3].length) (baseStart_7052713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052713 prefixEnd_7052713 := by exact prefixLift 7052713
  have htrace : WordTrace (prefixWord ++ tailWord_7052713) baseStart_7052713 baseEnd_7052713 := by
    simpa [prefixWord, tailWord_7052713, baseEnd_7052713] using wordTrace_append hprefix tailTrace_7052713
  have hstable : (prefixWord ++ tailWord_7052713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052713).length < 2 ^ (prefixWord ++ tailWord_7052713).sum := by decide
  have hdescent : baseEnd_7052713 < baseStart_7052713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052723 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 4]
def baseStart_7052723 : Nat := 118140960795 + 7052723 * 2 ^ 59
def prefixEnd_7052723 : Nat := 4983230072969 + 3 ^ 40 * 7052723 * 2
def baseEnd_7052723 : Nat := 3621436822019714922527623

theorem tailTrace_7052723 : CollatzResearch.WordTrace tailWord_7052723 prefixEnd_7052723 3621436822019714922527623 := by
  unfold tailWord_7052723
  simp only [CollatzResearch.WordTrace]
  refine ⟨257233940428196555037634823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171489293618797703358423215 257233940428196555037634823)
  ·
    refine ⟨385850910642294832556452235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257233940428196555037634823 385850910642294832556452235)
    ·
      refine ⟨578776365963442248834678353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385850910642294832556452235 578776365963442248834678353)
      ·
        refine ⟨434082274472581686626008765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578776365963442248834678353 434082274472581686626008765)
        ·
          refine ⟨162780852927218132484753287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434082274472581686626008765 162780852927218132484753287)
          ·
            refine ⟨244171279390827198727129931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162780852927218132484753287 244171279390827198727129931)
            ·
              refine ⟨366256919086240798090694897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244171279390827198727129931 366256919086240798090694897)
              ·
                refine ⟨274692689314680598568021173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366256919086240798090694897 274692689314680598568021173)
                ·
                  refine ⟨25752439623251306115751985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 274692689314680598568021173 25752439623251306115751985)
                  ·
                    refine ⟨19314329717438479586813989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25752439623251306115751985 19314329717438479586813989)
                    ·
                      refine ⟨3621436822019714922527623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19314329717438479586813989 3621436822019714922527623)
                      ·
                        rfl

theorem cell23_7052723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_7052723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052723 prefixEnd_7052723 := by exact prefixLift 7052723
  have htrace : WordTrace (prefixWord ++ tailWord_7052723) baseStart_7052723 baseEnd_7052723 := by
    simpa [prefixWord, tailWord_7052723, baseEnd_7052723] using wordTrace_append hprefix tailTrace_7052723
  have hstable : (prefixWord ++ tailWord_7052723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052723).length < 2 ^ (prefixWord ++ tailWord_7052723).sum := by decide
  have hdescent : baseEnd_7052723 < baseStart_7052723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052727 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 5, 2, 2]
def baseStart_7052727 : Nat := 118140960795 + 7052727 * 2 ^ 59
def prefixEnd_7052727 : Nat := 4983230072969 + 3 ^ 40 * 7052727 * 2
def baseEnd_7052727 : Nat := 3621438875942332906877605

theorem tailTrace_7052727 : CollatzResearch.WordTrace tailWord_7052727 prefixEnd_7052727 3621438875942332906877605 := by
  unfold tailWord_7052727
  simp only [CollatzResearch.WordTrace]
  refine ⟨257234086320182063720780435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171489390880121375813853623 257234086320182063720780435)
  ·
    refine ⟨385851129480273095581170653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257234086320182063720780435 385851129480273095581170653)
    ·
      refine ⟨144694173555102410842938995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385851129480273095581170653 144694173555102410842938995)
      ·
        refine ⟨217041260332653616264408493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144694173555102410842938995 217041260332653616264408493)
        ·
          refine ⟨81390472624745106099153185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217041260332653616264408493 81390472624745106099153185)
          ·
            refine ⟨61042854468558829574364889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81390472624745106099153185 61042854468558829574364889)
            ·
              refine ⟨45782140851419122180773667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61042854468558829574364889 45782140851419122180773667)
              ·
                refine ⟨68673211277128683271160501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45782140851419122180773667 68673211277128683271160501)
                ·
                  refine ⟨6438113557230814056671297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68673211277128683271160501 6438113557230814056671297)
                  ·
                    refine ⟨4828585167923110542503473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6438113557230814056671297 4828585167923110542503473)
                    ·
                      refine ⟨3621438875942332906877605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4828585167923110542503473 3621438875942332906877605)
                      ·
                        rfl

theorem cell23_7052727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 2, 2].length) (baseStart_7052727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052727 prefixEnd_7052727 := by exact prefixLift 7052727
  have htrace : WordTrace (prefixWord ++ tailWord_7052727) baseStart_7052727 baseEnd_7052727 := by
    simpa [prefixWord, tailWord_7052727, baseEnd_7052727] using wordTrace_append hprefix tailTrace_7052727
  have hstable : (prefixWord ++ tailWord_7052727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052727).length < 2 ^ (prefixWord ++ tailWord_7052727).sum := by decide
  have hdescent : baseEnd_7052727 < baseStart_7052727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052733 : List Nat := [1, 4, 1, 2, 2, 1, 1, 11]
def baseStart_7052733 : Nat := 118140960795 + 7052733 * 2 ^ 59
def prefixEnd_7052733 : Nat := 4983230072969 + 3 ^ 40 * 7052733 * 2
def baseEnd_7052733 : Nat := 134127479882454069755651

theorem tailTrace_7052733 : CollatzResearch.WordTrace tailWord_7052733 prefixEnd_7052733 134127479882454069755651 := by
  unfold tailWord_7052733
  simp only [CollatzResearch.WordTrace]
  refine ⟨257234305158160326745498853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171489536772106884496999235 257234305158160326745498853)
  ·
    refine ⟨48231432217155061264781035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257234305158160326745498853 48231432217155061264781035)
    ·
      refine ⟨72347148325732591897171553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48231432217155061264781035 72347148325732591897171553)
      ·
        refine ⟨54260361244299443922878665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72347148325732591897171553 54260361244299443922878665)
        ·
          refine ⟨40695270933224582942158999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54260361244299443922878665 40695270933224582942158999)
          ·
            refine ⟨61042906399836874413238499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40695270933224582942158999 61042906399836874413238499)
            ·
              refine ⟨91564359599755311619857749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61042906399836874413238499 91564359599755311619857749)
              ·
                refine ⟨134127479882454069755651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 91564359599755311619857749 134127479882454069755651)
                ·
                  rfl

theorem cell23_7052733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 11].length) (baseStart_7052733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052733 prefixEnd_7052733 := by exact prefixLift 7052733
  have htrace : WordTrace (prefixWord ++ tailWord_7052733) baseStart_7052733 baseEnd_7052733 := by
    simpa [prefixWord, tailWord_7052733, baseEnd_7052733] using wordTrace_append hprefix tailTrace_7052733
  have hstable : (prefixWord ++ tailWord_7052733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052733).length < 2 ^ (prefixWord ++ tailWord_7052733).sum := by decide
  have hdescent : baseEnd_7052733 < baseStart_7052733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052761 : List Nat := [1, 2, 1, 2, 4, 3, 1, 4, 1, 2, 2]
def baseStart_7052761 : Nat := 118140960795 + 7052761 * 2 ^ 59
def prefixEnd_7052761 : Nat := 4983230072969 + 3 ^ 40 * 7052761 * 2
def baseEnd_7052761 : Nat := 3621456334284585773852449

theorem tailTrace_7052761 : CollatzResearch.WordTrace tailWord_7052761 prefixEnd_7052761 3621456334284585773852449 := by
  unfold tailWord_7052761
  simp only [CollatzResearch.WordTrace]
  refine ⟨257235326402058887527518137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171490217601372591685012091 257235326402058887527518137)
  ·
    refine ⟨192926494801544165645638603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257235326402058887527518137 192926494801544165645638603)
    ·
      refine ⟨289389742202316248468457905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192926494801544165645638603 289389742202316248468457905)
      ·
        refine ⟨217042306651737186351343429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289389742202316248468457905 217042306651737186351343429)
        ·
          refine ⟨40695432497200722440876893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217042306651737186351343429 40695432497200722440876893)
          ·
            refine ⟨15260787186450270915328835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40695432497200722440876893 15260787186450270915328835)
            ·
              refine ⟨22891180779675406372993253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15260787186450270915328835 22891180779675406372993253)
              ·
                refine ⟨4292096396189138694936235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22891180779675406372993253 4292096396189138694936235)
                ·
                  refine ⟨6438144594283708042404353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4292096396189138694936235 6438144594283708042404353)
                  ·
                    refine ⟨4828608445712781031803265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6438144594283708042404353 4828608445712781031803265)
                    ·
                      refine ⟨3621456334284585773852449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4828608445712781031803265 3621456334284585773852449)
                      ·
                        rfl

theorem cell23_7052761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 1, 2, 2].length) (baseStart_7052761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052761 prefixEnd_7052761 := by exact prefixLift 7052761
  have htrace : WordTrace (prefixWord ++ tailWord_7052761) baseStart_7052761 baseEnd_7052761 := by
    simpa [prefixWord, tailWord_7052761, baseEnd_7052761] using wordTrace_append hprefix tailTrace_7052761
  have hstable : (prefixWord ++ tailWord_7052761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052761).length < 2 ^ (prefixWord ++ tailWord_7052761).sum := by decide
  have hdescent : baseEnd_7052761 < baseStart_7052761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052793 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 3, 8]
def baseStart_7052793 : Nat := 118140960795 + 7052793 * 2 ^ 59
def prefixEnd_7052793 : Nat := 4983230072969 + 3 ^ 40 * 7052793 * 2
def baseEnd_7052793 : Nat := 1207157588555176549550767

theorem tailTrace_7052793 : CollatzResearch.WordTrace tailWord_7052793 prefixEnd_7052793 1207157588555176549550767 := by
  unfold tailWord_7052793
  simp only [CollatzResearch.WordTrace]
  refine ⟨257236493537942956992683033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171490995691961971328455355 257236493537942956992683033)
  ·
    refine ⟨192927370153457217744512275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257236493537942956992683033 192927370153457217744512275)
    ·
      refine ⟨289391055230185826616768413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192927370153457217744512275 289391055230185826616768413)
      ·
        refine ⟨108521645711319684981288155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289391055230185826616768413 108521645711319684981288155)
        ·
          refine ⟨162782468566979527471932233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108521645711319684981288155 162782468566979527471932233)
          ·
            refine ⟨122086851425234645603949175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162782468566979527471932233 122086851425234645603949175)
            ·
              refine ⟨183130277137851968405923763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122086851425234645603949175 183130277137851968405923763)
              ·
                refine ⟨274695415706777952608885645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183130277137851968405923763 274695415706777952608885645)
                ·
                  refine ⟨103010780890041732228332117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274695415706777952608885645 103010780890041732228332117)
                  ·
                    refine ⟨1207157588555176549550767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103010780890041732228332117 1207157588555176549550767)
                    ·
                      rfl

theorem cell23_7052793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 8].length) (baseStart_7052793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052793 prefixEnd_7052793 := by exact prefixLift 7052793
  have htrace : WordTrace (prefixWord ++ tailWord_7052793) baseStart_7052793 baseEnd_7052793 := by
    simpa [prefixWord, tailWord_7052793, baseEnd_7052793] using wordTrace_append hprefix tailTrace_7052793
  have hstable : (prefixWord ++ tailWord_7052793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052793).length < 2 ^ (prefixWord ++ tailWord_7052793).sum := by decide
  have hdescent : baseEnd_7052793 < baseStart_7052793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052810 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 2, 6]
def baseStart_7052810 : Nat := 118140960795 + 7052810 * 2 ^ 59
def prefixEnd_7052810 : Nat := 4983230072969 + 3 ^ 40 * 7052810 * 2
def baseEnd_7052810 : Nat := 1207160498278885360713241

theorem tailTrace_7052810 : CollatzResearch.WordTrace tailWord_7052810 prefixEnd_7052810 1207160498278885360713241 := by
  unfold tailWord_7052810
  simp only [CollatzResearch.WordTrace]
  refine ⟨64309278394720342224012971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171491409052587579264034589 64309278394720342224012971)
  ·
    refine ⟨96463917592080513336019457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64309278394720342224012971 96463917592080513336019457)
    ·
      refine ⟨72347938194060385002014593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96463917592080513336019457 72347938194060385002014593)
      ·
        refine ⟨54260953645545288751510945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72347938194060385002014593 54260953645545288751510945)
        ·
          refine ⟨40695715234158966563633209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54260953645545288751510945 40695715234158966563633209)
          ·
            refine ⟨30521786425619224922724907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40695715234158966563633209 30521786425619224922724907)
            ·
              refine ⟨45782679638428837384087361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30521786425619224922724907 45782679638428837384087361)
              ·
                refine ⟨34337009728821628038065521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45782679638428837384087361 34337009728821628038065521)
                ·
                  refine ⟨25752757296616221028549141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34337009728821628038065521 25752757296616221028549141)
                  ·
                    refine ⟨1207160498278885360713241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25752757296616221028549141 1207160498278885360713241)
                    ·
                      rfl

theorem cell23_7052810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_7052810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052810 prefixEnd_7052810 := by exact prefixLift 7052810
  have htrace : WordTrace (prefixWord ++ tailWord_7052810) baseStart_7052810 baseEnd_7052810 := by
    simpa [prefixWord, tailWord_7052810, baseEnd_7052810] using wordTrace_append hprefix tailTrace_7052810
  have hstable : (prefixWord ++ tailWord_7052810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052810).length < 2 ^ (prefixWord ++ tailWord_7052810).sum := by decide
  have hdescent : baseEnd_7052810 < baseStart_7052810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052811 : List Nat := [1, 1, 1, 1, 8, 2, 1, 2, 2, 1, 3]
def baseStart_7052811 : Nat := 118140960795 + 7052811 * 2 ^ 59
def prefixEnd_7052811 : Nat := 4983230072969 + 3 ^ 40 * 7052811 * 2
def baseEnd_7052811 : Nat := 3621482008317310578227219

theorem tailTrace_7052811 : CollatzResearch.WordTrace tailWord_7052811 prefixEnd_7052811 3621482008317310578227219 := by
  unfold tailWord_7052811
  simp only [CollatzResearch.WordTrace]
  refine ⟨257237150051877746066838287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171491433367918497377892191 257237150051877746066838287)
  ·
    refine ⟨385855725077816619100257431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257237150051877746066838287 385855725077816619100257431)
    ·
      refine ⟨578783587616724928650386147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385855725077816619100257431 578783587616724928650386147)
      ·
        refine ⟨868175381425087392975579221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578783587616724928650386147 868175381425087392975579221)
        ·
          refine ⟨10173930251075242886432569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 868175381425087392975579221 10173930251075242886432569)
          ·
            refine ⟨7630447688306432164824427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10173930251075242886432569 7630447688306432164824427)
            ·
              refine ⟨11445671532459648247236641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7630447688306432164824427 11445671532459648247236641)
              ·
                refine ⟨8584253649344736185427481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11445671532459648247236641 8584253649344736185427481)
                ·
                  refine ⟨6438190237008552139070611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8584253649344736185427481 6438190237008552139070611)
                  ·
                    refine ⟨9657285355512828208605917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6438190237008552139070611 9657285355512828208605917)
                    ·
                      refine ⟨3621482008317310578227219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9657285355512828208605917 3621482008317310578227219)
                      ·
                        rfl

theorem cell23_7052811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 1, 3].length) (baseStart_7052811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052811 prefixEnd_7052811 := by exact prefixLift 7052811
  have htrace : WordTrace (prefixWord ++ tailWord_7052811) baseStart_7052811 baseEnd_7052811 := by
    simpa [prefixWord, tailWord_7052811, baseEnd_7052811] using wordTrace_append hprefix tailTrace_7052811
  have hstable : (prefixWord ++ tailWord_7052811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052811).length < 2 ^ (prefixWord ++ tailWord_7052811).sum := by decide
  have hdescent : baseEnd_7052811 < baseStart_7052811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052834 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 1, 4, 2]
def baseStart_7052834 : Nat := 118140960795 + 7052834 * 2 ^ 59
def prefixEnd_7052834 : Nat := 4983230072969 + 3 ^ 40 * 7052834 * 2
def baseEnd_7052834 : Nat := 3621493818372363988239613

theorem tailTrace_7052834 : CollatzResearch.WordTrace tailWord_7052834 prefixEnd_7052834 3621493818372363988239613 := by
  unfold tailWord_7052834
  simp only [CollatzResearch.WordTrace]
  refine ⟨64309497232698605248731389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171491992620529613996617037 64309497232698605248731389)
  ·
    refine ⟨24116061462261976968274271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64309497232698605248731389 24116061462261976968274271)
    ·
      refine ⟨36174092193392965452411407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24116061462261976968274271 36174092193392965452411407)
      ·
        refine ⟨54261138290089448178617111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36174092193392965452411407 54261138290089448178617111)
        ·
          refine ⟨81391707435134172267925667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54261138290089448178617111 81391707435134172267925667)
          ·
            refine ⟨122087561152701258401888501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81391707435134172267925667 122087561152701258401888501)
            ·
              refine ⟨11445708858065742975177047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122087561152701258401888501 11445708858065742975177047)
              ·
                refine ⟨17168563287098614462765571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11445708858065742975177047 17168563287098614462765571)
                ·
                  refine ⟨25752844930647921694148357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17168563287098614462765571 25752844930647921694148357)
                  ·
                    refine ⟨4828658424496485317652817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25752844930647921694148357 4828658424496485317652817)
                    ·
                      refine ⟨3621493818372363988239613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4828658424496485317652817 3621493818372363988239613)
                      ·
                        rfl

theorem cell23_7052834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_7052834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052834 prefixEnd_7052834 := by exact prefixLift 7052834
  have htrace : WordTrace (prefixWord ++ tailWord_7052834) baseStart_7052834 baseEnd_7052834 := by
    simpa [prefixWord, tailWord_7052834, baseEnd_7052834] using wordTrace_append hprefix tailTrace_7052834
  have hstable : (prefixWord ++ tailWord_7052834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052834).length < 2 ^ (prefixWord ++ tailWord_7052834).sum := by decide
  have hdescent : baseEnd_7052834 < baseStart_7052834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052854 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_7052854 : Nat := 118140960795 + 7052854 * 2 ^ 59
def prefixEnd_7052854 : Nat := 4983230072969 + 3 ^ 40 * 7052854 * 2
def baseEnd_7052854 : Nat := 3621504087985453909989521

theorem tailTrace_7052854 : CollatzResearch.WordTrace tailWord_7052854 prefixEnd_7052854 3621504087985453909989521 := by
  unfold tailWord_7052854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16077419899420122775665851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171492478927147976273769077 16077419899420122775665851)
  ·
    refine ⟨24116129849130184163498777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16077419899420122775665851 24116129849130184163498777)
    ·
      refine ⟨18087097386847638122624083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24116129849130184163498777 18087097386847638122624083)
      ·
        refine ⟨27130646080271457183936125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18087097386847638122624083 27130646080271457183936125)
        ·
          refine ⟨10173992280101796443976047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27130646080271457183936125 10173992280101796443976047)
          ·
            refine ⟨15260988420152694665964071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10173992280101796443976047 15260988420152694665964071)
            ·
              refine ⟨22891482630229041998946107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15260988420152694665964071 22891482630229041998946107)
              ·
                refine ⟨34337223945343562998419161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22891482630229041998946107 34337223945343562998419161)
                ·
                  refine ⟨25752917959007672248814371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34337223945343562998419161 25752917959007672248814371)
                  ·
                    refine ⟨38629376938511508373221557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25752917959007672248814371 38629376938511508373221557)
                    ·
                      refine ⟨3621504087985453909989521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38629376938511508373221557 3621504087985453909989521)
                      ·
                        rfl

theorem cell23_7052854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_7052854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052854 prefixEnd_7052854 := by exact prefixLift 7052854
  have htrace : WordTrace (prefixWord ++ tailWord_7052854) baseStart_7052854 baseEnd_7052854 := by
    simpa [prefixWord, tailWord_7052854, baseEnd_7052854] using wordTrace_append hprefix tailTrace_7052854
  have hstable : (prefixWord ++ tailWord_7052854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052854).length < 2 ^ (prefixWord ++ tailWord_7052854).sum := by decide
  have hdescent : baseEnd_7052854 < baseStart_7052854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052874 : List Nat := [3, 1, 2, 1, 1, 3, 5, 2, 5]
def baseStart_7052874 : Nat := 118140960795 + 7052874 * 2 ^ 59
def prefixEnd_7052874 : Nat := 4983230072969 + 3 ^ 40 * 7052874 * 2
def baseEnd_7052874 : Nat := 402390484177615981304381

theorem tailTrace_7052874 : CollatzResearch.WordTrace tailWord_7052874 prefixEnd_7052874 402390484177615981304381 := by
  unfold tailWord_7052874
  simp only [CollatzResearch.WordTrace]
  refine ⟨64309861962662376956595419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171492965233766338550921117 64309861962662376956595419)
  ·
    refine ⟨96464792943993565434893129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64309861962662376956595419 96464792943993565434893129)
    ·
      refine ⟨72348594707995174076169847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96464792943993565434893129 72348594707995174076169847)
      ·
        refine ⟨108522892061992761114254771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72348594707995174076169847 108522892061992761114254771)
        ·
          refine ⟨162784338092989141671382157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108522892061992761114254771 162784338092989141671382157)
          ·
            refine ⟨61044126784870928126768309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162784338092989141671382157 61044126784870928126768309)
            ·
              refine ⟨5722886886081649511884529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61044126784870928126768309 5722886886081649511884529)
              ·
                refine ⟨4292165164561237133913397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5722886886081649511884529 4292165164561237133913397)
                ·
                  refine ⟨402390484177615981304381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4292165164561237133913397 402390484177615981304381)
                  ·
                    rfl

theorem cell23_7052874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 5].length) (baseStart_7052874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052874 prefixEnd_7052874 := by exact prefixLift 7052874
  have htrace : WordTrace (prefixWord ++ tailWord_7052874) baseStart_7052874 baseEnd_7052874 := by
    simpa [prefixWord, tailWord_7052874, baseEnd_7052874] using wordTrace_append hprefix tailTrace_7052874
  have hstable : (prefixWord ++ tailWord_7052874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052874).length < 2 ^ (prefixWord ++ tailWord_7052874).sum := by decide
  have hdescent : baseEnd_7052874 < baseStart_7052874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052880 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 5]
def baseStart_7052880 : Nat := 118140960795 + 7052880 * 2 ^ 59
def prefixEnd_7052880 : Nat := 4983230072969 + 3 ^ 40 * 7052880 * 2
def baseEnd_7052880 : Nat := 3621517438482470808264401

theorem tailTrace_7052880 : CollatzResearch.WordTrace tailWord_7052880 prefixEnd_7052880 3621517438482470808264401 := by
  unfold tailWord_7052880
  simp only [CollatzResearch.WordTrace]
  refine ⟨128619833344313885425550047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171493111125751847234066729 128619833344313885425550047)
  ·
    refine ⟨192929750016470828138325071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128619833344313885425550047 192929750016470828138325071)
    ·
      refine ⟨289394625024706242207487607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192929750016470828138325071 289394625024706242207487607)
      ·
        refine ⟨434091937537059363311231411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289394625024706242207487607 434091937537059363311231411)
        ·
          refine ⟨651137906305589044966847117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434091937537059363311231411 651137906305589044966847117)
          ·
            refine ⟨244176714864595891862567669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 651137906305589044966847117 244176714864595891862567669)
            ·
              refine ⟨22891567018555864862115719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244176714864595891862567669 22891567018555864862115719)
              ·
                refine ⟨34337350527833797293173579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22891567018555864862115719 34337350527833797293173579)
                ·
                  refine ⟨51506025791750695939760369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34337350527833797293173579 51506025791750695939760369)
                  ·
                    refine ⟨38629519343813021954820277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51506025791750695939760369 38629519343813021954820277)
                    ·
                      refine ⟨3621517438482470808264401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38629519343813021954820277 3621517438482470808264401)
                      ·
                        rfl

theorem cell23_7052880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_7052880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052880 prefixEnd_7052880 := by exact prefixLift 7052880
  have htrace : WordTrace (prefixWord ++ tailWord_7052880) baseStart_7052880 baseEnd_7052880 := by
    simpa [prefixWord, tailWord_7052880, baseEnd_7052880] using wordTrace_append hprefix tailTrace_7052880
  have hstable : (prefixWord ++ tailWord_7052880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052880).length < 2 ^ (prefixWord ++ tailWord_7052880).sum := by decide
  have hdescent : baseEnd_7052880 < baseStart_7052880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052890 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4]
def baseStart_7052890 : Nat := 118140960795 + 7052890 * 2 ^ 59
def prefixEnd_7052890 : Nat := 4983230072969 + 3 ^ 40 * 7052890 * 2
def baseEnd_7052890 : Nat := 3621522573289015769139355

theorem tailTrace_7052890 : CollatzResearch.WordTrace tailWord_7052890 prefixEnd_7052890 3621522573289015769139355 := by
  unfold tailWord_7052890
  simp only [CollatzResearch.WordTrace]
  refine ⟨64310007854647885639741031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171493354279061028372642749 64310007854647885639741031)
  ·
    refine ⟨96465011781971828459611547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64310007854647885639741031 96465011781971828459611547)
    ·
      refine ⟨144697517672957742689417321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96465011781971828459611547 144697517672957742689417321)
      ·
        refine ⟨108523138254718307017062991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144697517672957742689417321 108523138254718307017062991)
        ·
          refine ⟨162784707382077460525594487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108523138254718307017062991 162784707382077460525594487)
          ·
            refine ⟨244177061073116190788391731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162784707382077460525594487 244177061073116190788391731)
            ·
              refine ⟨366265591609674286182587597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244177061073116190788391731 366265591609674286182587597)
              ·
                refine ⟨137349596853627857318470349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 366265591609674286182587597 137349596853627857318470349)
                ·
                  refine ⟨51506098820110446494426381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137349596853627857318470349 51506098820110446494426381)
                  ·
                    refine ⟨19314787057541417435409893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51506098820110446494426381 19314787057541417435409893)
                    ·
                      refine ⟨3621522573289015769139355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19314787057541417435409893 3621522573289015769139355)
                      ·
                        rfl

theorem cell23_7052890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_7052890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052890 prefixEnd_7052890 := by exact prefixLift 7052890
  have htrace : WordTrace (prefixWord ++ tailWord_7052890) baseStart_7052890 baseEnd_7052890 := by
    simpa [prefixWord, tailWord_7052890, baseEnd_7052890] using wordTrace_append hprefix tailTrace_7052890
  have hstable : (prefixWord ++ tailWord_7052890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052890).length < 2 ^ (prefixWord ++ tailWord_7052890).sum := by decide
  have hdescent : baseEnd_7052890 < baseStart_7052890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052904 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 2, 5]
def baseStart_7052904 : Nat := 118140960795 + 7052904 * 2 ^ 59
def prefixEnd_7052904 : Nat := 4983230072969 + 3 ^ 40 * 7052904 * 2
def baseEnd_7052904 : Nat := 1207176587339392904788097

theorem tailTrace_7052904 : CollatzResearch.WordTrace tailWord_7052904 prefixEnd_7052904 1207176587339392904788097 := by
  unfold tailWord_7052904
  simp only [CollatzResearch.WordTrace]
  refine ⟨128620271020270411474986883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171493694693693881966649177 128620271020270411474986883)
  ·
    refine ⟨192930406530405617212480325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128620271020270411474986883 192930406530405617212480325)
    ·
      refine ⟨36174451224451053227340061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192930406530405617212480325 36174451224451053227340061)
      ·
        refine ⟨13565419209169144960252523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36174451224451053227340061 13565419209169144960252523)
        ·
          refine ⟨20348128813753717440378785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13565419209169144960252523 20348128813753717440378785)
          ·
            refine ⟨15261096610315288080284089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20348128813753717440378785 15261096610315288080284089)
            ·
              refine ⟨11445822457736466060213067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15261096610315288080284089 11445822457736466060213067)
              ·
                refine ⟨17168733686604699090319601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11445822457736466060213067 17168733686604699090319601)
                ·
                  refine ⟨12876550264953524317739701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17168733686604699090319601 12876550264953524317739701)
                  ·
                    refine ⟨1207176587339392904788097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12876550264953524317739701 1207176587339392904788097)
                    ·
                      rfl

theorem cell23_7052904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_7052904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052904 prefixEnd_7052904 := by exact prefixLift 7052904
  have htrace : WordTrace (prefixWord ++ tailWord_7052904) baseStart_7052904 baseEnd_7052904 := by
    simpa [prefixWord, tailWord_7052904, baseEnd_7052904] using wordTrace_append hprefix tailTrace_7052904
  have hstable : (prefixWord ++ tailWord_7052904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052904).length < 2 ^ (prefixWord ++ tailWord_7052904).sum := by decide
  have hdescent : baseEnd_7052904 < baseStart_7052904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052961 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 2, 2, 3]
def baseStart_7052961 : Nat := 118140960795 + 7052961 * 2 ^ 59
def prefixEnd_7052961 : Nat := 4983230072969 + 3 ^ 40 * 7052961 * 2
def baseEnd_7052961 : Nat := 3621559030415484991351529

theorem tailTrace_7052961 : CollatzResearch.WordTrace tailWord_7052961 prefixEnd_7052961 3621559030415484991351529 := by
  unfold tailWord_7052961
  simp only [CollatzResearch.WordTrace]
  refine ⟨257242621001334321684798737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171495080667556214456532491 257242621001334321684798737)
  ·
    refine ⟨192931965751000741263599053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257242621001334321684798737 192931965751000741263599053)
    ·
      refine ⟨72349487156625277973849645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192931965751000741263599053 72349487156625277973849645)
      ·
        refine ⟨27131057683734479240193617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72349487156625277973849645 27131057683734479240193617)
        ·
          refine ⟨20348293262800859430145213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27131057683734479240193617 20348293262800859430145213)
          ·
            refine ⟨7630609973550322286304455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20348293262800859430145213 7630609973550322286304455)
            ·
              refine ⟨11445914960325483429456683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7630609973550322286304455 11445914960325483429456683)
              ·
                refine ⟨17168872440488225144185025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11445914960325483429456683 17168872440488225144185025)
                ·
                  refine ⟨12876654330366168858138769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17168872440488225144185025 12876654330366168858138769)
                  ·
                    refine ⟨9657490747774626643604077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12876654330366168858138769 9657490747774626643604077)
                    ·
                      refine ⟨3621559030415484991351529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9657490747774626643604077 3621559030415484991351529)
                      ·
                        rfl

theorem cell23_7052961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_7052961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052961 prefixEnd_7052961 := by exact prefixLift 7052961
  have htrace : WordTrace (prefixWord ++ tailWord_7052961) baseStart_7052961 baseEnd_7052961 := by
    simpa [prefixWord, tailWord_7052961, baseEnd_7052961] using wordTrace_append hprefix tailTrace_7052961
  have hstable : (prefixWord ++ tailWord_7052961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052961).length < 2 ^ (prefixWord ++ tailWord_7052961).sum := by decide
  have hdescent : baseEnd_7052961 < baseStart_7052961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052981 : List Nat := [1, 3, 3, 3, 2, 2, 1, 2, 6]
def baseStart_7052981 : Nat := 118140960795 + 7052981 * 2 ^ 59
def prefixEnd_7052981 : Nat := 4983230072969 + 3 ^ 40 * 7052981 * 2
def baseEnd_7052981 : Nat := 402396588892063879233493

theorem tailTrace_7052981 : CollatzResearch.WordTrace tailWord_7052981 prefixEnd_7052981 402396588892063879233493 := by
  unfold tailWord_7052981
  simp only [CollatzResearch.WordTrace]
  refine ⟨257243350461261865100526797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171495566974174576733684531 257243350461261865100526797)
  ·
    refine ⟨96466256422973199412697549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257243350461261865100526797 96466256422973199412697549)
    ·
      refine ⟨36174846158614949779761581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96466256422973199412697549 36174846158614949779761581)
      ·
        refine ⟨13565567309480606167410593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36174846158614949779761581 13565567309480606167410593)
        ·
          refine ⟨10174175482110454625557945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13565567309480606167410593 10174175482110454625557945)
          ·
            refine ⟨7630631611582840969168459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10174175482110454625557945 7630631611582840969168459)
            ·
              refine ⟨11445947417374261453752689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7630631611582840969168459 11445947417374261453752689)
              ·
                refine ⟨8584460563030696090314517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11445947417374261453752689 8584460563030696090314517)
                ·
                  refine ⟨402396588892063879233493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8584460563030696090314517 402396588892063879233493)
                  ·
                    rfl

theorem cell23_7052981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 6].length) (baseStart_7052981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052981 prefixEnd_7052981 := by exact prefixLift 7052981
  have htrace : WordTrace (prefixWord ++ tailWord_7052981) baseStart_7052981 baseEnd_7052981 := by
    simpa [prefixWord, tailWord_7052981, baseEnd_7052981] using wordTrace_append hprefix tailTrace_7052981
  have hstable : (prefixWord ++ tailWord_7052981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052981).length < 2 ^ (prefixWord ++ tailWord_7052981).sum := by decide
  have hdescent : baseEnd_7052981 < baseStart_7052981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052984 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 2, 3, 2]
def baseStart_7052984 : Nat := 118140960795 + 7052984 * 2 ^ 59
def prefixEnd_7052984 : Nat := 4983230072969 + 3 ^ 40 * 7052984 * 2
def baseEnd_7052984 : Nat := 3621570840470538401363923

theorem tailTrace_7052984 : CollatzResearch.WordTrace tailWord_7052984 prefixEnd_7052984 3621570840470538401363923 := by
  unfold tailWord_7052984
  simp only [CollatzResearch.WordTrace]
  refine ⟨128621729940125498306443003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171495639920167331075257337 128621729940125498306443003)
  ·
    refine ⟨192932594910188247459664505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128621729940125498306443003 192932594910188247459664505)
    ·
      refine ⟨144699446182641185594748379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192932594910188247459664505 144699446182641185594748379)
      ·
        refine ⟨217049169273961778392122569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144699446182641185594748379 217049169273961778392122569)
        ·
          refine ⟨162786876955471333794091927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217049169273961778392122569 162786876955471333794091927)
          ·
            refine ⟨244180315433207000691137891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162786876955471333794091927 244180315433207000691137891)
            ·
              refine ⟨366270473149810501036706837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244180315433207000691137891 366270473149810501036706837)
              ·
                refine ⟨17168928428897367236095633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 366270473149810501036706837 17168928428897367236095633)
                ·
                  refine ⟨12876696321673025427071725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17168928428897367236095633 12876696321673025427071725)
                  ·
                    refine ⟨4828761120627384535151897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12876696321673025427071725 4828761120627384535151897)
                    ·
                      refine ⟨3621570840470538401363923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4828761120627384535151897 3621570840470538401363923)
                      ·
                        rfl

theorem cell23_7052984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 2, 3, 2].length) (baseStart_7052984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052984 prefixEnd_7052984 := by exact prefixLift 7052984
  have htrace : WordTrace (prefixWord ++ tailWord_7052984) baseStart_7052984 baseEnd_7052984 := by
    simpa [prefixWord, tailWord_7052984, baseEnd_7052984] using wordTrace_append hprefix tailTrace_7052984
  have hstable : (prefixWord ++ tailWord_7052984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052984).length < 2 ^ (prefixWord ++ tailWord_7052984).sum := by decide
  have hdescent : baseEnd_7052984 < baseStart_7052984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7052991 : List Nat := [1, 1, 2, 2, 2, 3, 1, 6, 1, 1, 3]
def baseStart_7052991 : Nat := 118140960795 + 7052991 * 2 ^ 59
def prefixEnd_7052991 : Nat := 4983230072969 + 3 ^ 40 * 7052991 * 2
def baseEnd_7052991 : Nat := 3621574434835119873976391

theorem tailTrace_7052991 : CollatzResearch.WordTrace tailWord_7052991 prefixEnd_7052991 3621574434835119873976391 := by
  unfold tailWord_7052991
  simp only [CollatzResearch.WordTrace]
  refine ⟨257243715191225636808390827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171495810127483757872260551 257243715191225636808390827)
  ·
    refine ⟨385865572786838455212586241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257243715191225636808390827 385865572786838455212586241)
    ·
      refine ⟨289399179590128841409439681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385865572786838455212586241 289399179590128841409439681)
      ·
        refine ⟨217049384692596631057079761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289399179590128841409439681 217049384692596631057079761)
        ·
          refine ⟨162787038519447473292809821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217049384692596631057079761 162787038519447473292809821)
          ·
            refine ⟨61045139444792802484803683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162787038519447473292809821 61045139444792802484803683)
            ·
              refine ⟨91567709167189203727205525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61045139444792802484803683 91567709167189203727205525)
              ·
                refine ⟨4292236367211993924712759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91567709167189203727205525 4292236367211993924712759)
                ·
                  refine ⟨6438354550817990887069139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4292236367211993924712759 6438354550817990887069139)
                  ·
                    refine ⟨9657531826226986330603709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6438354550817990887069139 9657531826226986330603709)
                    ·
                      refine ⟨3621574434835119873976391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9657531826226986330603709 3621574434835119873976391)
                      ·
                        rfl

theorem cell23_7052991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 1, 1, 3].length) (baseStart_7052991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7052991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7052991 prefixEnd_7052991 := by exact prefixLift 7052991
  have htrace : WordTrace (prefixWord ++ tailWord_7052991) baseStart_7052991 baseEnd_7052991 := by
    simpa [prefixWord, tailWord_7052991, baseEnd_7052991] using wordTrace_append hprefix tailTrace_7052991
  have hstable : (prefixWord ++ tailWord_7052991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7052991).length < 2 ^ (prefixWord ++ tailWord_7052991).sum := by decide
  have hdescent : baseEnd_7052991 < baseStart_7052991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7052991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053025 : List Nat := [1, 2, 3, 1, 5, 2, 1, 3, 1, 1, 3]
def baseStart_7053025 : Nat := 118140960795 + 7053025 * 2 ^ 59
def prefixEnd_7053025 : Nat := 4983230072969 + 3 ^ 40 * 7053025 * 2
def baseEnd_7053025 : Nat := 3621591893177372740951235

theorem tailTrace_7053025 : CollatzResearch.WordTrace tailWord_7053025 prefixEnd_7053025 3621591893177372740951235 := by
  unfold tailWord_7053025
  simp only [CollatzResearch.WordTrace]
  refine ⟨257244955273102460615128529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171496636848734973743419019 257244955273102460615128529)
  ·
    refine ⟨192933716454826845461346397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257244955273102460615128529 192933716454826845461346397)
    ·
      refine ⟨72350143670560067048004899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192933716454826845461346397 72350143670560067048004899)
      ·
        refine ⟨108525215505840100572007349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72350143670560067048004899 108525215505840100572007349)
        ·
          refine ⟨10174238953672509428625689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108525215505840100572007349 10174238953672509428625689)
          ·
            refine ⟨7630679215254382071469267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10174238953672509428625689 7630679215254382071469267)
            ·
              refine ⟨11446018822881573107203901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7630679215254382071469267 11446018822881573107203901)
              ·
                refine ⟨4292257058580589915201463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11446018822881573107203901 4292257058580589915201463)
                ·
                  refine ⟨6438385587870884872802195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4292257058580589915201463 6438385587870884872802195)
                  ·
                    refine ⟨9657578381806327309203293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6438385587870884872802195 9657578381806327309203293)
                    ·
                      refine ⟨3621591893177372740951235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9657578381806327309203293 3621591893177372740951235)
                      ·
                        rfl

theorem cell23_7053025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_7053025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053025 prefixEnd_7053025 := by exact prefixLift 7053025
  have htrace : WordTrace (prefixWord ++ tailWord_7053025) baseStart_7053025 baseEnd_7053025 := by
    simpa [prefixWord, tailWord_7053025, baseEnd_7053025] using wordTrace_append hprefix tailTrace_7053025
  have hstable : (prefixWord ++ tailWord_7053025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053025).length < 2 ^ (prefixWord ++ tailWord_7053025).sum := by decide
  have hdescent : baseEnd_7053025 < baseStart_7053025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053037 : List Nat := [1, 5, 1, 2, 1, 2, 11]
def baseStart_7053037 : Nat := 118140960795 + 7053037 * 2 ^ 59
def prefixEnd_7053037 : Nat := 4983230072969 + 3 ^ 40 * 7053037 * 2
def baseEnd_7053037 : Nat := 44711087098089218444459

theorem tailTrace_7053037 : CollatzResearch.WordTrace tailWord_7053037 prefixEnd_7053037 44711087098089218444459 := by
  unfold tailWord_7053037
  simp only [CollatzResearch.WordTrace]
  refine ⟨257245392949058986664565365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171496928632705991109710243 257245392949058986664565365)
  ·
    refine ⟨24116755588974279999803003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257245392949058986664565365 24116755588974279999803003)
    ·
      refine ⟨36175133383461419999704505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24116755588974279999803003 36175133383461419999704505)
      ·
        refine ⟨27131350037596064999778379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36175133383461419999704505 27131350037596064999778379)
        ·
          refine ⟨40697025056394097499667569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27131350037596064999778379 40697025056394097499667569)
          ·
            refine ⟨30522768792295573124750677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40697025056394097499667569 30522768792295573124750677)
            ·
              refine ⟨44711087098089218444459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30522768792295573124750677 44711087098089218444459)
              ·
                rfl

theorem cell23_7053037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 11].length) (baseStart_7053037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053037 prefixEnd_7053037 := by exact prefixLift 7053037
  have htrace : WordTrace (prefixWord ++ tailWord_7053037) baseStart_7053037 baseEnd_7053037 := by
    simpa [prefixWord, tailWord_7053037, baseEnd_7053037] using wordTrace_append hprefix tailTrace_7053037
  have hstable : (prefixWord ++ tailWord_7053037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053037).length < 2 ^ (prefixWord ++ tailWord_7053037).sum := by decide
  have hdescent : baseEnd_7053037 < baseStart_7053037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053062 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_7053062 : Nat := 118140960795 + 7053062 * 2 ^ 59
def prefixEnd_7053062 : Nat := 4983230072969 + 3 ^ 40 * 7053062 * 2
def baseEnd_7053062 : Nat := 1207203630653863032062855

theorem tailTrace_7053062 : CollatzResearch.WordTrace tailWord_7053062 prefixEnd_7053062 1207203630653863032062855 := by
  unfold tailWord_7053062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8038947024186512997944545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 171497536515978943956150293 8038947024186512997944545)
  ·
    refine ⟨6029210268139884748458409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8038947024186512997944545 6029210268139884748458409)
    ·
      refine ⟨4521907701104913561343807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6029210268139884748458409 4521907701104913561343807)
      ·
        refine ⟨6782861551657370342015711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521907701104913561343807 6782861551657370342015711)
        ·
          refine ⟨10174292327486055513023567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6782861551657370342015711 10174292327486055513023567)
          ·
            refine ⟨15261438491229083269535351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10174292327486055513023567 15261438491229083269535351)
            ·
              refine ⟨22892157736843624904303027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15261438491229083269535351 22892157736843624904303027)
              ·
                refine ⟨34338236605265437356454541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22892157736843624904303027 34338236605265437356454541)
                ·
                  refine ⟨12876838726974539008670453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34338236605265437356454541 12876838726974539008670453)
                  ·
                    refine ⟨1207203630653863032062855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12876838726974539008670453 1207203630653863032062855)
                    ·
                      rfl

theorem cell23_7053062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_7053062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053062 prefixEnd_7053062 := by exact prefixLift 7053062
  have htrace : WordTrace (prefixWord ++ tailWord_7053062) baseStart_7053062 baseEnd_7053062 := by
    simpa [prefixWord, tailWord_7053062, baseEnd_7053062] using wordTrace_append hprefix tailTrace_7053062
  have hstable : (prefixWord ++ tailWord_7053062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053062).length < 2 ^ (prefixWord ++ tailWord_7053062).sum := by decide
  have hdescent : baseEnd_7053062 < baseStart_7053062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053064 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 1, 3, 3]
def baseStart_7053064 : Nat := 118140960795 + 7053064 * 2 ^ 59
def prefixEnd_7053064 : Nat := 4983230072969 + 3 ^ 40 * 7053064 * 2
def baseEnd_7053064 : Nat := 3621611918922898088363555

theorem tailTrace_7053064 : CollatzResearch.WordTrace tailWord_7053064 prefixEnd_7053064 3621611918922898088363555 := by
  unfold tailWord_7053064
  simp only [CollatzResearch.WordTrace]
  refine ⟨128623188859980585137899123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171497585146640780183865497 128623188859980585137899123)
  ·
    refine ⟨192934783289970877706848685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128623188859980585137899123 192934783289970877706848685)
    ·
      refine ⟨72350543733739079140068257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192934783289970877706848685 72350543733739079140068257)
      ·
        refine ⟨54262907800304309355051193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72350543733739079140068257 54262907800304309355051193)
        ·
          refine ⟨40697180850228232016288395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54262907800304309355051193 40697180850228232016288395)
          ·
            refine ⟨61045771275342348024432593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40697180850228232016288395 61045771275342348024432593)
            ·
              refine ⟨45784328456506761018324445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61045771275342348024432593 45784328456506761018324445)
              ·
                refine ⟨17169123171190035381871667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45784328456506761018324445 17169123171190035381871667)
                ·
                  refine ⟨25753684756785053072807501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17169123171190035381871667 25753684756785053072807501)
                  ·
                    refine ⟨9657631783794394902302813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25753684756785053072807501 9657631783794394902302813)
                    ·
                      refine ⟨3621611918922898088363555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9657631783794394902302813 3621611918922898088363555)
                      ·
                        rfl

theorem cell23_7053064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_7053064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053064 prefixEnd_7053064 := by exact prefixLift 7053064
  have htrace : WordTrace (prefixWord ++ tailWord_7053064) baseStart_7053064 baseEnd_7053064 := by
    simpa [prefixWord, tailWord_7053064, baseEnd_7053064] using wordTrace_append hprefix tailTrace_7053064
  have hstable : (prefixWord ++ tailWord_7053064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053064).length < 2 ^ (prefixWord ++ tailWord_7053064).sum := by decide
  have hdescent : baseEnd_7053064 < baseStart_7053064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053069 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_7053069 : Nat := 118140960795 + 7053069 * 2 ^ 59
def prefixEnd_7053069 : Nat := 4983230072969 + 3 ^ 40 * 7053069 * 2
def baseEnd_7053069 : Nat := 3621614486326170568801033

theorem tailTrace_7053069 : CollatzResearch.WordTrace tailWord_7053069 prefixEnd_7053069 3621614486326170568801033 := by
  unfold tailWord_7053069
  simp only [CollatzResearch.WordTrace]
  refine ⟨257246560084943056129730261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171497706723295370753153507 257246560084943056129730261)
  ·
    refine ⟨6029216251990852878040553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 257246560084943056129730261 6029216251990852878040553)
    ·
      refine ⟨4521912188993139658530415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6029216251990852878040553 4521912188993139658530415)
      ·
        refine ⟨6782868283489709487795623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521912188993139658530415 6782868283489709487795623)
        ·
          refine ⟨10174302425234564231693435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6782868283489709487795623 10174302425234564231693435)
          ·
            refine ⟨15261453637851846347540153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10174302425234564231693435 15261453637851846347540153)
            ·
              refine ⟨11446090228388884760655115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15261453637851846347540153 11446090228388884760655115)
              ·
                refine ⟨17169135342583327140982673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11446090228388884760655115 17169135342583327140982673)
                ·
                  refine ⟨12876851506937495355737005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17169135342583327140982673 12876851506937495355737005)
                  ·
                    refine ⟨4828819315101560758401377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12876851506937495355737005 4828819315101560758401377)
                    ·
                      refine ⟨3621614486326170568801033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4828819315101560758401377 3621614486326170568801033)
                      ·
                        rfl

theorem cell23_7053069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_7053069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053069 prefixEnd_7053069 := by exact prefixLift 7053069
  have htrace : WordTrace (prefixWord ++ tailWord_7053069) baseStart_7053069 baseEnd_7053069 := by
    simpa [prefixWord, tailWord_7053069, baseEnd_7053069] using wordTrace_append hprefix tailTrace_7053069
  have hstable : (prefixWord ++ tailWord_7053069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053069).length < 2 ^ (prefixWord ++ tailWord_7053069).sum := by decide
  have hdescent : baseEnd_7053069 < baseStart_7053069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053091 : List Nat := [1, 1, 1, 4, 2, 1, 2, 5, 1, 3, 2]
def baseStart_7053091 : Nat := 118140960795 + 7053091 * 2 ^ 59
def prefixEnd_7053091 : Nat := 4983230072969 + 3 ^ 40 * 7053091 * 2
def baseEnd_7053091 : Nat := 3621625782900569482725931

theorem tailTrace_7053091 : CollatzResearch.WordTrace tailWord_7053091 prefixEnd_7053091 3621625782900569482725931 := by
  unfold tailWord_7053091
  simp only [CollatzResearch.WordTrace]
  refine ⟨257247362490863353887031127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171498241660575569258020751 257247362490863353887031127)
  ·
    refine ⟨385871043736295030830546691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257247362490863353887031127 385871043736295030830546691)
    ·
      refine ⟨578806565604442546245820037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385871043736295030830546691 578806565604442546245820037)
      ·
        refine ⟨108526231050832977421091257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 578806565604442546245820037 108526231050832977421091257)
        ·
          refine ⟨81394673288124733065818443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108526231050832977421091257 81394673288124733065818443)
          ·
            refine ⟨122092009932187099598727665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81394673288124733065818443 122092009932187099598727665)
            ·
              refine ⟨91569007449140324699045749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122092009932187099598727665 91569007449140324699045749)
              ·
                refine ⟨8584594448356905440535539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91569007449140324699045749 8584594448356905440535539)
                ·
                  refine ⟨12876891672535358160803309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8584594448356905440535539 12876891672535358160803309)
                  ·
                    refine ⟨4828834377200759310301241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12876891672535358160803309 4828834377200759310301241)
                    ·
                      refine ⟨3621625782900569482725931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4828834377200759310301241 3621625782900569482725931)
                      ·
                        rfl

theorem cell23_7053091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_7053091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053091 prefixEnd_7053091 := by exact prefixLift 7053091
  have htrace : WordTrace (prefixWord ++ tailWord_7053091) baseStart_7053091 baseEnd_7053091 := by
    simpa [prefixWord, tailWord_7053091, baseEnd_7053091] using wordTrace_append hprefix tailTrace_7053091
  have hstable : (prefixWord ++ tailWord_7053091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053091).length < 2 ^ (prefixWord ++ tailWord_7053091).sum := by decide
  have hdescent : baseEnd_7053091 < baseStart_7053091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053108 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_7053108 : Nat := 118140960795 + 7053108 * 2 ^ 59
def prefixEnd_7053108 : Nat := 4983230072969 + 3 ^ 40 * 7053108 * 2
def baseEnd_7053108 : Nat := 3621634512071695916213353

theorem tailTrace_7053108 : CollatzResearch.WordTrace tailWord_7053108 prefixEnd_7053108 3621634512071695916213353 := by
  unfold tailWord_7053108
  simp only [CollatzResearch.WordTrace]
  refine ⟨128623991265900882895199989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171498655021201177193599985 128623991265900882895199989)
  ·
    refine ⟨12058499181178207771424999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128623991265900882895199989 12058499181178207771424999)
    ·
      refine ⟨18087748771767311657137499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12058499181178207771424999 18087748771767311657137499)
      ·
        refine ⟨27131623157650967485706249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18087748771767311657137499 27131623157650967485706249)
        ·
          refine ⟨20348717368238225614279687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27131623157650967485706249 20348717368238225614279687)
          ·
            refine ⟨30523076052357338421419531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20348717368238225614279687 30523076052357338421419531)
            ·
              refine ⟨45784614078536007632129297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30523076052357338421419531 45784614078536007632129297)
              ·
                refine ⟨34338460558902005724096973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45784614078536007632129297 34338460558902005724096973)
                ·
                  refine ⟨12876922709588252146536365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34338460558902005724096973 12876922709588252146536365)
                  ·
                    refine ⟨4828846016095594554951137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12876922709588252146536365 4828846016095594554951137)
                    ·
                      refine ⟨3621634512071695916213353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4828846016095594554951137 3621634512071695916213353)
                      ·
                        rfl

theorem cell23_7053108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_7053108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053108 prefixEnd_7053108 := by exact prefixLift 7053108
  have htrace : WordTrace (prefixWord ++ tailWord_7053108) baseStart_7053108 baseEnd_7053108 := by
    simpa [prefixWord, tailWord_7053108, baseEnd_7053108] using wordTrace_append hprefix tailTrace_7053108
  have hstable : (prefixWord ++ tailWord_7053108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053108).length < 2 ^ (prefixWord ++ tailWord_7053108).sum := by decide
  have hdescent : baseEnd_7053108 < baseStart_7053108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053114 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 2, 6]
def baseStart_7053114 : Nat := 118140960795 + 7053114 * 2 ^ 59
def prefixEnd_7053114 : Nat := 4983230072969 + 3 ^ 40 * 7053114 * 2
def baseEnd_7053114 : Nat := 1207212530985207630912775

theorem tailTrace_7053114 : CollatzResearch.WordTrace tailWord_7053114 prefixEnd_7053114 1207212530985207630912775 := by
  unfold tailWord_7053114
  simp only [CollatzResearch.WordTrace]
  refine ⟨64312050342445007203779599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171498800913186685876745597 64312050342445007203779599)
  ·
    refine ⟨96468075513667510805669399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64312050342445007203779599 96468075513667510805669399)
    ·
      refine ⟨144702113270501266208504099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96468075513667510805669399 144702113270501266208504099)
      ·
        refine ⟨217053169905751899312756149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144702113270501266208504099 217053169905751899312756149)
        ·
          refine ⟨20348734678664240560570889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217053169905751899312756149 20348734678664240560570889)
          ·
            refine ⟨15261551008998180420428167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20348734678664240560570889 15261551008998180420428167)
            ·
              refine ⟨22892326513497270630642251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15261551008998180420428167 22892326513497270630642251)
              ·
                refine ⟨34338489770245905945963377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22892326513497270630642251 34338489770245905945963377)
                ·
                  refine ⟨25753867327684429459472533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34338489770245905945963377 25753867327684429459472533)
                  ·
                    refine ⟨1207212530985207630912775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25753867327684429459472533 1207212530985207630912775)
                    ·
                      rfl

theorem cell23_7053114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_7053114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053114 prefixEnd_7053114 := by exact prefixLift 7053114
  have htrace : WordTrace (prefixWord ++ tailWord_7053114) baseStart_7053114 baseEnd_7053114 := by
    simpa [prefixWord, tailWord_7053114, baseEnd_7053114] using wordTrace_append hprefix tailTrace_7053114
  have hstable : (prefixWord ++ tailWord_7053114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053114).length < 2 ^ (prefixWord ++ tailWord_7053114).sum := by decide
  have hdescent : baseEnd_7053114 < baseStart_7053114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053127 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 9]
def baseStart_7053127 : Nat := 118140960795 + 7053127 * 2 ^ 59
def prefixEnd_7053127 : Nat := 4983230072969 + 3 ^ 40 * 7053127 * 2
def baseEnd_7053127 : Nat := 402404918689347926875085

theorem tailTrace_7053127 : CollatzResearch.WordTrace tailWord_7053127 prefixEnd_7053127 402404918689347926875085 := by
  unfold tailWord_7053127
  simp only [CollatzResearch.WordTrace]
  refine ⟨257248675518732932035341635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171499117012488621356894423 257248675518732932035341635)
  ·
    refine ⟨385873013278099398053012453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257248675518732932035341635 385873013278099398053012453)
    ·
      refine ⟨72351189989643637134939835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385873013278099398053012453 72351189989643637134939835)
      ·
        refine ⟨108526784984465455702409753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72351189989643637134939835 108526784984465455702409753)
        ·
          refine ⟨81395088738349091776807315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108526784984465455702409753 81395088738349091776807315)
          ·
            refine ⟨122092633107523637665210973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81395088738349091776807315 122092633107523637665210973)
            ·
              refine ⟨45784737415321364124454115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122092633107523637665210973 45784737415321364124454115)
              ·
                refine ⟨68677106122982046186681173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45784737415321364124454115 68677106122982046186681173)
                ·
                  refine ⟨402404918689347926875085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68677106122982046186681173 402404918689347926875085)
                  ·
                    rfl

theorem cell23_7053127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 9].length) (baseStart_7053127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053127 prefixEnd_7053127 := by exact prefixLift 7053127
  have htrace : WordTrace (prefixWord ++ tailWord_7053127) baseStart_7053127 baseEnd_7053127 := by
    simpa [prefixWord, tailWord_7053127, baseEnd_7053127] using wordTrace_append hprefix tailTrace_7053127
  have hstable : (prefixWord ++ tailWord_7053127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053127).length < 2 ^ (prefixWord ++ tailWord_7053127).sum := by decide
  have hdescent : baseEnd_7053127 < baseStart_7053127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053208 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 2, 5]
def baseStart_7053208 : Nat := 118140960795 + 7053208 * 2 ^ 59
def prefixEnd_7053208 : Nat := 4983230072969 + 3 ^ 40 * 7053208 * 2
def baseEnd_7053208 : Nat := 1207228620045715174987631

theorem tailTrace_7053208 : CollatzResearch.WordTrace tailWord_7053208 prefixEnd_7053208 1207228620045715174987631 := by
  unfold tailWord_7053208
  simp only [CollatzResearch.WordTrace]
  refine ⟨128625814915719741434520139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171501086554292988579360185 128625814915719741434520139)
  ·
    refine ⟨192938722373579612151780209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128625814915719741434520139 192938722373579612151780209)
    ·
      refine ⟨144704041780184709113835157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192938722373579612151780209 144704041780184709113835157)
      ·
        refine ⟨6783001958446158239711023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 144704041780184709113835157 6783001958446158239711023)
        ·
          refine ⟨10174502937669237359566535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6783001958446158239711023 10174502937669237359566535)
          ·
            refine ⟨15261754406503856039349803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10174502937669237359566535 15261754406503856039349803)
            ·
              refine ⟨22892631609755784059024705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15261754406503856039349803 22892631609755784059024705)
              ·
                refine ⟨17169473707316838044268529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22892631609755784059024705 17169473707316838044268529)
                ·
                  refine ⟨12877105280487628533201397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17169473707316838044268529 12877105280487628533201397)
                  ·
                    refine ⟨1207228620045715174987631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12877105280487628533201397 1207228620045715174987631)
                    ·
                      rfl

theorem cell23_7053208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_7053208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053208 prefixEnd_7053208 := by exact prefixLift 7053208
  have htrace : WordTrace (prefixWord ++ tailWord_7053208) baseStart_7053208 baseEnd_7053208 := by
    simpa [prefixWord, tailWord_7053208, baseEnd_7053208] using wordTrace_append hprefix tailTrace_7053208
  have hstable : (prefixWord ++ tailWord_7053208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053208).length < 2 ^ (prefixWord ++ tailWord_7053208).sum := by decide
  have hdescent : baseEnd_7053208 < baseStart_7053208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053305 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 2, 3, 2]
def baseStart_7053305 : Nat := 118140960795 + 7053305 * 2 ^ 59
def prefixEnd_7053305 : Nat := 4983230072969 + 3 ^ 40 * 7053305 * 2
def baseEnd_7053305 : Nat := 3621735667760631645449947

theorem tailTrace_7053305 : CollatzResearch.WordTrace tailWord_7053305 prefixEnd_7053305 3621735667760631645449947 := by
  unfold tailWord_7053305
  simp only [CollatzResearch.WordTrace]
  refine ⟨257255167712088068435321369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171503445141392045623547579 257255167712088068435321369)
  ·
    refine ⟨192941375784066051326491027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257255167712088068435321369 192941375784066051326491027)
    ·
      refine ⟨289412063676099076989736541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192941375784066051326491027 289412063676099076989736541)
      ·
        refine ⟨108529523878537153871151203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289412063676099076989736541 108529523878537153871151203)
        ·
          refine ⟨162794285817805730806726805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108529523878537153871151203 162794285817805730806726805)
          ·
            refine ⟨7630982147709643631565319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162794285817805730806726805 7630982147709643631565319)
            ·
              refine ⟨11446473221564465447347979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7630982147709643631565319 11446473221564465447347979)
              ·
                refine ⟨17169709832346698171021969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11446473221564465447347979 17169709832346698171021969)
                ·
                  refine ⟨12877282374260023628266477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17169709832346698171021969 12877282374260023628266477)
                  ·
                    refine ⟨4828980890347508860599929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12877282374260023628266477 4828980890347508860599929)
                    ·
                      refine ⟨3621735667760631645449947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4828980890347508860599929 3621735667760631645449947)
                      ·
                        rfl

theorem cell23_7053305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_7053305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053305 prefixEnd_7053305 := by exact prefixLift 7053305
  have htrace : WordTrace (prefixWord ++ tailWord_7053305) baseStart_7053305 baseEnd_7053305 := by
    simpa [prefixWord, tailWord_7053305, baseEnd_7053305] using wordTrace_append hprefix tailTrace_7053305
  have hstable : (prefixWord ++ tailWord_7053305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053305).length < 2 ^ (prefixWord ++ tailWord_7053305).sum := by decide
  have hdescent : baseEnd_7053305 < baseStart_7053305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053324 : List Nat := [2, 2, 1, 2, 3, 1, 12]
def baseStart_7053324 : Nat := 118140960795 + 7053324 * 2 ^ 59
def prefixEnd_7053324 : Nat := 4983230072969 + 3 ^ 40 * 7053324 * 2
def baseEnd_7053324 : Nat := 44712906467815642853239

theorem tailTrace_7053324 : CollatzResearch.WordTrace tailWord_7053324 prefixEnd_7053324 44712906467815642853239 := by
  unfold tailWord_7053324
  simp only [CollatzResearch.WordTrace]
  refine ⟨128627930349509617340131513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171503907132679489786842017 128627930349509617340131513)
  ·
    refine ⟨96470947762132213005098635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128627930349509617340131513 96470947762132213005098635)
    ·
      refine ⟨144706421643198319507647953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96470947762132213005098635 144706421643198319507647953)
      ·
        refine ⟨108529816232398739630735965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144706421643198319507647953 108529816232398739630735965)
        ·
          refine ⟨40698681087149527361525987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108529816232398739630735965 40698681087149527361525987)
          ·
            refine ⟨61048021630724291042288981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40698681087149527361525987 61048021630724291042288981)
            ·
              refine ⟨44712906467815642853239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 61048021630724291042288981 44712906467815642853239)
              ·
                rfl

theorem cell23_7053324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 12].length) (baseStart_7053324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053324 prefixEnd_7053324 := by exact prefixLift 7053324
  have htrace : WordTrace (prefixWord ++ tailWord_7053324) baseStart_7053324 baseEnd_7053324 := by
    simpa [prefixWord, tailWord_7053324, baseEnd_7053324] using wordTrace_append hprefix tailTrace_7053324
  have hstable : (prefixWord ++ tailWord_7053324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053324).length < 2 ^ (prefixWord ++ tailWord_7053324).sum := by decide
  have hdescent : baseEnd_7053324 < baseStart_7053324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053345 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 1, 6]
def baseStart_7053345 : Nat := 118140960795 + 7053345 * 2 ^ 59
def prefixEnd_7053345 : Nat := 4983230072969 + 3 ^ 40 * 7053345 * 2
def baseEnd_7053345 : Nat := 1207252068995603829649921

theorem tailTrace_7053345 : CollatzResearch.WordTrace tailWord_7053345 prefixEnd_7053345 1207252068995603829649921 := by
  unfold tailWord_7053345
  simp only [CollatzResearch.WordTrace]
  refine ⟨257256626631943155266777489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171504417754628770177851659 257256626631943155266777489)
  ·
    refine ⟨192942469973957366450083117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257256626631943155266777489 192942469973957366450083117)
    ·
      refine ⟨72353426240234012418781169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192942469973957366450083117 72353426240234012418781169)
      ·
        refine ⟨54265069680175509314085877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72353426240234012418781169 54265069680175509314085877)
        ·
          refine ⟨5087350282516453998195551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54265069680175509314085877 5087350282516453998195551)
          ·
            refine ⟨7631025423774680997293327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5087350282516453998195551 7631025423774680997293327)
            ·
              refine ⟨11446538135662021495939991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7631025423774680997293327 11446538135662021495939991)
              ·
                refine ⟨17169807203493032243909987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11446538135662021495939991 17169807203493032243909987)
                ·
                  refine ⟨25754710805239548365864981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17169807203493032243909987 25754710805239548365864981)
                  ·
                    refine ⟨1207252068995603829649921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25754710805239548365864981 1207252068995603829649921)
                    ·
                      rfl

theorem cell23_7053345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_7053345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053345 prefixEnd_7053345 := by exact prefixLift 7053345
  have htrace : WordTrace (prefixWord ++ tailWord_7053345) baseStart_7053345 baseEnd_7053345 := by
    simpa [prefixWord, tailWord_7053345, baseEnd_7053345] using wordTrace_append hprefix tailTrace_7053345
  have hstable : (prefixWord ++ tailWord_7053345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053345).length < 2 ^ (prefixWord ++ tailWord_7053345).sum := by decide
  have hdescent : baseEnd_7053345 < baseStart_7053345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053348 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 1, 1, 6]
def baseStart_7053348 : Nat := 118140960795 + 7053348 * 2 ^ 59
def prefixEnd_7053348 : Nat := 4983230072969 + 3 ^ 40 * 7053348 * 2
def baseEnd_7053348 : Nat := 3621757747428774977212249

theorem tailTrace_7053348 : CollatzResearch.WordTrace tailWord_7053348 prefixEnd_7053348 3621757747428774977212249 := by
  unfold tailWord_7053348
  simp only [CollatzResearch.WordTrace]
  refine ⟨128628368025466143389568349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171504490700621524519424465 128628368025466143389568349)
  ·
    refine ⟨48235638009549803771088131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128628368025466143389568349 48235638009549803771088131)
    ·
      refine ⟨72353457014324705656632197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48235638009549803771088131 72353457014324705656632197)
      ·
        refine ⟨13566273190185882310618537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72353457014324705656632197 13566273190185882310618537)
        ·
          refine ⟨10174704892639411732963903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13566273190185882310618537 10174704892639411732963903)
          ·
            refine ⟨15262057338959117599445855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10174704892639411732963903 15262057338959117599445855)
            ·
              refine ⟨22893086008438676399168783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15262057338959117599445855 22893086008438676399168783)
              ·
                refine ⟨34339629012658014598753175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22893086008438676399168783 34339629012658014598753175)
                ·
                  refine ⟨51509443518987021898129763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34339629012658014598753175 51509443518987021898129763)
                  ·
                    refine ⟨77264165278480532847194645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51509443518987021898129763 77264165278480532847194645)
                    ·
                      refine ⟨3621757747428774977212249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77264165278480532847194645 3621757747428774977212249)
                      ·
                        rfl

theorem cell23_7053348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_7053348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053348 prefixEnd_7053348 := by exact prefixLift 7053348
  have htrace : WordTrace (prefixWord ++ tailWord_7053348) baseStart_7053348 baseEnd_7053348 := by
    simpa [prefixWord, tailWord_7053348, baseEnd_7053348] using wordTrace_append hprefix tailTrace_7053348
  have hstable : (prefixWord ++ tailWord_7053348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053348).length < 2 ^ (prefixWord ++ tailWord_7053348).sum := by decide
  have hdescent : baseEnd_7053348 < baseStart_7053348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053352 : List Nat := [2, 1, 5, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_7053352 : Nat := 118140960795 + 7053352 * 2 ^ 59
def prefixEnd_7053352 : Nat := 4983230072969 + 3 ^ 40 * 7053352 * 2
def baseEnd_7053352 : Nat := 3621759801351392961562231

theorem tailTrace_7053352 : CollatzResearch.WordTrace tailWord_7053352 prefixEnd_7053352 3621759801351392961562231 := by
  unfold tailWord_7053352
  simp only [CollatzResearch.WordTrace]
  refine ⟨128628440971458897731141155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171504587961945196974854873 128628440971458897731141155)
  ·
    refine ⟨192942661457188346596711733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128628440971458897731141155 192942661457188346596711733)
    ·
      refine ⟨18088374511611407493441725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192942661457188346596711733 18088374511611407493441725)
      ·
        refine ⟨6783140441854277810040647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18088374511611407493441725 6783140441854277810040647)
        ·
          refine ⟨10174710662781416715060971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6783140441854277810040647 10174710662781416715060971)
          ·
            refine ⟨15262065994172125072591457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10174710662781416715060971 15262065994172125072591457)
            ·
              refine ⟨11446549495629093804443593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15262065994172125072591457 11446549495629093804443593)
              ·
                refine ⟨8584912121721820353332695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11446549495629093804443593 8584912121721820353332695)
                ·
                  refine ⟨12877368182582730529999043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8584912121721820353332695 12877368182582730529999043)
                  ·
                    refine ⟨19316052273874095794998565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12877368182582730529999043 19316052273874095794998565)
                    ·
                      refine ⟨3621759801351392961562231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19316052273874095794998565 3621759801351392961562231)
                      ·
                        rfl

theorem cell23_7053352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_7053352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053352 prefixEnd_7053352 := by exact prefixLift 7053352
  have htrace : WordTrace (prefixWord ++ tailWord_7053352) baseStart_7053352 baseEnd_7053352 := by
    simpa [prefixWord, tailWord_7053352, baseEnd_7053352] using wordTrace_append hprefix tailTrace_7053352
  have hstable : (prefixWord ++ tailWord_7053352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053352).length < 2 ^ (prefixWord ++ tailWord_7053352).sum := by decide
  have hdescent : baseEnd_7053352 < baseStart_7053352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053358 : List Nat := [4, 1, 3, 1, 1, 2, 4, 7]
def baseStart_7053358 : Nat := 118140960795 + 7053358 * 2 ^ 59
def prefixEnd_7053358 : Nat := 4983230072969 + 3 ^ 40 * 7053358 * 2
def baseEnd_7053358 : Nat := 134139366008715553262489

theorem tailTrace_7053358 : CollatzResearch.WordTrace tailWord_7053358 prefixEnd_7053358 134139366008715553262489 := by
  unfold tailWord_7053358
  simp only [CollatzResearch.WordTrace]
  refine ⟨32157137597612007310875091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171504733853930705658000485 32157137597612007310875091)
  ·
    refine ⟨48235706396418010966312637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32157137597612007310875091 48235706396418010966312637)
    ·
      refine ⟨18088389898656754112367239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48235706396418010966312637 18088389898656754112367239)
      ·
        refine ⟨27132584847985131168550859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18088389898656754112367239 27132584847985131168550859)
        ·
          refine ⟨40698877271977696752826289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27132584847985131168550859 40698877271977696752826289)
          ·
            refine ⟨30524157953983272564619717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40698877271977696752826289 30524157953983272564619717)
            ·
              refine ⟨5723279616371863605866197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30524157953983272564619717 5723279616371863605866197)
              ·
                refine ⟨134139366008715553262489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5723279616371863605866197 134139366008715553262489)
                ·
                  rfl

theorem cell23_7053358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 7].length) (baseStart_7053358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053358 prefixEnd_7053358 := by exact prefixLift 7053358
  have htrace : WordTrace (prefixWord ++ tailWord_7053358) baseStart_7053358 baseEnd_7053358 := by
    simpa [prefixWord, tailWord_7053358, baseEnd_7053358] using wordTrace_append hprefix tailTrace_7053358
  have hstable : (prefixWord ++ tailWord_7053358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053358).length < 2 ^ (prefixWord ++ tailWord_7053358).sum := by decide
  have hdescent : baseEnd_7053358 < baseStart_7053358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053406 : List Nat := [4, 4, 1, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_7053406 : Nat := 118140960795 + 7053406 * 2 ^ 59
def prefixEnd_7053406 : Nat := 4983230072969 + 3 ^ 40 * 7053406 * 2
def baseEnd_7053406 : Nat := 3621787529306735750286983

theorem tailTrace_7053406 : CollatzResearch.WordTrace tailWord_7053406 prefixEnd_7053406 3621787529306735750286983 := by
  unfold tailWord_7053406
  simp only [CollatzResearch.WordTrace]
  refine ⟨32157356435590270335593509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171505900989814775123165381 32157356435590270335593509)
  ·
    refine ⟨6029504331673175687923783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32157356435590270335593509 6029504331673175687923783)
    ·
      refine ⟨9044256497509763531885675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6029504331673175687923783 9044256497509763531885675)
      ·
        refine ⟨13566384746264645297828513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9044256497509763531885675 13566384746264645297828513)
        ·
          refine ⟨10174788559698483973371385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13566384746264645297828513 10174788559698483973371385)
          ·
            refine ⟨7631091419773862980028539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10174788559698483973371385 7631091419773862980028539)
            ·
              refine ⟨11446637129660794470042809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7631091419773862980028539 11446637129660794470042809)
              ·
                refine ⟨8584977847245595852532107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11446637129660794470042809 8584977847245595852532107)
                ·
                  refine ⟨12877466770868393778798161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8584977847245595852532107 12877466770868393778798161)
                  ·
                    refine ⟨9658100078151295334098621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12877466770868393778798161 9658100078151295334098621)
                    ·
                      refine ⟨3621787529306735750286983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9658100078151295334098621 3621787529306735750286983)
                      ·
                        rfl

theorem cell23_7053406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_7053406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053406 prefixEnd_7053406 := by exact prefixLift 7053406
  have htrace : WordTrace (prefixWord ++ tailWord_7053406) baseStart_7053406 baseEnd_7053406 := by
    simpa [prefixWord, tailWord_7053406, baseEnd_7053406] using wordTrace_append hprefix tailTrace_7053406
  have hstable : (prefixWord ++ tailWord_7053406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053406).length < 2 ^ (prefixWord ++ tailWord_7053406).sum := by decide
  have hdescent : baseEnd_7053406 < baseStart_7053406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053411 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 5]
def baseStart_7053411 : Nat := 118140960795 + 7053411 * 2 ^ 59
def prefixEnd_7053411 : Nat := 4983230072969 + 3 ^ 40 * 7053411 * 2
def baseEnd_7053411 : Nat := 3621790096710008230724459

theorem tailTrace_7053411 : CollatzResearch.WordTrace tailWord_7053411 prefixEnd_7053411 3621790096710008230724459 := by
  unfold tailWord_7053411
  simp only [CollatzResearch.WordTrace]
  refine ⟨257259033849704048538680087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171506022566469365692453391 257259033849704048538680087)
  ·
    refine ⟨385888550774556072808020131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257259033849704048538680087 385888550774556072808020131)
    ·
      refine ⟨578832826161834109212030197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385888550774556072808020131 578832826161834109212030197)
      ·
        refine ⟨54265577452671947738627831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 578832826161834109212030197 54265577452671947738627831)
        ·
          refine ⟨81398366179007921607941747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54265577452671947738627831 81398366179007921607941747)
          ·
            refine ⟨122097549268511882411912621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81398366179007921607941747 122097549268511882411912621)
            ·
              refine ⟨45786580975691955904467233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122097549268511882411912621 45786580975691955904467233)
              ·
                refine ⟨34339935731768966928350425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45786580975691955904467233 34339935731768966928350425)
                ·
                  refine ⟨25754951798826725196262819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34339935731768966928350425 25754951798826725196262819)
                  ·
                    refine ⟨38632427698240087794394229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25754951798826725196262819 38632427698240087794394229)
                    ·
                      refine ⟨3621790096710008230724459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38632427698240087794394229 3621790096710008230724459)
                      ·
                        rfl

theorem cell23_7053411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_7053411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053411 prefixEnd_7053411 := by exact prefixLift 7053411
  have htrace : WordTrace (prefixWord ++ tailWord_7053411) baseStart_7053411 baseEnd_7053411 := by
    simpa [prefixWord, tailWord_7053411, baseEnd_7053411] using wordTrace_append hprefix tailTrace_7053411
  have hstable : (prefixWord ++ tailWord_7053411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053411).length < 2 ^ (prefixWord ++ tailWord_7053411).sum := by decide
  have hdescent : baseEnd_7053411 < baseStart_7053411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053461 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 1, 7]
def baseStart_7053461 : Nat := 118140960795 + 7053461 * 2 ^ 59
def prefixEnd_7053461 : Nat := 4983230072969 + 3 ^ 40 * 7053461 * 2
def baseEnd_7053461 : Nat := 1207271923580911011699743

theorem tailTrace_7053461 : CollatzResearch.WordTrace tailWord_7053461 prefixEnd_7053461 1207271923580911011699743 := by
  unfold tailWord_7053461
  simp only [CollatzResearch.WordTrace]
  refine ⟨257260857499522907078000237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171507238333015271385333491 257260857499522907078000237)
  ·
    refine ⟨96472821562321090154250089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257260857499522907078000237 96472821562321090154250089)
    ·
      refine ⟨72354616171740817615687567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96472821562321090154250089 72354616171740817615687567)
      ·
        refine ⟨108531924257611226423531351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72354616171740817615687567 108531924257611226423531351)
        ·
          refine ⟨162797886386416839635297027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108531924257611226423531351 162797886386416839635297027)
          ·
            refine ⟨244196829579625259452945541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162797886386416839635297027 244196829579625259452945541)
            ·
              refine ⟨45786905546179736147427289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244196829579625259452945541 45786905546179736147427289)
              ·
                refine ⟨34340179159634802110570467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45786905546179736147427289 34340179159634802110570467)
                ·
                  refine ⟨51510268739452203165855701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34340179159634802110570467 51510268739452203165855701)
                  ·
                    refine ⟨1207271923580911011699743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51510268739452203165855701 1207271923580911011699743)
                    ·
                      rfl

theorem cell23_7053461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_7053461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053461 prefixEnd_7053461 := by exact prefixLift 7053461
  have htrace : WordTrace (prefixWord ++ tailWord_7053461) baseStart_7053461 baseEnd_7053461 := by
    simpa [prefixWord, tailWord_7053461, baseEnd_7053461] using wordTrace_append hprefix tailTrace_7053461
  have hstable : (prefixWord ++ tailWord_7053461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053461).length < 2 ^ (prefixWord ++ tailWord_7053461).sum := by decide
  have hdescent : baseEnd_7053461 < baseStart_7053461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053493 : List Nat := [1, 3, 3, 4, 2, 1, 1, 2, 2, 2, 2]
def baseStart_7053493 : Nat := 118140960795 + 7053493 * 2 ^ 59
def prefixEnd_7053493 : Nat := 4983230072969 + 3 ^ 40 * 7053493 * 2
def baseEnd_7053493 : Nat := 3621832202123676909899083

theorem tailTrace_7053493 : CollatzResearch.WordTrace tailWord_7053493 prefixEnd_7053493 3621832202123676909899083 := by
  unfold tailWord_7053493
  simp only [CollatzResearch.WordTrace]
  refine ⟨257262024635406976543165133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171508016423604651028776755 257262024635406976543165133)
  ·
    refine ⟨96473259238277616203686925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257262024635406976543165133 96473259238277616203686925)
    ·
      refine ⟨36177472214354106076382597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96473259238277616203686925 36177472214354106076382597)
      ·
        refine ⟨6783276040191394889321737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36177472214354106076382597 6783276040191394889321737)
        ·
          refine ⟨5087457030143546166991303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6783276040191394889321737 5087457030143546166991303)
          ·
            refine ⟨7631185545215319250486955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5087457030143546166991303 7631185545215319250486955)
            ·
              refine ⟨11446778317822978875730433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7631185545215319250486955 11446778317822978875730433)
              ·
                refine ⟨8585083738367234156797825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11446778317822978875730433 8585083738367234156797825)
                ·
                  refine ⟨6438812803775425617598369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8585083738367234156797825 6438812803775425617598369)
                  ·
                    refine ⟨4829109602831569213198777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6438812803775425617598369 4829109602831569213198777)
                    ·
                      refine ⟨3621832202123676909899083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4829109602831569213198777 3621832202123676909899083)
                      ·
                        rfl

theorem cell23_7053493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_7053493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053493 prefixEnd_7053493 := by exact prefixLift 7053493
  have htrace : WordTrace (prefixWord ++ tailWord_7053493) baseStart_7053493 baseEnd_7053493 := by
    simpa [prefixWord, tailWord_7053493, baseEnd_7053493] using wordTrace_append hprefix tailTrace_7053493
  have hstable : (prefixWord ++ tailWord_7053493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053493).length < 2 ^ (prefixWord ++ tailWord_7053493).sum := by decide
  have hdescent : baseEnd_7053493 < baseStart_7053493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053498 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4]
def baseStart_7053498 : Nat := 118140960795 + 7053498 * 2 ^ 59
def prefixEnd_7053498 : Nat := 4983230072969 + 3 ^ 40 * 7053498 * 2
def baseEnd_7053498 : Nat := 3621834769526949390336559

theorem tailTrace_7053498 : CollatzResearch.WordTrace tailWord_7053498 prefixEnd_7053498 3621834769526949390336559 := by
  unfold tailWord_7053498
  simp only [CollatzResearch.WordTrace]
  refine ⟨64315551750097215599274287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171508138000259241598064765 64315551750097215599274287)
  ·
    refine ⟨96473327625145823398911431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64315551750097215599274287 96473327625145823398911431)
    ·
      refine ⟨144709991437718735098367147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96473327625145823398911431 144709991437718735098367147)
      ·
        refine ⟨217064987156578102647550721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144709991437718735098367147 217064987156578102647550721)
        ·
          refine ⟨162798740367433576985663041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217064987156578102647550721 162798740367433576985663041)
          ·
            refine ⟨122099055275575182739247281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162798740367433576985663041 122099055275575182739247281)
            ·
              refine ⟨91574291456681387054435461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122099055275575182739247281 91574291456681387054435461)
              ·
                refine ⟨17170179648127760072706649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91574291456681387054435461 17170179648127760072706649)
                ·
                  refine ⟨12877634736095820054529987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17170179648127760072706649 12877634736095820054529987)
                  ·
                    refine ⟨19316452104143730081794981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12877634736095820054529987 19316452104143730081794981)
                    ·
                      refine ⟨3621834769526949390336559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19316452104143730081794981 3621834769526949390336559)
                      ·
                        rfl

theorem cell23_7053498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_7053498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053498 prefixEnd_7053498 := by exact prefixLift 7053498
  have htrace : WordTrace (prefixWord ++ tailWord_7053498) baseStart_7053498 baseEnd_7053498 := by
    simpa [prefixWord, tailWord_7053498, baseEnd_7053498] using wordTrace_append hprefix tailTrace_7053498
  have hstable : (prefixWord ++ tailWord_7053498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053498).length < 2 ^ (prefixWord ++ tailWord_7053498).sum := by decide
  have hdescent : baseEnd_7053498 < baseStart_7053498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053558 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_7053558 : Nat := 118140960795 + 7053558 * 2 ^ 59
def prefixEnd_7053558 : Nat := 4983230072969 + 3 ^ 40 * 7053558 * 2
def baseEnd_7053558 : Nat := 3621865578366219155586283

theorem tailTrace_7053558 : CollatzResearch.WordTrace tailWord_7053558 prefixEnd_7053558 3621865578366219155586283 := by
  unfold tailWord_7053558
  simp only [CollatzResearch.WordTrace]
  refine ⟨16079024711260718290267583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171509596920114328429520885 16079024711260718290267583)
  ·
    refine ⟨24118537066891077435401375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16079024711260718290267583 24118537066891077435401375)
    ·
      refine ⟨36177805600336616153102063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24118537066891077435401375 36177805600336616153102063)
      ·
        refine ⟨54266708400504924229653095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36177805600336616153102063 54266708400504924229653095)
        ·
          refine ⟨81400062600757386344479643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54266708400504924229653095 81400062600757386344479643)
          ·
            refine ⟨122100093901136079516719465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81400062600757386344479643 122100093901136079516719465)
            ·
              refine ⟨91575070425852059637539599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122100093901136079516719465 91575070425852059637539599)
              ·
                refine ⟨137362605638778089456309399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91575070425852059637539599 137362605638778089456309399)
                ·
                  refine ⟨206043908458167134184464099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137362605638778089456309399 206043908458167134184464099)
                  ·
                    refine ⟨309065862687250701276696149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 206043908458167134184464099 309065862687250701276696149)
                    ·
                      refine ⟨3621865578366219155586283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 309065862687250701276696149 3621865578366219155586283)
                      ·
                        rfl

theorem cell23_7053558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_7053558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053558 prefixEnd_7053558 := by exact prefixLift 7053558
  have htrace : WordTrace (prefixWord ++ tailWord_7053558) baseStart_7053558 baseEnd_7053558 := by
    simpa [prefixWord, tailWord_7053558, baseEnd_7053558] using wordTrace_append hprefix tailTrace_7053558
  have hstable : (prefixWord ++ tailWord_7053558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053558).length < 2 ^ (prefixWord ++ tailWord_7053558).sum := by decide
  have hdescent : baseEnd_7053558 < baseStart_7053558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053585 : List Nat := [1, 2, 2, 1, 1, 5, 3, 2, 1, 5]
def baseStart_7053585 : Nat := 118140960795 + 7053585 * 2 ^ 59
def prefixEnd_7053585 : Nat := 4983230072969 + 3 ^ 40 * 7053585 * 2
def baseEnd_7053585 : Nat := 1207293147447963516649553

theorem tailTrace_7053585 : CollatzResearch.WordTrace tailWord_7053585 prefixEnd_7053585 1207293147447963516649553 := by
  unfold tailWord_7053585
  simp only [CollatzResearch.WordTrace]
  refine ⟨257265380151073676255514209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171510253434049117503676139 257265380151073676255514209)
  ·
    refine ⟨192949035113305257191635657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257265380151073676255514209 192949035113305257191635657)
    ·
      refine ⟨144711776334978942893726743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192949035113305257191635657 144711776334978942893726743)
      ·
        refine ⟨217067664502468414340590115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144711776334978942893726743 217067664502468414340590115)
        ·
          refine ⟨325601496753702621510885173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217067664502468414340590115 325601496753702621510885173)
          ·
            refine ⟨30525140320659620766645485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 325601496753702621510885173 30525140320659620766645485)
            ·
              refine ⟨11446927620247357787492057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30525140320659620766645485 11446927620247357787492057)
              ·
                refine ⟨8585195715185518340619043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11446927620247357787492057 8585195715185518340619043)
                ·
                  refine ⟨12877793572778277510928565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8585195715185518340619043 12877793572778277510928565)
                  ·
                    refine ⟨1207293147447963516649553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12877793572778277510928565 1207293147447963516649553)
                    ·
                      rfl

theorem cell23_7053585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_7053585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053585 prefixEnd_7053585 := by exact prefixLift 7053585
  have htrace : WordTrace (prefixWord ++ tailWord_7053585) baseStart_7053585 baseEnd_7053585 := by
    simpa [prefixWord, tailWord_7053585, baseEnd_7053585] using wordTrace_append hprefix tailTrace_7053585
  have hstable : (prefixWord ++ tailWord_7053585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053585).length < 2 ^ (prefixWord ++ tailWord_7053585).sum := by decide
  have hdescent : baseEnd_7053585 < baseStart_7053585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053592 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 2, 3, 2]
def baseStart_7053592 : Nat := 118140960795 + 7053592 * 2 ^ 59
def prefixEnd_7053592 : Nat := 4983230072969 + 3 ^ 40 * 7053592 * 2
def baseEnd_7053592 : Nat := 3621883036708472022561127

theorem tailTrace_7053592 : CollatzResearch.WordTrace tailWord_7053592 prefixEnd_7053592 3621883036708472022561127 := by
  unfold tailWord_7053592
  simp only [CollatzResearch.WordTrace]
  refine ⟨128632817731024158225509515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171510423641365544300679353 128632817731024158225509515)
  ·
    refine ⟨192949226596536237338264273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128632817731024158225509515 192949226596536237338264273)
    ·
      refine ⟨144711919947402178003698205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192949226596536237338264273 144711919947402178003698205)
      ·
        refine ⟨54266969980275816751386827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144711919947402178003698205 54266969980275816751386827)
        ·
          refine ⟨81400454970413725127080241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54266969980275816751386827 81400454970413725127080241)
          ·
            refine ⟨61050341227810293845310181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81400454970413725127080241 61050341227810293845310181)
            ·
              refine ⟨11446938980214430095995659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61050341227810293845310181 11446938980214430095995659)
              ·
                refine ⟨17170408470321645143993489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11446938980214430095995659 17170408470321645143993489)
                ·
                  refine ⟨12877806352741233857995117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17170408470321645143993489 12877806352741233857995117)
                  ·
                    refine ⟨4829177382277962696748169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12877806352741233857995117 4829177382277962696748169)
                    ·
                      refine ⟨3621883036708472022561127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4829177382277962696748169 3621883036708472022561127)
                      ·
                        rfl

theorem cell23_7053592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_7053592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053592 prefixEnd_7053592 := by exact prefixLift 7053592
  have htrace : WordTrace (prefixWord ++ tailWord_7053592) baseStart_7053592 baseEnd_7053592 := by
    simpa [prefixWord, tailWord_7053592, baseEnd_7053592] using wordTrace_append hprefix tailTrace_7053592
  have hstable : (prefixWord ++ tailWord_7053592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053592).length < 2 ^ (prefixWord ++ tailWord_7053592).sum := by decide
  have hdescent : baseEnd_7053592 < baseStart_7053592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053615 : List Nat := [1, 1, 2, 1, 2, 1, 5, 4, 2, 4]
def baseStart_7053615 : Nat := 118140960795 + 7053615 * 2 ^ 59
def prefixEnd_7053615 : Nat := 4983230072969 + 3 ^ 40 * 7053615 * 2
def baseEnd_7053615 : Nat := 1207298282254508477524507

theorem tailTrace_7053615 : CollatzResearch.WordTrace tailWord_7053615 prefixEnd_7053615 1207298282254508477524507 := by
  unfold tailWord_7053615
  simp only [CollatzResearch.WordTrace]
  refine ⟨257266474340964991379106299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171510982893976660919404199 257266474340964991379106299)
  ·
    refine ⟨385899711511447487068659449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257266474340964991379106299 385899711511447487068659449)
    ·
      refine ⟨289424783633585615301494587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385899711511447487068659449 289424783633585615301494587)
      ·
        refine ⟨434137175450378422952241881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289424783633585615301494587 434137175450378422952241881)
        ·
          refine ⟨325602881587783817214181411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434137175450378422952241881 325602881587783817214181411)
          ·
            refine ⟨488404322381675725821272117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325602881587783817214181411 488404322381675725821272117)
            ·
              refine ⟨45787905223282099295744261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 488404322381675725821272117 45787905223282099295744261)
              ·
                refine ⟨8585232229365393617952049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45787905223282099295744261 8585232229365393617952049)
                ·
                  refine ⟨6438924172024045213464037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8585232229365393617952049 6438924172024045213464037)
                  ·
                    refine ⟨1207298282254508477524507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6438924172024045213464037 1207298282254508477524507)
                    ·
                      rfl

theorem cell23_7053615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 4].length) (baseStart_7053615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053615 prefixEnd_7053615 := by exact prefixLift 7053615
  have htrace : WordTrace (prefixWord ++ tailWord_7053615) baseStart_7053615 baseEnd_7053615 := by
    simpa [prefixWord, tailWord_7053615, baseEnd_7053615] using wordTrace_append hprefix tailTrace_7053615
  have hstable : (prefixWord ++ tailWord_7053615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053615).length < 2 ^ (prefixWord ++ tailWord_7053615).sum := by decide
  have hdescent : baseEnd_7053615 < baseStart_7053615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053655 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 3]
def baseStart_7053655 : Nat := 118140960795 + 7053655 * 2 ^ 59
def prefixEnd_7053655 : Nat := 4983230072969 + 3 ^ 40 * 7053655 * 2
def baseEnd_7053655 : Nat := 3621915385989705276073337

theorem tailTrace_7053655 : CollatzResearch.WordTrace tailWord_7053655 prefixEnd_7053655 3621915385989705276073337 := by
  unfold tailWord_7053655
  simp only [CollatzResearch.WordTrace]
  refine ⟨257267933260820078210562419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171511955507213385473708279 257267933260820078210562419)
  ·
    refine ⟨385901899891230117315843629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257267933260820078210562419 385901899891230117315843629)
    ·
      refine ⟨144713212459211293993441361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385901899891230117315843629 144713212459211293993441361)
      ·
        refine ⟨108534909344408470495081021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144713212459211293993441361 108534909344408470495081021)
        ·
          refine ⟨40700591004153176435655383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108534909344408470495081021 40700591004153176435655383)
          ·
            refine ⟨61050886506229764653483075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40700591004153176435655383 61050886506229764653483075)
            ·
              refine ⟨91576329759344646980224613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61050886506229764653483075 91576329759344646980224613)
              ·
                refine ⟨17170561829877121308792115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91576329759344646980224613 17170561829877121308792115)
                ·
                  refine ⟨25755842744815681963188173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17170561829877121308792115 25755842744815681963188173)
                  ·
                    refine ⟨9658441029305880736195565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25755842744815681963188173 9658441029305880736195565)
                    ·
                      refine ⟨3621915385989705276073337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9658441029305880736195565 3621915385989705276073337)
                      ·
                        rfl

theorem cell23_7053655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_7053655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053655 prefixEnd_7053655 := by exact prefixLift 7053655
  have htrace : WordTrace (prefixWord ++ tailWord_7053655) baseStart_7053655 baseEnd_7053655 := by
    simpa [prefixWord, tailWord_7053655, baseEnd_7053655] using wordTrace_append hprefix tailTrace_7053655
  have hstable : (prefixWord ++ tailWord_7053655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053655).length < 2 ^ (prefixWord ++ tailWord_7053655).sum := by decide
  have hdescent : baseEnd_7053655 < baseStart_7053655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053686 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_7053686 : Nat := 118140960795 + 7053686 * 2 ^ 59
def prefixEnd_7053686 : Nat := 4983230072969 + 3 ^ 40 * 7053686 * 2
def baseEnd_7053686 : Nat := 3621931303889994654785695

theorem tailTrace_7053686 : CollatzResearch.WordTrace tailWord_7053686 prefixEnd_7053686 3621931303889994654785695 := by
  unfold tailWord_7053686
  simp only [CollatzResearch.WordTrace]
  refine ⟨16079316495231735656558807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171512709282471847003293941 16079316495231735656558807)
  ·
    refine ⟨24118974742847603484838211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16079316495231735656558807 24118974742847603484838211)
    ·
      refine ⟨36178462114271405227257317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24118974742847603484838211 36178462114271405227257317)
      ·
        refine ⟨6783461646425888480110747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36178462114271405227257317 6783461646425888480110747)
        ·
          refine ⟨10175192469638832720166121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6783461646425888480110747 10175192469638832720166121)
          ·
            refine ⟨7631394352229124540124591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10175192469638832720166121 7631394352229124540124591)
            ·
              refine ⟨11447091528343686810186887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7631394352229124540124591 11447091528343686810186887)
              ·
                refine ⟨17170637292515530215280331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11447091528343686810186887 17170637292515530215280331)
                ·
                  refine ⟨25755955938773295322920497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17170637292515530215280331 25755955938773295322920497)
                  ·
                    refine ⟨19316966954079971492190373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25755955938773295322920497 19316966954079971492190373)
                    ·
                      refine ⟨3621931303889994654785695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19316966954079971492190373 3621931303889994654785695)
                      ·
                        rfl

theorem cell23_7053686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_7053686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053686 prefixEnd_7053686 := by exact prefixLift 7053686
  have htrace : WordTrace (prefixWord ++ tailWord_7053686) baseStart_7053686 baseEnd_7053686 := by
    simpa [prefixWord, tailWord_7053686, baseEnd_7053686] using wordTrace_append hprefix tailTrace_7053686
  have hstable : (prefixWord ++ tailWord_7053686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053686).length < 2 ^ (prefixWord ++ tailWord_7053686).sum := by decide
  have hdescent : baseEnd_7053686 < baseStart_7053686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053829 : List Nat := [1, 3, 1, 1, 2, 2, 3, 5, 1, 4]
def baseStart_7053829 : Nat := 118140960795 + 7053829 * 2 ^ 59
def prefixEnd_7053829 : Nat := 4983230072969 + 3 ^ 40 * 7053829 * 2
def baseEnd_7053829 : Nat := 1207334910541195865099179

theorem tailTrace_7053829 : CollatzResearch.WordTrace tailWord_7053829 prefixEnd_7053829 1207334910541195865099179 := by
  unfold tailWord_7053829
  simp only [CollatzResearch.WordTrace]
  refine ⟨257274279562189705927396541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171516186374793137284931027 257274279562189705927396541)
  ·
    refine ⟨96477854835821139722773703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257274279562189705927396541 96477854835821139722773703)
    ·
      refine ⟨144716782253731709584160555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96477854835821139722773703 144716782253731709584160555)
      ·
        refine ⟨217075173380597564376240833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144716782253731709584160555 217075173380597564376240833)
        ·
          refine ⟨162806380035448173282180625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217075173380597564376240833 162806380035448173282180625)
          ·
            refine ⟨122104785026586129961635469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162806380035448173282180625 122104785026586129961635469)
            ·
              refine ⟨45789294384969798735613301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122104785026586129961635469 45789294384969798735613301)
              ·
                refine ⟨4292746348590918631463747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45789294384969798735613301 4292746348590918631463747)
                ·
                  refine ⟨6439119522886377947195621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4292746348590918631463747 6439119522886377947195621)
                  ·
                    refine ⟨1207334910541195865099179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6439119522886377947195621 1207334910541195865099179)
                    ·
                      rfl

theorem cell23_7053829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_7053829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053829 prefixEnd_7053829 := by exact prefixLift 7053829
  have htrace : WordTrace (prefixWord ++ tailWord_7053829) baseStart_7053829 baseEnd_7053829 := by
    simpa [prefixWord, tailWord_7053829, baseEnd_7053829] using wordTrace_append hprefix tailTrace_7053829
  have hstable : (prefixWord ++ tailWord_7053829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053829).length < 2 ^ (prefixWord ++ tailWord_7053829).sum := by decide
  have hdescent : baseEnd_7053829 < baseStart_7053829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053845 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_7053845 : Nat := 118140960795 + 7053845 * 2 ^ 59
def prefixEnd_7053845 : Nat := 4983230072969 + 3 ^ 40 * 7053845 * 2
def baseEnd_7053845 : Nat := 3622012947314059532697463

theorem tailTrace_7053845 : CollatzResearch.WordTrace tailWord_7053845 prefixEnd_7053845 3622012947314059532697463 := by
  unfold tailWord_7053845
  simp only [CollatzResearch.WordTrace]
  refine ⟨257274863130131740659978989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171516575420087827106652659 257274863130131740659978989)
  ·
    refine ⟨96478073673799402747492121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257274863130131740659978989 96478073673799402747492121)
    ·
      refine ⟨72358555255349552060619091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96478073673799402747492121 72358555255349552060619091)
      ·
        refine ⟨108537832883024328090928637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72358555255349552060619091 108537832883024328090928637)
        ·
          refine ⟨40701687331134123034098239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108537832883024328090928637 40701687331134123034098239)
          ·
            refine ⟨61052530996701184551147359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40701687331134123034098239 61052530996701184551147359)
            ·
              refine ⟨91578796495051776826721039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61052530996701184551147359 91578796495051776826721039)
              ·
                refine ⟨137368194742577665240081559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91578796495051776826721039 137368194742577665240081559)
                ·
                  refine ⟨206052292113866497860122339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137368194742577665240081559 206052292113866497860122339)
                  ·
                    refine ⟨309078438170799746790183509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 206052292113866497860122339 309078438170799746790183509)
                    ·
                      refine ⟨3622012947314059532697463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 309078438170799746790183509 3622012947314059532697463)
                      ·
                        rfl

theorem cell23_7053845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_7053845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053845 prefixEnd_7053845 := by exact prefixLift 7053845
  have htrace : WordTrace (prefixWord ++ tailWord_7053845) baseStart_7053845 baseEnd_7053845 := by
    simpa [prefixWord, tailWord_7053845, baseEnd_7053845] using wordTrace_append hprefix tailTrace_7053845
  have hstable : (prefixWord ++ tailWord_7053845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053845).length < 2 ^ (prefixWord ++ tailWord_7053845).sum := by decide
  have hdescent : baseEnd_7053845 < baseStart_7053845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053859 : List Nat := [1, 1, 1, 4, 4, 2, 3, 1, 6]
def baseStart_7053859 : Nat := 118140960795 + 7053859 * 2 ^ 59
def prefixEnd_7053859 : Nat := 4983230072969 + 3 ^ 40 * 7053859 * 2
def baseEnd_7053859 : Nat := 402446681782580275324711

theorem tailTrace_7053859 : CollatzResearch.WordTrace tailWord_7053859 prefixEnd_7053859 402446681782580275324711 := by
  unfold tailWord_7053859
  simp only [CollatzResearch.WordTrace]
  refine ⟨257275373752081021050988631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171516915834720680700659087 257275373752081021050988631)
  ·
    refine ⟨385913060628121531576482947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257275373752081021050988631 385913060628121531576482947)
    ·
      refine ⟨578869590942182297364724421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385913060628121531576482947 578869590942182297364724421)
      ·
        refine ⟨108538048301659180755885829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 578869590942182297364724421 108538048301659180755885829)
        ·
          refine ⟨20350884056561096391728593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108538048301659180755885829 20350884056561096391728593)
          ·
            refine ⟨15263163042420822293796445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20350884056561096391728593 15263163042420822293796445)
            ·
              refine ⟨5723686140907808360173667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15263163042420822293796445 5723686140907808360173667)
              ·
                refine ⟨8585529211361712540260501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5723686140907808360173667 8585529211361712540260501)
                ·
                  refine ⟨402446681782580275324711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8585529211361712540260501 402446681782580275324711)
                  ·
                    rfl

theorem cell23_7053859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 6].length) (baseStart_7053859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053859 prefixEnd_7053859 := by exact prefixLift 7053859
  have htrace : WordTrace (prefixWord ++ tailWord_7053859) baseStart_7053859 baseEnd_7053859 := by
    simpa [prefixWord, tailWord_7053859, baseEnd_7053859] using wordTrace_append hprefix tailTrace_7053859
  have hstable : (prefixWord ++ tailWord_7053859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053859).length < 2 ^ (prefixWord ++ tailWord_7053859).sum := by decide
  have hdescent : baseEnd_7053859 < baseStart_7053859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053872 : List Nat := [2, 1, 1, 1, 2, 3, 3, 4, 1, 5]
def baseStart_7053872 : Nat := 118140960795 + 7053872 * 2 ^ 59
def prefixEnd_7053872 : Nat := 4983230072969 + 3 ^ 40 * 7053872 * 2
def baseEnd_7053872 : Nat := 1207342270430576975686613

theorem tailTrace_7053872 : CollatzResearch.WordTrace tailWord_7053872 prefixEnd_7053872 1207342270430576975686613 := by
  unfold tailWord_7053872
  simp only [CollatzResearch.WordTrace]
  refine ⟨128637923950516962135605935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171517231934022616180807913 128637923950516962135605935)
  ·
    refine ⟨192956885925775443203408903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128637923950516962135605935 192956885925775443203408903)
    ·
      refine ⟨289435328888663164805113355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192956885925775443203408903 289435328888663164805113355)
      ·
        refine ⟨434152993332994747207670033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289435328888663164805113355 434152993332994747207670033)
        ·
          refine ⟨325614744999746060405752525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434152993332994747207670033 325614744999746060405752525)
          ·
            refine ⟨122105529374904772652157197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325614744999746060405752525 122105529374904772652157197)
            ·
              refine ⟨45789573515589289744558949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122105529374904772652157197 45789573515589289744558949)
              ·
                refine ⟨8585545034172991827104803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45789573515589289744558949 8585545034172991827104803)
                ·
                  refine ⟨12878317551259487740657205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8585545034172991827104803 12878317551259487740657205)
                  ·
                    refine ⟨1207342270430576975686613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12878317551259487740657205 1207342270430576975686613)
                    ·
                      rfl

theorem cell23_7053872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 1, 5].length) (baseStart_7053872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053872 prefixEnd_7053872 := by exact prefixLift 7053872
  have htrace : WordTrace (prefixWord ++ tailWord_7053872) baseStart_7053872 baseEnd_7053872 := by
    simpa [prefixWord, tailWord_7053872, baseEnd_7053872] using wordTrace_append hprefix tailTrace_7053872
  have hstable : (prefixWord ++ tailWord_7053872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053872).length < 2 ^ (prefixWord ++ tailWord_7053872).sum := by decide
  have hdescent : baseEnd_7053872 < baseStart_7053872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053879 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 2, 3, 2]
def baseStart_7053879 : Nat := 118140960795 + 7053879 * 2 ^ 59
def prefixEnd_7053879 : Nat := 4983230072969 + 3 ^ 40 * 7053879 * 2
def baseEnd_7053879 : Nat := 3622030405656312399672307

theorem tailTrace_7053879 : CollatzResearch.WordTrace tailWord_7053879 prefixEnd_7053879 3622030405656312399672307 := by
  unfold tailWord_7053879
  simp only [CollatzResearch.WordTrace]
  refine ⟨257276103212008564466716691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171517402141339042977811127 257276103212008564466716691)
  ·
    refine ⟨385914154818012846700075037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257276103212008564466716691 385914154818012846700075037)
    ·
      refine ⟨144717808056754817512528139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385914154818012846700075037 144717808056754817512528139)
      ·
        refine ⟨217076712085132226268792209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144717808056754817512528139 217076712085132226268792209)
        ·
          refine ⟨162807534063849169701594157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217076712085132226268792209 162807534063849169701594157)
          ·
            refine ⟨61052825273943438638097809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162807534063849169701594157 61052825273943438638097809)
            ·
              refine ⟨45789618955457578978573357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61052825273943438638097809 45789618955457578978573357)
              ·
                refine ⟨17171107108296592116965009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45789618955457578978573357 17171107108296592116965009)
                ·
                  refine ⟨12878330331222444087723757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17171107108296592116965009 12878330331222444087723757)
                  ·
                    refine ⟨4829373874208416532896409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12878330331222444087723757 4829373874208416532896409)
                    ·
                      refine ⟨3622030405656312399672307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4829373874208416532896409 3622030405656312399672307)
                      ·
                        rfl

theorem cell23_7053879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 3, 2].length) (baseStart_7053879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053879 prefixEnd_7053879 := by exact prefixLift 7053879
  have htrace : WordTrace (prefixWord ++ tailWord_7053879) baseStart_7053879 baseEnd_7053879 := by
    simpa [prefixWord, tailWord_7053879, baseEnd_7053879] using wordTrace_append hprefix tailTrace_7053879
  have hstable : (prefixWord ++ tailWord_7053879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053879).length < 2 ^ (prefixWord ++ tailWord_7053879).sum := by decide
  have hdescent : baseEnd_7053879 < baseStart_7053879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053889 : List Nat := [1, 2, 5, 1, 1, 2, 2, 3, 1, 5]
def baseStart_7053889 : Nat := 118140960795 + 7053889 * 2 ^ 59
def prefixEnd_7053889 : Nat := 4983230072969 + 3 ^ 40 * 7053889 * 2
def baseEnd_7053889 : Nat := 1207345180154285786849087

theorem tailTrace_7053889 : CollatzResearch.WordTrace tailWord_7053889 prefixEnd_7053889 1207345180154285786849087 := by
  unfold tailWord_7053889
  simp only [CollatzResearch.WordTrace]
  refine ⟨257276467941972336174580721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171517645294648224116387147 257276467941972336174580721)
  ·
    refine ⟨192957350956479252130935541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257276467941972336174580721 192957350956479252130935541)
    ·
      refine ⟨18089751652169929887275207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192957350956479252130935541 18089751652169929887275207)
      ·
        refine ⟨27134627478254894830912811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18089751652169929887275207 27134627478254894830912811)
        ·
          refine ⟨40701941217382342246369217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27134627478254894830912811 40701941217382342246369217)
          ·
            refine ⟨30526455913036756684776913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40701941217382342246369217 30526455913036756684776913)
            ·
              refine ⟨22894841934777567513582685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30526455913036756684776913 22894841934777567513582685)
              ·
                refine ⟨8585565725541587817593507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22894841934777567513582685 8585565725541587817593507)
                ·
                  refine ⟨12878348588312381726390261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8585565725541587817593507 12878348588312381726390261)
                  ·
                    refine ⟨1207345180154285786849087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12878348588312381726390261 1207345180154285786849087)
                    ·
                      rfl

theorem cell23_7053889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_7053889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053889 prefixEnd_7053889 := by exact prefixLift 7053889
  have htrace : WordTrace (prefixWord ++ tailWord_7053889) baseStart_7053889 baseEnd_7053889 := by
    simpa [prefixWord, tailWord_7053889, baseEnd_7053889] using wordTrace_append hprefix tailTrace_7053889
  have hstable : (prefixWord ++ tailWord_7053889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053889).length < 2 ^ (prefixWord ++ tailWord_7053889).sum := by decide
  have hdescent : baseEnd_7053889 < baseStart_7053889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053912 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 1, 1, 5]
def baseStart_7053912 : Nat := 118140960795 + 7053912 * 2 ^ 59
def prefixEnd_7053912 : Nat := 4983230072969 + 3 ^ 40 * 7053912 * 2
def baseEnd_7053912 : Nat := 3622047350517910770559655

theorem tailTrace_7053912 : CollatzResearch.WordTrace tailWord_7053912 prefixEnd_7053912 3622047350517910770559655 := by
  unfold tailWord_7053912
  simp only [CollatzResearch.WordTrace]
  refine ⟨128638653410444505551333995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171518204547259340735111993 128638653410444505551333995)
  ·
    refine ⟨192957980115666758327000993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128638653410444505551333995 192957980115666758327000993)
    ·
      refine ⟨144718485086750068745250745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192957980115666758327000993 144718485086750068745250745)
      ·
        refine ⟨108538863815062551558938059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144718485086750068745250745 108538863815062551558938059)
        ·
          refine ⟨162808295722593827338407089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108538863815062551558938059 162808295722593827338407089)
          ·
            refine ⟨122106221791945370503805317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162808295722593827338407089 122106221791945370503805317)
            ·
              refine ⟨22894916585989756969463497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122106221791945370503805317 22894916585989756969463497)
              ·
                refine ⟨17171187439492317727097623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22894916585989756969463497 17171187439492317727097623)
                ·
                  refine ⟨25756781159238476590646435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17171187439492317727097623 25756781159238476590646435)
                  ·
                    refine ⟨38635171738857714885969653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25756781159238476590646435 38635171738857714885969653)
                    ·
                      refine ⟨3622047350517910770559655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38635171738857714885969653 3622047350517910770559655)
                      ·
                        rfl

theorem cell23_7053912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_7053912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053912 prefixEnd_7053912 := by exact prefixLift 7053912
  have htrace : WordTrace (prefixWord ++ tailWord_7053912) baseStart_7053912 baseEnd_7053912 := by
    simpa [prefixWord, tailWord_7053912, baseEnd_7053912] using wordTrace_append hprefix tailTrace_7053912
  have hstable : (prefixWord ++ tailWord_7053912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053912).length < 2 ^ (prefixWord ++ tailWord_7053912).sum := by decide
  have hdescent : baseEnd_7053912 < baseStart_7053912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053954 : List Nat := [3, 4, 3, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_7053954 : Nat := 118140960795 + 7053954 * 2 ^ 59
def prefixEnd_7053954 : Nat := 4983230072969 + 3 ^ 40 * 7053954 * 2
def baseEnd_7053954 : Nat := 3622068916705399606234463

theorem tailTrace_7053954 : CollatzResearch.WordTrace tailWord_7053954 prefixEnd_7053954 3622068916705399606234463 := by
  unfold tailWord_7053954
  simp only [CollatzResearch.WordTrace]
  refine ⟨64319709671684213068924229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171519225791157901517131277 64319709671684213068924229)
  ·
    refine ⟨12059945563440789950423293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64319709671684213068924229 12059945563440789950423293)
    ·
      refine ⟨4522479586290296231408735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12059945563440789950423293 4522479586290296231408735)
      ·
        refine ⟨6783719379435444347113103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4522479586290296231408735 6783719379435444347113103)
        ·
          refine ⟨10175579069153166520669655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6783719379435444347113103 10175579069153166520669655)
          ·
            refine ⟨15263368603729749781004483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10175579069153166520669655 15263368603729749781004483)
            ·
              refine ⟨22895052905594624671506725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15263368603729749781004483 22895052905594624671506725)
              ·
                refine ⟨4292822419798992125907511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22895052905594624671506725 4292822419798992125907511)
                ·
                  refine ⟨6439233629698488188861267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4292822419798992125907511 6439233629698488188861267)
                  ·
                    refine ⟨9658850444547732283291901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6439233629698488188861267 9658850444547732283291901)
                    ·
                      refine ⟨3622068916705399606234463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9658850444547732283291901 3622068916705399606234463)
                      ·
                        rfl

theorem cell23_7053954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_7053954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053954 prefixEnd_7053954 := by exact prefixLift 7053954
  have htrace : WordTrace (prefixWord ++ tailWord_7053954) baseStart_7053954 baseEnd_7053954 := by
    simpa [prefixWord, tailWord_7053954, baseEnd_7053954] using wordTrace_append hprefix tailTrace_7053954
  have hstable : (prefixWord ++ tailWord_7053954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053954).length < 2 ^ (prefixWord ++ tailWord_7053954).sum := by decide
  have hdescent : baseEnd_7053954 < baseStart_7053954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053976 : List Nat := [2, 1, 2, 4, 1, 1, 1, 5, 2, 1, 3]
def baseStart_7053976 : Nat := 118140960795 + 7053976 * 2 ^ 59
def prefixEnd_7053976 : Nat := 4983230072969 + 3 ^ 40 * 7053976 * 2
def baseEnd_7053976 : Nat := 3622080213279798520159361

theorem tailTrace_7053976 : CollatzResearch.WordTrace tailWord_7053976 prefixEnd_7053976 3622080213279798520159361 := by
  unfold tailWord_7053976
  simp only [CollatzResearch.WordTrace]
  refine ⟨128639820546328575016498891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171519760728438100021998521 128639820546328575016498891)
  ·
    refine ⟨192959730819492862524748337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128639820546328575016498891 192959730819492862524748337)
    ·
      refine ⟨144719798114619646893561253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192959730819492862524748337 144719798114619646893561253)
      ·
        refine ⟨27134962146491183792542735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144719798114619646893561253 27134962146491183792542735)
        ·
          refine ⟨40702443219736775688814103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27134962146491183792542735 40702443219736775688814103)
          ·
            refine ⟨61053664829605163533221155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40702443219736775688814103 61053664829605163533221155)
            ·
              refine ⟨91580497244407745299831733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61053664829605163533221155 91580497244407745299831733)
              ·
                refine ⟨8585671616663226121859225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91580497244407745299831733 8585671616663226121859225)
                ·
                  refine ⟨6439253712497419591394419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8585671616663226121859225 6439253712497419591394419)
                  ·
                    refine ⟨9658880568746129387091629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6439253712497419591394419 9658880568746129387091629)
                    ·
                      refine ⟨3622080213279798520159361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9658880568746129387091629 3622080213279798520159361)
                      ·
                        rfl

theorem cell23_7053976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_7053976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053976 prefixEnd_7053976 := by exact prefixLift 7053976
  have htrace : WordTrace (prefixWord ++ tailWord_7053976) baseStart_7053976 baseEnd_7053976 := by
    simpa [prefixWord, tailWord_7053976, baseEnd_7053976] using wordTrace_append hprefix tailTrace_7053976
  have hstable : (prefixWord ++ tailWord_7053976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053976).length < 2 ^ (prefixWord ++ tailWord_7053976).sum := by decide
  have hdescent : baseEnd_7053976 < baseStart_7053976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7053994 : List Nat := [3, 1, 5, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_7053994 : Nat := 118140960795 + 7053994 * 2 ^ 59
def prefixEnd_7053994 : Nat := 4983230072969 + 3 ^ 40 * 7053994 * 2
def baseEnd_7053994 : Nat := 3622089455931579449734279

theorem tailTrace_7053994 : CollatzResearch.WordTrace tailWord_7053994 prefixEnd_7053994 3622089455931579449734279 := by
  unfold tailWord_7053994
  simp only [CollatzResearch.WordTrace]
  refine ⟨64320074401647984776788259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171520198404394626071435357 64320074401647984776788259)
  ·
    refine ⟨96480111602471977165182389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64320074401647984776788259 96480111602471977165182389)
    ·
      refine ⟨9045010462731747859235849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96480111602471977165182389 9045010462731747859235849)
      ·
        refine ⟨6783757847048810894426887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9045010462731747859235849 6783757847048810894426887)
        ·
          refine ⟨10175636770573216341640331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6783757847048810894426887 10175636770573216341640331)
          ·
            refine ⟨15263455155859824512460497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10175636770573216341640331 15263455155859824512460497)
            ·
              refine ⟨11447591366894868384345373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15263455155859824512460497 11447591366894868384345373)
              ·
                refine ⟨4292846762585575644129515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11447591366894868384345373 4292846762585575644129515)
                ·
                  refine ⟨6439270143878363466194273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4292846762585575644129515 6439270143878363466194273)
                  ·
                    refine ⟨4829452607908772599645705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6439270143878363466194273 4829452607908772599645705)
                    ·
                      refine ⟨3622089455931579449734279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4829452607908772599645705 3622089455931579449734279)
                      ·
                        rfl

theorem cell23_7053994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_7053994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7053994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7053994 prefixEnd_7053994 := by exact prefixLift 7053994
  have htrace : WordTrace (prefixWord ++ tailWord_7053994) baseStart_7053994 baseEnd_7053994 := by
    simpa [prefixWord, tailWord_7053994, baseEnd_7053994] using wordTrace_append hprefix tailTrace_7053994
  have hstable : (prefixWord ++ tailWord_7053994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7053994).length < 2 ^ (prefixWord ++ tailWord_7053994).sum := by decide
  have hdescent : baseEnd_7053994 < baseStart_7053994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7053994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054002 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_7054002 : Nat := 118140960795 + 7054002 * 2 ^ 59
def prefixEnd_7054002 : Nat := 4983230072969 + 3 ^ 40 * 7054002 * 2
def baseEnd_7054002 : Nat := 3622093563776815418434241

theorem tailTrace_7054002 : CollatzResearch.WordTrace tailWord_7054002 prefixEnd_7054002 3622093563776815418434241 := by
  unfold tailWord_7054002
  simp only [CollatzResearch.WordTrace]
  refine ⟨64320147347640739118361065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171520392927041970982296173 64320147347640739118361065)
  ·
    refine ⟨48240110510730554338770799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64320147347640739118361065 48240110510730554338770799)
    ·
      refine ⟨72360165766095831508156199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48240110510730554338770799 72360165766095831508156199)
      ·
        refine ⟨108540248649143747262234299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72360165766095831508156199 108540248649143747262234299)
        ·
          refine ⟨162810372973715620893351449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108540248649143747262234299 162810372973715620893351449)
          ·
            refine ⟨122107779730286715670013587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162810372973715620893351449 122107779730286715670013587)
            ·
              refine ⟨183161669595430073505020381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122107779730286715670013587 183161669595430073505020381)
              ·
                refine ⟨68685626098286277564382643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183161669595430073505020381 68685626098286277564382643)
                ·
                  refine ⟨103028439147429416346573965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68685626098286277564382643 103028439147429416346573965)
                  ·
                    refine ⟨38635664680286031129965237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103028439147429416346573965 38635664680286031129965237)
                    ·
                      refine ⟨3622093563776815418434241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38635664680286031129965237 3622093563776815418434241)
                      ·
                        rfl

theorem cell23_7054002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_7054002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054002 prefixEnd_7054002 := by exact prefixLift 7054002
  have htrace : WordTrace (prefixWord ++ tailWord_7054002) baseStart_7054002 baseEnd_7054002 := by
    simpa [prefixWord, tailWord_7054002, baseEnd_7054002] using wordTrace_append hprefix tailTrace_7054002
  have hstable : (prefixWord ++ tailWord_7054002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054002).length < 2 ^ (prefixWord ++ tailWord_7054002).sum := by decide
  have hdescent : baseEnd_7054002 < baseStart_7054002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054003 : List Nat := [1, 1, 1, 2, 3, 4, 4, 1, 1, 3, 2]
def baseStart_7054003 : Nat := 118140960795 + 7054003 * 2 ^ 59
def prefixEnd_7054003 : Nat := 4983230072969 + 3 ^ 40 * 7054003 * 2
def baseEnd_7054003 : Nat := 3622094077257469914521737

theorem tailTrace_7054003 : CollatzResearch.WordTrace tailWord_7054003 prefixEnd_7054003 3622094077257469914521737 := by
  unfold tailWord_7054003
  simp only [CollatzResearch.WordTrace]
  refine ⟨257280625863559333644230663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171520417242372889096153775 257280625863559333644230663)
  ·
    refine ⟨385920938795339000466345995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257280625863559333644230663 385920938795339000466345995)
    ·
      refine ⟨578881408193008500699518993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385920938795339000466345995 578881408193008500699518993)
      ·
        refine ⟨434161056144756375524639245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578881408193008500699518993 434161056144756375524639245)
        ·
          refine ⟨162810396054283640821739717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434161056144756375524639245 162810396054283640821739717)
          ·
            refine ⟨30526949260178182654076197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162810396054283640821739717 30526949260178182654076197)
            ·
              refine ⟨5723802986283409247639287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30526949260178182654076197 5723802986283409247639287)
              ·
                refine ⟨8585704479425113871458931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5723802986283409247639287 8585704479425113871458931)
                ·
                  refine ⟨12878556719137670807188397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8585704479425113871458931 12878556719137670807188397)
                  ·
                    refine ⟨4829458769676626552695649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12878556719137670807188397 4829458769676626552695649)
                    ·
                      refine ⟨3622094077257469914521737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4829458769676626552695649 3622094077257469914521737)
                      ·
                        rfl

theorem cell23_7054003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 1, 3, 2].length) (baseStart_7054003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054003 prefixEnd_7054003 := by exact prefixLift 7054003
  have htrace : WordTrace (prefixWord ++ tailWord_7054003) baseStart_7054003 baseEnd_7054003 := by
    simpa [prefixWord, tailWord_7054003, baseEnd_7054003] using wordTrace_append hprefix tailTrace_7054003
  have hstable : (prefixWord ++ tailWord_7054003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054003).length < 2 ^ (prefixWord ++ tailWord_7054003).sum := by decide
  have hdescent : baseEnd_7054003 < baseStart_7054003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054059 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 1, 7, 2]
def baseStart_7054059 : Nat := 118140960795 + 7054059 * 2 ^ 59
def prefixEnd_7054059 : Nat := 4983230072969 + 3 ^ 40 * 7054059 * 2
def baseEnd_7054059 : Nat := 3622122832174121695421479

theorem tailTrace_7054059 : CollatzResearch.WordTrace tailWord_7054059 prefixEnd_7054059 3622122832174121695421479 := by
  unfold tailWord_7054059
  simp only [CollatzResearch.WordTrace]
  refine ⟨257282668351356455208269231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171521778900904303472179487 257282668351356455208269231)
  ·
    refine ⟨385924002527034682812403847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257282668351356455208269231 385924002527034682812403847)
    ·
      refine ⟨578886003790552024218605771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385924002527034682812403847 578886003790552024218605771)
      ·
        refine ⟨868329005685828036327908657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578886003790552024218605771 868329005685828036327908657)
        ·
          refine ⟨651246754264371027245931493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 868329005685828036327908657 651246754264371027245931493)
          ·
            refine ⟨122108766424569567608612155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 651246754264371027245931493 122108766424569567608612155)
            ·
              refine ⟨183163149636854351412918233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122108766424569567608612155 183163149636854351412918233)
              ·
                refine ⟨137372362227640763559688675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183163149636854351412918233 137372362227640763559688675)
                ·
                  refine ⟨206058543341461145339533013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137372362227640763559688675 206058543341461145339533013)
                  ·
                    refine ⟨4829497109565495593895305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 206058543341461145339533013 4829497109565495593895305)
                    ·
                      refine ⟨3622122832174121695421479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4829497109565495593895305 3622122832174121695421479)
                      ·
                        rfl

theorem cell23_7054059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 7, 2].length) (baseStart_7054059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054059 prefixEnd_7054059 := by exact prefixLift 7054059
  have htrace : WordTrace (prefixWord ++ tailWord_7054059) baseStart_7054059 baseEnd_7054059 := by
    simpa [prefixWord, tailWord_7054059, baseEnd_7054059] using wordTrace_append hprefix tailTrace_7054059
  have hstable : (prefixWord ++ tailWord_7054059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054059).length < 2 ^ (prefixWord ++ tailWord_7054059).sum := by decide
  have hdescent : baseEnd_7054059 < baseStart_7054059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054099 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 5, 4]
def baseStart_7054099 : Nat := 118140960795 + 7054099 * 2 ^ 59
def prefixEnd_7054099 : Nat := 4983230072969 + 3 ^ 40 * 7054099 * 2
def baseEnd_7054099 : Nat := 1207381123800100512973765

theorem tailTrace_7054099 : CollatzResearch.WordTrace tailWord_7054099 prefixEnd_7054099 1207381123800100512973765 := by
  unfold tailWord_7054099
  simp only [CollatzResearch.WordTrace]
  refine ⟨257284127271211542039725351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171522751514141028026483567 257284127271211542039725351)
  ·
    refine ⟨385926190906817313059588027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257284127271211542039725351 385926190906817313059588027)
    ·
      refine ⟨578889286360225969589382041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385926190906817313059588027 578889286360225969589382041)
      ·
        refine ⟨434166964770169477192036531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578889286360225969589382041 434166964770169477192036531)
        ·
          refine ⟨651250447155254215788054797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434166964770169477192036531 651250447155254215788054797)
          ·
            refine ⟨244218917683220330920520549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 651250447155254215788054797 244218917683220330920520549)
            ·
              refine ⟨45791047065603812047597603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244218917683220330920520549 45791047065603812047597603)
              ·
                refine ⟨68686570598405718071396405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45791047065603812047597603 68686570598405718071396405)
                ·
                  refine ⟨6439365993600536069193413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68686570598405718071396405 6439365993600536069193413)
                  ·
                    refine ⟨1207381123800100512973765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6439365993600536069193413 1207381123800100512973765)
                    ·
                      rfl

theorem cell23_7054099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 4].length) (baseStart_7054099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054099 prefixEnd_7054099 := by exact prefixLift 7054099
  have htrace : WordTrace (prefixWord ++ tailWord_7054099) baseStart_7054099 baseEnd_7054099 := by
    simpa [prefixWord, tailWord_7054099, baseEnd_7054099] using wordTrace_append hprefix tailTrace_7054099
  have hstable : (prefixWord ++ tailWord_7054099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054099).length < 2 ^ (prefixWord ++ tailWord_7054099).sum := by decide
  have hdescent : baseEnd_7054099 < baseStart_7054099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054106 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4]
def baseStart_7054106 : Nat := 118140960795 + 7054106 * 2 ^ 59
def prefixEnd_7054106 : Nat := 4983230072969 + 3 ^ 40 * 7054106 * 2
def baseEnd_7054106 : Nat := 3622146965764883011533763

theorem tailTrace_7054106 : CollatzResearch.WordTrace tailWord_7054106 prefixEnd_7054106 3622146965764883011533763 := by
  unfold tailWord_7054106
  simp only [CollatzResearch.WordTrace]
  refine ⟨64321095645546545558807543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171522921721457454823486781 64321095645546545558807543)
  ·
    refine ⟨96481643468319818338211315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64321095645546545558807543 96481643468319818338211315)
    ·
      refine ⟨144722465202479727507316973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96481643468319818338211315 144722465202479727507316973)
      ·
        refine ⟨54270924450929897815243865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144722465202479727507316973 54270924450929897815243865)
        ·
          refine ⟨40703193338197423361432899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54270924450929897815243865 40703193338197423361432899)
          ·
            refine ⟨61054790007296135042149349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40703193338197423361432899 61054790007296135042149349)
            ·
              refine ⟨11447773126368025320403003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61054790007296135042149349 11447773126368025320403003)
              ·
                refine ⟨17171659689552037980604505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11447773126368025320403003 17171659689552037980604505)
                ·
                  refine ⟨12878744767164028485453379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17171659689552037980604505 12878744767164028485453379)
                  ·
                    refine ⟨19318117150746042728180069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12878744767164028485453379 19318117150746042728180069)
                    ·
                      refine ⟨3622146965764883011533763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19318117150746042728180069 3622146965764883011533763)
                      ·
                        rfl

theorem cell23_7054106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_7054106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054106 prefixEnd_7054106 := by exact prefixLift 7054106
  have htrace : WordTrace (prefixWord ++ tailWord_7054106) baseStart_7054106 baseEnd_7054106 := by
    simpa [prefixWord, tailWord_7054106, baseEnd_7054106] using wordTrace_append hprefix tailTrace_7054106
  have hstable : (prefixWord ++ tailWord_7054106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054106).length < 2 ^ (prefixWord ++ tailWord_7054106).sum := by decide
  have hdescent : baseEnd_7054106 < baseStart_7054106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054157 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_7054157 : Nat := 118140960795 + 7054157 * 2 ^ 59
def prefixEnd_7054157 : Nat := 4983230072969 + 3 ^ 40 * 7054157 * 2
def baseEnd_7054157 : Nat := 3622173153278262311996029

theorem tailTrace_7054157 : CollatzResearch.WordTrace tailWord_7054157 prefixEnd_7054157 3622173153278262311996029 := by
  unfold tailWord_7054157
  simp only [CollatzResearch.WordTrace]
  refine ⟨257286242705001417945336725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171524161803334278630224483 257286242705001417945336725)
  ·
    refine ⟨12060292626796941466187659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 257286242705001417945336725 12060292626796941466187659)
    ·
      refine ⟨18090438940195412199281489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12060292626796941466187659 18090438940195412199281489)
      ·
        refine ⟨13567829205146559149461117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18090438940195412199281489 13567829205146559149461117)
        ·
          refine ⟨5087935951929959681047919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13567829205146559149461117 5087935951929959681047919)
          ·
            refine ⟨7631903927894939521571879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5087935951929959681047919 7631903927894939521571879)
            ·
              refine ⟨11447855891842409282357819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7631903927894939521571879 11447855891842409282357819)
              ·
                refine ⟨17171783837763613923536729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11447855891842409282357819 17171783837763613923536729)
                ·
                  refine ⟨12878837878322710442652547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17171783837763613923536729 12878837878322710442652547)
                  ·
                    refine ⟨19318256817484065663978821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12878837878322710442652547 19318256817484065663978821)
                    ·
                      refine ⟨3622173153278262311996029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19318256817484065663978821 3622173153278262311996029)
                      ·
                        rfl

theorem cell23_7054157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_7054157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054157 prefixEnd_7054157 := by exact prefixLift 7054157
  have htrace : WordTrace (prefixWord ++ tailWord_7054157) baseStart_7054157 baseEnd_7054157 := by
    simpa [prefixWord, tailWord_7054157, baseEnd_7054157] using wordTrace_append hprefix tailTrace_7054157
  have hstable : (prefixWord ++ tailWord_7054157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054157).length < 2 ^ (prefixWord ++ tailWord_7054157).sum := by decide
  have hdescent : baseEnd_7054157 < baseStart_7054157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054176 : List Nat := [2, 1, 1, 3, 3, 1, 3, 3, 1, 5]
def baseStart_7054176 : Nat := 118140960795 + 7054176 * 2 ^ 59
def prefixEnd_7054176 : Nat := 4983230072969 + 3 ^ 40 * 7054176 * 2
def baseEnd_7054176 : Nat := 1207394303136899245886147

theorem tailTrace_7054176 : CollatzResearch.WordTrace tailWord_7054176 prefixEnd_7054176 1207394303136899245886147 := by
  unfold tailWord_7054176
  simp only [CollatzResearch.WordTrace]
  refine ⟨128643467845966292095139191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171524623794621722793518921 128643467845966292095139191)
  ·
    refine ⟨192965201768949438142708787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128643467845966292095139191 192965201768949438142708787)
    ·
      refine ⟨289447802653424157214063181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192965201768949438142708787 289447802653424157214063181)
      ·
        refine ⟨108542925995034058955273693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289447802653424157214063181 108542925995034058955273693)
        ·
          refine ⟨40703597248137772108227635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108542925995034058955273693 40703597248137772108227635)
          ·
            refine ⟨61055395872206658162341453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40703597248137772108227635 61055395872206658162341453)
            ·
              refine ⟨22895773452077496810878045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61055395872206658162341453 22895773452077496810878045)
              ·
                refine ⟨8585915044529061304079267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22895773452077496810878045 8585915044529061304079267)
                ·
                  refine ⟨12878872566793591956118901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8585915044529061304079267 12878872566793591956118901)
                  ·
                    refine ⟨1207394303136899245886147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12878872566793591956118901 1207394303136899245886147)
                    ·
                      rfl

theorem cell23_7054176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 1, 5].length) (baseStart_7054176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054176 prefixEnd_7054176 := by exact prefixLift 7054176
  have htrace : WordTrace (prefixWord ++ tailWord_7054176) baseStart_7054176 baseEnd_7054176 := by
    simpa [prefixWord, tailWord_7054176, baseEnd_7054176] using wordTrace_append hprefix tailTrace_7054176
  have hstable : (prefixWord ++ tailWord_7054176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054176).length < 2 ^ (prefixWord ++ tailWord_7054176).sum := by decide
  have hdescent : baseEnd_7054176 < baseStart_7054176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054213 : List Nat := [1, 3, 1, 1, 3, 4, 2, 2, 1, 1, 4]
def baseStart_7054213 : Nat := 118140960795 + 7054213 * 2 ^ 59
def prefixEnd_7054213 : Nat := 4983230072969 + 3 ^ 40 * 7054213 * 2
def baseEnd_7054213 : Nat := 3622201908194914092895771

theorem tailTrace_7054213 : CollatzResearch.WordTrace tailWord_7054213 prefixEnd_7054213 3622201908194914092895771 := by
  unfold tailWord_7054213
  simp only [CollatzResearch.WordTrace]
  refine ⟨257288285192798539509375293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171525523461865693006250195 257288285192798539509375293)
  ·
    refine ⟨96483106947299452316015735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257288285192798539509375293 96483106947299452316015735)
    ·
      refine ⟨144724660420949178474023603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96483106947299452316015735 144724660420949178474023603)
      ·
        refine ⟨217086990631423767711035405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144724660420949178474023603 217086990631423767711035405)
        ·
          refine ⟨81407621486783912891638277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217086990631423767711035405 81407621486783912891638277)
          ·
            refine ⟨15263929028771983667182177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81407621486783912891638277 15263929028771983667182177)
            ·
              refine ⟨11447946771578987750386633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15263929028771983667182177 11447946771578987750386633)
              ·
                refine ⟨8585960078684240812789975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11447946771578987750386633 8585960078684240812789975)
                ·
                  refine ⟨12878940118026361219184963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8585960078684240812789975 12878940118026361219184963)
                  ·
                    refine ⟨19318410177039541828777445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12878940118026361219184963 19318410177039541828777445)
                    ·
                      refine ⟨3622201908194914092895771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19318410177039541828777445 3622201908194914092895771)
                      ·
                        rfl

theorem cell23_7054213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_7054213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054213 prefixEnd_7054213 := by exact prefixLift 7054213
  have htrace : WordTrace (prefixWord ++ tailWord_7054213) baseStart_7054213 baseEnd_7054213 := by
    simpa [prefixWord, tailWord_7054213, baseEnd_7054213] using wordTrace_append hprefix tailTrace_7054213
  have hstable : (prefixWord ++ tailWord_7054213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054213).length < 2 ^ (prefixWord ++ tailWord_7054213).sum := by decide
  have hdescent : baseEnd_7054213 < baseStart_7054213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054249 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 2, 7]
def baseStart_7054249 : Nat := 118140960795 + 7054249 * 2 ^ 59
def prefixEnd_7054249 : Nat := 4983230072969 + 3 ^ 40 * 7054249 * 2
def baseEnd_7054249 : Nat := 1207406797832825317348535

theorem tailTrace_7054249 : CollatzResearch.WordTrace tailWord_7054249 prefixEnd_7054249 1207406797832825317348535 := by
  unfold tailWord_7054249
  simp only [CollatzResearch.WordTrace]
  refine ⟨257289598220668117657685801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171526398813778745105123867 257289598220668117657685801)
  ·
    refine ⟨192967198665501088243264351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257289598220668117657685801 192967198665501088243264351)
    ·
      refine ⟨289450797998251632364896527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192967198665501088243264351 289450797998251632364896527)
      ·
        refine ⟨434176196997377448547344791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289450797998251632364896527 434176196997377448547344791)
        ·
          refine ⟨651264295496066172821017187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434176196997377448547344791 651264295496066172821017187)
          ·
            refine ⟨976896443244099259231525781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651264295496066172821017187 976896443244099259231525781)
            ·
              refine ⟨45792020777067152776477771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 976896443244099259231525781 45792020777067152776477771)
              ·
                refine ⟨68688031165600729164716657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45792020777067152776477771 68688031165600729164716657)
                ·
                  refine ⟨51516023374200546873537493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68688031165600729164716657 51516023374200546873537493)
                  ·
                    refine ⟨1207406797832825317348535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51516023374200546873537493 1207406797832825317348535)
                    ·
                      rfl

theorem cell23_7054249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 7].length) (baseStart_7054249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054249 prefixEnd_7054249 := by exact prefixLift 7054249
  have htrace : WordTrace (prefixWord ++ tailWord_7054249) baseStart_7054249 baseEnd_7054249 := by
    simpa [prefixWord, tailWord_7054249, baseEnd_7054249] using wordTrace_append hprefix tailTrace_7054249
  have hstable : (prefixWord ++ tailWord_7054249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054249).length < 2 ^ (prefixWord ++ tailWord_7054249).sum := by decide
  have hdescent : baseEnd_7054249 < baseStart_7054249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054257 : List Nat := [1, 2, 2, 4, 3, 2, 2, 1, 2, 4]
def baseStart_7054257 : Nat := 118140960795 + 7054257 * 2 ^ 59
def prefixEnd_7054257 : Nat := 4983230072969 + 3 ^ 40 * 7054257 * 2
def baseEnd_7054257 : Nat := 1207408167114570640248523

theorem tailTrace_7054257 : CollatzResearch.WordTrace tailWord_7054257 prefixEnd_7054257 1207408167114570640248523 := by
  unfold tailWord_7054257
  simp only [CollatzResearch.WordTrace]
  refine ⟨257289890004639135023977025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171526593336426090015984683 257289890004639135023977025)
  ·
    refine ⟨192967417503479351267982769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257289890004639135023977025 192967417503479351267982769)
    ·
      refine ⟨144725563127609513450987077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192967417503479351267982769 144725563127609513450987077)
      ·
        refine ⟨27136043086426783772060077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144725563127609513450987077 27136043086426783772060077)
        ·
          refine ⟨10176016157410043914522529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27136043086426783772060077 10176016157410043914522529)
          ·
            refine ⟨7632012118057532935891897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10176016157410043914522529 7632012118057532935891897)
            ·
              refine ⟨5724009088543149701918923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7632012118057532935891897 5724009088543149701918923)
              ·
                refine ⟨8586013632814724552878385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5724009088543149701918923 8586013632814724552878385)
                ·
                  refine ⟨6439510224611043414658789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8586013632814724552878385 6439510224611043414658789)
                  ·
                    refine ⟨1207408167114570640248523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6439510224611043414658789 1207408167114570640248523)
                    ·
                      rfl

theorem cell23_7054257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_7054257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054257 prefixEnd_7054257 := by exact prefixLift 7054257
  have htrace : WordTrace (prefixWord ++ tailWord_7054257) baseStart_7054257 baseEnd_7054257 := by
    simpa [prefixWord, tailWord_7054257, baseEnd_7054257] using wordTrace_append hprefix tailTrace_7054257
  have hstable : (prefixWord ++ tailWord_7054257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054257).length < 2 ^ (prefixWord ++ tailWord_7054257).sum := by decide
  have hdescent : baseEnd_7054257 < baseStart_7054257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054259 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 5]
def baseStart_7054259 : Nat := 118140960795 + 7054259 * 2 ^ 59
def prefixEnd_7054259 : Nat := 4983230072969 + 3 ^ 40 * 7054259 * 2
def baseEnd_7054259 : Nat := 3622225528305020912920559

theorem tailTrace_7054259 : CollatzResearch.WordTrace tailWord_7054259 prefixEnd_7054259 3622225528305020912920559 := by
  unfold tailWord_7054259
  simp only [CollatzResearch.WordTrace]
  refine ⟨257289962950631889365549831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171526641967087926243699887 257289962950631889365549831)
  ·
    refine ⟨385934944425947834048324747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257289962950631889365549831 385934944425947834048324747)
    ·
      refine ⟨578902416638921751072487121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385934944425947834048324747 578902416638921751072487121)
      ·
        refine ⟨434176812479191313304365341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578902416638921751072487121 434176812479191313304365341)
        ·
          refine ⟨162816304679696742489137003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434176812479191313304365341 162816304679696742489137003)
          ·
            refine ⟨244224457019545113733705505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162816304679696742489137003 244224457019545113733705505)
            ·
              refine ⟨183168342764658835300279129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244224457019545113733705505 183168342764658835300279129)
              ·
                refine ⟨137376257073494126475209347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183168342764658835300279129 137376257073494126475209347)
                ·
                  refine ⟨206064385610241189712814021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137376257073494126475209347 206064385610241189712814021)
                  ·
                    refine ⟨38637072301920223071152629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 206064385610241189712814021 38637072301920223071152629)
                    ·
                      refine ⟨3622225528305020912920559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38637072301920223071152629 3622225528305020912920559)
                      ·
                        rfl

theorem cell23_7054259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_7054259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054259 prefixEnd_7054259 := by exact prefixLift 7054259
  have htrace : WordTrace (prefixWord ++ tailWord_7054259) baseStart_7054259 baseEnd_7054259 := by
    simpa [prefixWord, tailWord_7054259, baseEnd_7054259] using wordTrace_append hprefix tailTrace_7054259
  have hstable : (prefixWord ++ tailWord_7054259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054259).length < 2 ^ (prefixWord ++ tailWord_7054259).sum := by decide
  have hdescent : baseEnd_7054259 < baseStart_7054259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054386 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_7054386 : Nat := 118140960795 + 7054386 * 2 ^ 59
def prefixEnd_7054386 : Nat := 4983230072969 + 3 ^ 40 * 7054386 * 2
def baseEnd_7054386 : Nat := 1207430246782713972010825

theorem tailTrace_7054386 : CollatzResearch.WordTrace tailWord_7054386 prefixEnd_7054386 1207430246782713972010825 := by
  unfold tailWord_7054386
  simp only [CollatzResearch.WordTrace]
  refine ⟨64323648755292947513855753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171529730014114526703615341 64323648755292947513855753)
  ·
    refine ⟨48242736566469710635391815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64323648755292947513855753 48242736566469710635391815)
    ·
      refine ⟨72364104849704565953087723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48242736566469710635391815 72364104849704565953087723)
      ·
        refine ⟨108546157274556848929631585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72364104849704565953087723 108546157274556848929631585)
        ·
          refine ⟨81409617955917636697223689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108546157274556848929631585 81409617955917636697223689)
          ·
            refine ⟨61057213466938227522917767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81409617955917636697223689 61057213466938227522917767)
            ·
              refine ⟨91585820200407341284376651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61057213466938227522917767 91585820200407341284376651)
              ·
                refine ⟨137378730300611011926564977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91585820200407341284376651 137378730300611011926564977)
                ·
                  refine ⟨103034047725458258944923733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137378730300611011926564977 103034047725458258944923733)
                  ·
                    refine ⟨1207430246782713972010825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103034047725458258944923733 1207430246782713972010825)
                    ·
                      rfl

theorem cell23_7054386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_7054386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054386 prefixEnd_7054386 := by exact prefixLift 7054386
  have htrace : WordTrace (prefixWord ++ tailWord_7054386) baseStart_7054386 baseEnd_7054386 := by
    simpa [prefixWord, tailWord_7054386, baseEnd_7054386] using wordTrace_append hprefix tailTrace_7054386
  have hstable : (prefixWord ++ tailWord_7054386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054386).length < 2 ^ (prefixWord ++ tailWord_7054386).sum := by decide
  have hdescent : baseEnd_7054386 < baseStart_7054386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054393 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 1, 3, 4]
def baseStart_7054393 : Nat := 118140960795 + 7054393 * 2 ^ 59
def prefixEnd_7054393 : Nat := 4983230072969 + 3 ^ 40 * 7054393 * 2
def baseEnd_7054393 : Nat := 3622294334712723388644943

theorem tailTrace_7054393 : CollatzResearch.WordTrace tailWord_7054393 prefixEnd_7054393 3622294334712723388644943 := by
  unfold tailWord_7054393
  simp only [CollatzResearch.WordTrace]
  refine ⟨257294850332146430250927833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171529900221430953500618555 257294850332146430250927833)
  ·
    refine ⟨192971137749109822688195875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257294850332146430250927833 192971137749109822688195875)
    ·
      refine ⟨289456706623664734032293813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192971137749109822688195875 289456706623664734032293813)
      ·
        refine ⟨27136566245968568815527545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 289456706623664734032293813 27136566245968568815527545)
        ·
          refine ⟨20352424684476426611645659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27136566245968568815527545 20352424684476426611645659)
          ·
            refine ⟨30528637026714639917468489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20352424684476426611645659 30528637026714639917468489)
            ·
              refine ⟨22896477770035979938101367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30528637026714639917468489 22896477770035979938101367)
              ·
                refine ⟨34344716655053969907152051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22896477770035979938101367 34344716655053969907152051)
                ·
                  refine ⟨51517074982580954860728077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34344716655053969907152051 51517074982580954860728077)
                  ·
                    refine ⟨19318903118467858072773029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51517074982580954860728077 19318903118467858072773029)
                    ·
                      refine ⟨3622294334712723388644943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19318903118467858072773029 3622294334712723388644943)
                      ·
                        rfl

theorem cell23_7054393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_7054393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054393 prefixEnd_7054393 := by exact prefixLift 7054393
  have htrace : WordTrace (prefixWord ++ tailWord_7054393) baseStart_7054393 baseEnd_7054393 := by
    simpa [prefixWord, tailWord_7054393, baseEnd_7054393] using wordTrace_append hprefix tailTrace_7054393
  have hstable : (prefixWord ++ tailWord_7054393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054393).length < 2 ^ (prefixWord ++ tailWord_7054393).sum := by decide
  have hdescent : baseEnd_7054393 < baseStart_7054393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054420 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_7054420 : Nat := 118140960795 + 7054420 * 2 ^ 59
def prefixEnd_7054420 : Nat := 4983230072969 + 3 ^ 40 * 7054420 * 2
def baseEnd_7054420 : Nat := 1207436066230131594335773

theorem tailTrace_7054420 : CollatzResearch.WordTrace tailWord_7054420 prefixEnd_7054420 1207436066230131594335773 := by
  unfold tailWord_7054420
  simp only [CollatzResearch.WordTrace]
  refine ⟨128647917551524306931080357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171530556735365742574773809 128647917551524306931080357)
  ·
    refine ⟨24121484540910807549577567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128647917551524306931080357 24121484540910807549577567)
    ·
      refine ⟨36182226811366211324366351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24121484540910807549577567 36182226811366211324366351)
      ·
        refine ⟨54273340217049316986549527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36182226811366211324366351 54273340217049316986549527)
        ·
          refine ⟨81410010325573975479824291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54273340217049316986549527 81410010325573975479824291)
          ·
            refine ⟨122115015488360963219736437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81410010325573975479824291 122115015488360963219736437)
            ·
              refine ⟨11448282702033840301850291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122115015488360963219736437 11448282702033840301850291)
              ·
                refine ⟨17172424053050760452775437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11448282702033840301850291 17172424053050760452775437)
                ·
                  refine ⟨6439659019894035169790789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17172424053050760452775437 6439659019894035169790789)
                  ·
                    refine ⟨1207436066230131594335773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6439659019894035169790789 1207436066230131594335773)
                    ·
                      rfl

theorem cell23_7054420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_7054420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054420 prefixEnd_7054420 := by exact prefixLift 7054420
  have htrace : WordTrace (prefixWord ++ tailWord_7054420) baseStart_7054420 baseEnd_7054420 := by
    simpa [prefixWord, tailWord_7054420, baseEnd_7054420] using wordTrace_append hprefix tailTrace_7054420
  have hstable : (prefixWord ++ tailWord_7054420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054420).length < 2 ^ (prefixWord ++ tailWord_7054420).sum := by decide
  have hdescent : baseEnd_7054420 < baseStart_7054420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054483 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 4]
def baseStart_7054483 : Nat := 118140960795 + 7054483 * 2 ^ 59
def prefixEnd_7054483 : Nat := 4983230072969 + 3 ^ 40 * 7054483 * 2
def baseEnd_7054483 : Nat := 3622340547971628036519529

theorem tailTrace_7054483 : CollatzResearch.WordTrace tailWord_7054483 prefixEnd_7054483 3622340547971628036519529 := by
  unfold tailWord_7054483
  simp only [CollatzResearch.WordTrace]
  refine ⟨257298132901820375621704103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171532088601213583747802735 257298132901820375621704103)
  ·
    refine ⟨385947199352730563432556155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257298132901820375621704103 385947199352730563432556155)
    ·
      refine ⟨578920799029095845148834233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385947199352730563432556155 578920799029095845148834233)
      ·
        refine ⟨434190599271821883861625675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578920799029095845148834233 434190599271821883861625675)
        ·
          refine ⟨651285898907732825792438513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434190599271821883861625675 651285898907732825792438513)
          ·
            refine ⟨488464424180799619344328885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651285898907732825792438513 488464424180799619344328885)
            ·
              refine ⟨45793539766949964313530833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 488464424180799619344328885 45793539766949964313530833)
              ·
                refine ⟨34345154825212473235148125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45793539766949964313530833 34345154825212473235148125)
                ·
                  refine ⟨12879433059454677463180547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34345154825212473235148125 12879433059454677463180547)
                  ·
                    refine ⟨19319149589182016194770821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12879433059454677463180547 19319149589182016194770821)
                    ·
                      refine ⟨3622340547971628036519529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19319149589182016194770821 3622340547971628036519529)
                      ·
                        rfl

theorem cell23_7054483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_7054483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054483 prefixEnd_7054483 := by exact prefixLift 7054483
  have htrace : WordTrace (prefixWord ++ tailWord_7054483) baseStart_7054483 baseEnd_7054483 := by
    simpa [prefixWord, tailWord_7054483, baseEnd_7054483] using wordTrace_append hprefix tailTrace_7054483
  have hstable : (prefixWord ++ tailWord_7054483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054483).length < 2 ^ (prefixWord ++ tailWord_7054483).sum := by decide
  have hdescent : baseEnd_7054483 < baseStart_7054483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054494 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_7054494 : Nat := 118140960795 + 7054494 * 2 ^ 59
def prefixEnd_7054494 : Nat := 4983230072969 + 3 ^ 40 * 7054494 * 2
def baseEnd_7054494 : Nat := 3622346196258827493481979

theorem tailTrace_7054494 : CollatzResearch.WordTrace tailWord_7054494 prefixEnd_7054494 3622346196258827493481979 := by
  unfold tailWord_7054494
  simp only [CollatzResearch.WordTrace]
  refine ⟨32162316763097565562544317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171532356069853683000236357 32162316763097565562544317)
  ·
    refine ⟨12060868786161587085954119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32162316763097565562544317 12060868786161587085954119)
    ·
      refine ⟨18091303179242380628931179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12060868786161587085954119 18091303179242380628931179)
      ·
        refine ⟨27136954768863570943396769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18091303179242380628931179 27136954768863570943396769)
        ·
          refine ⟨20352716076647678207547577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27136954768863570943396769 20352716076647678207547577)
          ·
            refine ⟨15264537057485758655660683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20352716076647678207547577 15264537057485758655660683)
            ·
              refine ⟨22896805586228637983491025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15264537057485758655660683 22896805586228637983491025)
              ·
                refine ⟨17172604189671478487618269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22896805586228637983491025 17172604189671478487618269)
                ·
                  refine ⟨6439726571126804432856851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17172604189671478487618269 6439726571126804432856851)
                  ·
                    refine ⟨9659589856690206649285277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6439726571126804432856851 9659589856690206649285277)
                    ·
                      refine ⟨3622346196258827493481979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9659589856690206649285277 3622346196258827493481979)
                      ·
                        rfl

theorem cell23_7054494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_7054494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054494 prefixEnd_7054494 := by exact prefixLift 7054494
  have htrace : WordTrace (prefixWord ++ tailWord_7054494) baseStart_7054494 baseEnd_7054494 := by
    simpa [prefixWord, tailWord_7054494, baseEnd_7054494] using wordTrace_append hprefix tailTrace_7054494
  have hstable : (prefixWord ++ tailWord_7054494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054494).length < 2 ^ (prefixWord ++ tailWord_7054494).sum := by decide
  have hdescent : baseEnd_7054494 < baseStart_7054494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054500 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_7054500 : Nat := 118140960795 + 7054500 * 2 ^ 59
def prefixEnd_7054500 : Nat := 4983230072969 + 3 ^ 40 * 7054500 * 2
def baseEnd_7054500 : Nat := 3622349277142754470006951

theorem tailTrace_7054500 : CollatzResearch.WordTrace tailWord_7054500 prefixEnd_7054500 3622349277142754470006951 := by
  unfold tailWord_7054500
  simp only [CollatzResearch.WordTrace]
  refine ⟨128649376471379393762536477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171532501961839191683381969 128649376471379393762536477)
  ·
    refine ⟨48243516176767272660951179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128649376471379393762536477 48243516176767272660951179)
    ·
      refine ⟨72365274265150908991426769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48243516176767272660951179 72365274265150908991426769)
      ·
        refine ⟨54273955698863181743570077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72365274265150908991426769 54273955698863181743570077)
        ·
          refine ⟨20352733387073693153838779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54273955698863181743570077 20352733387073693153838779)
          ·
            refine ⟨30529100080610539730758169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20352733387073693153838779 30529100080610539730758169)
            ·
              refine ⟨22896825060457904798068627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30529100080610539730758169 22896825060457904798068627)
              ·
                refine ⟨34345237590686857197102941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22896825060457904798068627 34345237590686857197102941)
                ·
                  refine ⟨12879464096507571448913603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34345237590686857197102941 12879464096507571448913603)
                  ·
                    refine ⟨19319196144761357173370405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12879464096507571448913603 19319196144761357173370405)
                    ·
                      refine ⟨3622349277142754470006951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19319196144761357173370405 3622349277142754470006951)
                      ·
                        rfl

theorem cell23_7054500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_7054500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054500 prefixEnd_7054500 := by exact prefixLift 7054500
  have htrace : WordTrace (prefixWord ++ tailWord_7054500) baseStart_7054500 baseEnd_7054500 := by
    simpa [prefixWord, tailWord_7054500, baseEnd_7054500] using wordTrace_append hprefix tailTrace_7054500
  have hstable : (prefixWord ++ tailWord_7054500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054500).length < 2 ^ (prefixWord ++ tailWord_7054500).sum := by decide
  have hdescent : baseEnd_7054500 < baseStart_7054500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054613 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 9]
def baseStart_7054613 : Nat := 118140960795 + 7054613 * 2 ^ 59
def prefixEnd_7054613 : Nat := 4983230072969 + 3 ^ 40 * 7054613 * 2
def baseEnd_7054613 : Nat := 402489700050745836432659

theorem tailTrace_7054613 : CollatzResearch.WordTrace tailWord_7054613 prefixEnd_7054613 402489700050745836432659 := by
  unfold tailWord_7054613
  simp only [CollatzResearch.WordTrace]
  refine ⟨257302874391349407823936493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171535249594232938549290995 257302874391349407823936493)
  ·
    refine ⟨96488577896756027933976185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257302874391349407823936493 96488577896756027933976185)
    ·
      refine ⟨72366433422567020950482139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96488577896756027933976185 72366433422567020950482139)
      ·
        refine ⟨108549650133850531425723209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72366433422567020950482139 108549650133850531425723209)
        ·
          refine ⟨81412237600387898569292407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108549650133850531425723209 81412237600387898569292407)
          ·
            refine ⟨122118356400581847853938611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81412237600387898569292407 122118356400581847853938611)
            ·
              refine ⟨183177534600872771780907917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122118356400581847853938611 183177534600872771780907917)
              ·
                refine ⟨68691575475327289417840469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183177534600872771780907917 68691575475327289417840469)
                ·
                  refine ⟨402489700050745836432659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68691575475327289417840469 402489700050745836432659)
                  ·
                    rfl

theorem cell23_7054613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 9].length) (baseStart_7054613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054613 prefixEnd_7054613 := by exact prefixLift 7054613
  have htrace : WordTrace (prefixWord ++ tailWord_7054613) baseStart_7054613 baseEnd_7054613 := by
    simpa [prefixWord, tailWord_7054613, baseEnd_7054613] using wordTrace_append hprefix tailTrace_7054613
  have hstable : (prefixWord ++ tailWord_7054613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054613).length < 2 ^ (prefixWord ++ tailWord_7054613).sum := by decide
  have hdescent : baseEnd_7054613 < baseStart_7054613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054624 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 1, 4, 2]
def baseStart_7054624 : Nat := 118140960795 + 7054624 * 2 ^ 59
def prefixEnd_7054624 : Nat := 4983230072969 + 3 ^ 40 * 7054624 * 2
def baseEnd_7054624 : Nat := 3622412948743911984856381

theorem tailTrace_7054624 : CollatzResearch.WordTrace tailWord_7054624 prefixEnd_7054624 3622412948743911984856381 := by
  unfold tailWord_7054624
  simp only [CollatzResearch.WordTrace]
  refine ⟨128651637797154778351293463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171535517062873037801724617 128651637797154778351293463)
  ·
    refine ⟨192977456695732167526940195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128651637797154778351293463 192977456695732167526940195)
    ·
      refine ⟨289466185043598251290410293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192977456695732167526940195 289466185043598251290410293)
      ·
        refine ⟨27137454847837336058475965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 289466185043598251290410293 27137454847837336058475965)
        ·
          refine ⟨10176545567939001021928487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27137454847837336058475965 10176545567939001021928487)
          ·
            refine ⟨15264818351908501532892731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10176545567939001021928487 15264818351908501532892731)
            ·
              refine ⟨22897227527862752299339097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15264818351908501532892731 22897227527862752299339097)
              ·
                refine ⟨17172920645897064224504323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22897227527862752299339097 17172920645897064224504323)
                ·
                  refine ⟨25759380968845596336756485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17172920645897064224504323 25759380968845596336756485)
                  ·
                    refine ⟨4829883931658549313141841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25759380968845596336756485 4829883931658549313141841)
                    ·
                      refine ⟨3622412948743911984856381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4829883931658549313141841 3622412948743911984856381)
                      ·
                        rfl

theorem cell23_7054624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_7054624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054624 prefixEnd_7054624 := by exact prefixLift 7054624
  have htrace : WordTrace (prefixWord ++ tailWord_7054624) baseStart_7054624 baseEnd_7054624 := by
    simpa [prefixWord, tailWord_7054624, baseEnd_7054624] using wordTrace_append hprefix tailTrace_7054624
  have hstable : (prefixWord ++ tailWord_7054624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054624).length < 2 ^ (prefixWord ++ tailWord_7054624).sum := by decide
  have hdescent : baseEnd_7054624 < baseStart_7054624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054640 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 3]
def baseStart_7054640 : Nat := 118140960795 + 7054640 * 2 ^ 59
def prefixEnd_7054640 : Nat := 4983230072969 + 3 ^ 40 * 7054640 * 2
def baseEnd_7054640 : Nat := 3622421164434383922256307

theorem tailTrace_7054640 : CollatzResearch.WordTrace tailWord_7054640 prefixEnd_7054640 3622421164434383922256307 := by
  unfold tailWord_7054640
  simp only [CollatzResearch.WordTrace]
  refine ⟨128651929581125795717584687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171535906108167727623446249 128651929581125795717584687)
  ·
    refine ⟨192977894371688693576377031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128651929581125795717584687 192977894371688693576377031)
    ·
      refine ⟨289466841557533040364565547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192977894371688693576377031 289466841557533040364565547)
      ·
        refine ⟨434200262336299560546848321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289466841557533040364565547 434200262336299560546848321)
        ·
          refine ⟨325650196752224670410136241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434200262336299560546848321 325650196752224670410136241)
          ·
            refine ⟨244237647564168502807602181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325650196752224670410136241 244237647564168502807602181)
            ·
              refine ⟨45794558918281594276425409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244237647564168502807602181 45794558918281594276425409)
              ·
                refine ⟨34345919188711195707319057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45794558918281594276425409 34345919188711195707319057)
                ·
                  refine ⟨25759439391533396780489293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34345919188711195707319057 25759439391533396780489293)
                  ·
                    refine ⟨9659789771825023792683485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25759439391533396780489293 9659789771825023792683485)
                    ·
                      refine ⟨3622421164434383922256307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9659789771825023792683485 3622421164434383922256307)
                      ·
                        rfl

theorem cell23_7054640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 3].length) (baseStart_7054640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054640 prefixEnd_7054640 := by exact prefixLift 7054640
  have htrace : WordTrace (prefixWord ++ tailWord_7054640) baseStart_7054640 baseEnd_7054640 := by
    simpa [prefixWord, tailWord_7054640, baseEnd_7054640] using wordTrace_append hprefix tailTrace_7054640
  have hstable : (prefixWord ++ tailWord_7054640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054640).length < 2 ^ (prefixWord ++ tailWord_7054640).sum := by decide
  have hdescent : baseEnd_7054640 < baseStart_7054640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054641 : List Nat := [1, 2, 2, 3, 3, 2, 2, 2, 2, 2, 2]
def baseStart_7054641 : Nat := 118140960795 + 7054641 * 2 ^ 59
def prefixEnd_7054641 : Nat := 4983230072969 + 3 ^ 40 * 7054641 * 2
def baseEnd_7054641 : Nat := 3622421677915038418343803

theorem tailTrace_7054641 : CollatzResearch.WordTrace tailWord_7054641 prefixEnd_7054641 3622421677915038418343803 := by
  unfold tailWord_7054641
  simp only [CollatzResearch.WordTrace]
  refine ⟨257303895635247968605955777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171535930423498645737303851 257303895635247968605955777)
  ·
    refine ⟨192977921726435976454466833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257303895635247968605955777 192977921726435976454466833)
    ·
      refine ⟨144733441294826982340850125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192977921726435976454466833 144733441294826982340850125)
      ·
        refine ⟨54275040485560118377818797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144733441294826982340850125 54275040485560118377818797)
        ·
          refine ⟨20353140182085044391682049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54275040485560118377818797 20353140182085044391682049)
          ·
            refine ⟨15264855136563783293761537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20353140182085044391682049 15264855136563783293761537)
            ·
              refine ⟨11448641352422837470321153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15264855136563783293761537 11448641352422837470321153)
              ·
                refine ⟨8586481014317128102740865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11448641352422837470321153 8586481014317128102740865)
                ·
                  refine ⟨6439860760737846077055649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8586481014317128102740865 6439860760737846077055649)
                  ·
                    refine ⟨4829895570553384557791737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6439860760737846077055649 4829895570553384557791737)
                    ·
                      refine ⟨3622421677915038418343803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4829895570553384557791737 3622421677915038418343803)
                      ·
                        rfl

theorem cell23_7054641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_7054641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054641 prefixEnd_7054641 := by exact prefixLift 7054641
  have htrace : WordTrace (prefixWord ++ tailWord_7054641) baseStart_7054641 baseEnd_7054641 := by
    simpa [prefixWord, tailWord_7054641, baseEnd_7054641] using wordTrace_append hprefix tailTrace_7054641
  have hstable : (prefixWord ++ tailWord_7054641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054641).length < 2 ^ (prefixWord ++ tailWord_7054641).sum := by decide
  have hdescent : baseEnd_7054641 < baseStart_7054641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054657 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_7054657 : Nat := 118140960795 + 7054657 * 2 ^ 59
def prefixEnd_7054657 : Nat := 4983230072969 + 3 ^ 40 * 7054657 * 2
def baseEnd_7054657 : Nat := 3622429893605510355743729

theorem tailTrace_7054657 : CollatzResearch.WordTrace tailWord_7054657 prefixEnd_7054657 3622429893605510355743729 := by
  unfold tailWord_7054657
  simp only [CollatzResearch.WordTrace]
  refine ⟨257304479203190003338538225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171536319468793335559025483 257304479203190003338538225)
  ·
    refine ⟨192978359402392502503903669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257304479203190003338538225 192978359402392502503903669)
    ·
      refine ⟨18091721193974297109740969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192978359402392502503903669 18091721193974297109740969)
      ·
        refine ⟨13568790895480722832305727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18091721193974297109740969 13568790895480722832305727)
        ·
          refine ⟨20353186343221084248458591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13568790895480722832305727 20353186343221084248458591)
          ·
            refine ⟨30529779514831626372687887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20353186343221084248458591 30529779514831626372687887)
            ·
              refine ⟨45794669272247439559031831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30529779514831626372687887 45794669272247439559031831)
              ·
                refine ⟨68692003908371159338547747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45794669272247439559031831 68692003908371159338547747)
                ·
                  refine ⟨103038005862556739007821621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68692003908371159338547747 103038005862556739007821621)
                  ·
                    refine ⟨9659813049614694281983277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103038005862556739007821621 9659813049614694281983277)
                    ·
                      refine ⟨3622429893605510355743729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9659813049614694281983277 3622429893605510355743729)
                      ·
                        rfl

theorem cell23_7054657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_7054657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054657 prefixEnd_7054657 := by exact prefixLift 7054657
  have htrace : WordTrace (prefixWord ++ tailWord_7054657) baseStart_7054657 baseEnd_7054657 := by
    simpa [prefixWord, tailWord_7054657, baseEnd_7054657] using wordTrace_append hprefix tailTrace_7054657
  have hstable : (prefixWord ++ tailWord_7054657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054657).length < 2 ^ (prefixWord ++ tailWord_7054657).sum := by decide
  have hdescent : baseEnd_7054657 < baseStart_7054657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054677 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 2, 5]
def baseStart_7054677 : Nat := 118140960795 + 7054677 * 2 ^ 59
def prefixEnd_7054677 : Nat := 4983230072969 + 3 ^ 40 * 7054677 * 2
def baseEnd_7054677 : Nat := 1207480054406200092497879

theorem tailTrace_7054677 : CollatzResearch.WordTrace tailWord_7054677 prefixEnd_7054677 1207480054406200092497879 := by
  unfold tailWord_7054677
  simp only [CollatzResearch.WordTrace]
  refine ⟨257305208663117546754266285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171536805775411697836177523 257305208663117546754266285)
  ·
    refine ⟨96489453248669080032849857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257305208663117546754266285 96489453248669080032849857)
    ·
      refine ⟨72367089936501810024637393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96489453248669080032849857 72367089936501810024637393)
      ·
        refine ⟨54275317452376357518478045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72367089936501810024637393 54275317452376357518478045)
        ·
          refine ⟨20353244044641134069429267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54275317452376357518478045 20353244044641134069429267)
          ·
            refine ⟨30529866066961701104143901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20353244044641134069429267 30529866066961701104143901)
            ·
              refine ⟨11448699775110637914053963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30529866066961701104143901 11448699775110637914053963)
              ·
                refine ⟨17173049662665956871080945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11448699775110637914053963 17173049662665956871080945)
                ·
                  refine ⟨12879787246999467653310709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17173049662665956871080945 12879787246999467653310709)
                  ·
                    refine ⟨1207480054406200092497879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12879787246999467653310709 1207480054406200092497879)
                    ·
                      rfl

theorem cell23_7054677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_7054677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054677 prefixEnd_7054677 := by exact prefixLift 7054677
  have htrace : WordTrace (prefixWord ++ tailWord_7054677) baseStart_7054677 baseEnd_7054677 := by
    simpa [prefixWord, tailWord_7054677, baseEnd_7054677] using wordTrace_append hprefix tailTrace_7054677
  have hstable : (prefixWord ++ tailWord_7054677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054677).length < 2 ^ (prefixWord ++ tailWord_7054677).sum := by decide
  have hdescent : baseEnd_7054677 < baseStart_7054677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054680 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 1, 3, 4]
def baseStart_7054680 : Nat := 118140960795 + 7054680 * 2 ^ 59
def prefixEnd_7054680 : Nat := 4983230072969 + 3 ^ 40 * 7054680 * 2
def baseEnd_7054680 : Nat := 3622441703660563765756123

theorem tailTrace_7054680 : CollatzResearch.WordTrace tailWord_7054680 prefixEnd_7054680 3622441703660563765756123 := by
  unfold tailWord_7054680
  simp only [CollatzResearch.WordTrace]
  refine ⟨128652659041053339133312747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171536878721404452177750329 128652659041053339133312747)
  ·
    refine ⟨192978988561580008699969121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128652659041053339133312747 192978988561580008699969121)
    ·
      refine ⟨144734241421185006524976841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192978988561580008699969121 144734241421185006524976841)
      ·
        refine ⟨108550681065888754893732631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144734241421185006524976841 108550681065888754893732631)
        ·
          refine ⟨162826021598833132340598947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108550681065888754893732631 162826021598833132340598947)
          ·
            refine ⟨244239032398249698510898421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162826021598833132340598947 244239032398249698510898421)
            ·
              refine ⟨22897409287335909235396727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244239032398249698510898421 22897409287335909235396727)
              ·
                refine ⟨34346113931003863853095091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22897409287335909235396727 34346113931003863853095091)
                ·
                  refine ⟨51519170896505795779642637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34346113931003863853095091 51519170896505795779642637)
                  ·
                    refine ⟨19319689086189673417365989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51519170896505795779642637 19319689086189673417365989)
                    ·
                      refine ⟨3622441703660563765756123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19319689086189673417365989 3622441703660563765756123)
                      ·
                        rfl

theorem cell23_7054680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_7054680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054680 prefixEnd_7054680 := by exact prefixLift 7054680
  have htrace : WordTrace (prefixWord ++ tailWord_7054680) baseStart_7054680 baseEnd_7054680 := by
    simpa [prefixWord, tailWord_7054680, baseEnd_7054680] using wordTrace_append hprefix tailTrace_7054680
  have hstable : (prefixWord ++ tailWord_7054680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054680).length < 2 ^ (prefixWord ++ tailWord_7054680).sum := by decide
  have hdescent : baseEnd_7054680 < baseStart_7054680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054720 : List Nat := [2, 1, 1, 2, 1, 2, 1, 7, 6]
def baseStart_7054720 : Nat := 118140960795 + 7054720 * 2 ^ 59
def prefixEnd_7054720 : Nat := 4983230072969 + 3 ^ 40 * 7054720 * 2
def baseEnd_7054720 : Nat := 402495804765193734361771

theorem tailTrace_7054720 : CollatzResearch.WordTrace tailWord_7054720 prefixEnd_7054720 402495804765193734361771 := by
  unfold tailWord_7054720
  simp only [CollatzResearch.WordTrace]
  refine ⟨128653388500980882549040807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171537851334641176732054409 128653388500980882549040807)
  ·
    refine ⟨192980082751471323823561211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128653388500980882549040807 192980082751471323823561211)
    ·
      refine ⟨289470124127206985735341817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192980082751471323823561211 289470124127206985735341817)
      ·
        refine ⟨217102593095405239301506363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289470124127206985735341817 217102593095405239301506363)
        ·
          refine ⟨325653889643107858952259545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217102593095405239301506363 325653889643107858952259545)
          ·
            refine ⟨244240417232330894214194659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325653889643107858952259545 244240417232330894214194659)
            ·
              refine ⟨366360625848496341321291989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244240417232330894214194659 366360625848496341321291989)
              ·
                refine ⟨8586577168324132999717781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 366360625848496341321291989 8586577168324132999717781)
                ·
                  refine ⟨402495804765193734361771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8586577168324132999717781 402495804765193734361771)
                  ·
                    rfl

theorem cell23_7054720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 6].length) (baseStart_7054720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054720 prefixEnd_7054720 := by exact prefixLift 7054720
  have htrace : WordTrace (prefixWord ++ tailWord_7054720) baseStart_7054720 baseEnd_7054720 := by
    simpa [prefixWord, tailWord_7054720, baseEnd_7054720] using wordTrace_append hprefix tailTrace_7054720
  have hstable : (prefixWord ++ tailWord_7054720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054720).length < 2 ^ (prefixWord ++ tailWord_7054720).sum := by decide
  have hdescent : baseEnd_7054720 < baseStart_7054720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054757 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 3, 5, 2]
def baseStart_7054757 : Nat := 118140960795 + 7054757 * 2 ^ 59
def prefixEnd_7054757 : Nat := 4983230072969 + 3 ^ 40 * 7054757 * 2
def baseEnd_7054757 : Nat := 3622481241670959964493269

theorem tailTrace_7054757 : CollatzResearch.WordTrace tailWord_7054757 prefixEnd_7054757 3622481241670959964493269 := by
  unfold tailWord_7054757
  simp only [CollatzResearch.WordTrace]
  refine ⟨257308126502827720417178525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171538751001885146944785683 257308126502827720417178525)
  ·
    refine ⟨96490547438560395156441947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257308126502827720417178525 96490547438560395156441947)
    ·
      refine ⟨144735821157840592734662921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96490547438560395156441947 144735821157840592734662921)
      ·
        refine ⟨108551865868380444550997191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144735821157840592734662921 108551865868380444550997191)
        ·
          refine ⟨162827798802570666826495787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108551865868380444550997191 162827798802570666826495787)
          ·
            refine ⟨244241698203856000239743681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162827798802570666826495787 244241698203856000239743681)
            ·
              refine ⟨183181273652892000179807761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244241698203856000239743681 183181273652892000179807761)
              ·
                refine ⟨137385955239669000134855821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183181273652892000179807761 137385955239669000134855821)
                ·
                  refine ⟨51519733214875875050570933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137385955239669000134855821 51519733214875875050570933)
                  ·
                    refine ⟨4829974988894613285991025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51519733214875875050570933 4829974988894613285991025)
                    ·
                      refine ⟨3622481241670959964493269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4829974988894613285991025 3622481241670959964493269)
                      ·
                        rfl

theorem cell23_7054757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_7054757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054757 prefixEnd_7054757 := by exact prefixLift 7054757
  have htrace : WordTrace (prefixWord ++ tailWord_7054757) baseStart_7054757 baseEnd_7054757 := by
    simpa [prefixWord, tailWord_7054757, baseEnd_7054757] using wordTrace_append hprefix tailTrace_7054757
  have hstable : (prefixWord ++ tailWord_7054757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054757).length < 2 ^ (prefixWord ++ tailWord_7054757).sum := by decide
  have hdescent : baseEnd_7054757 < baseStart_7054757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054764 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 3]
def baseStart_7054764 : Nat := 118140960795 + 7054764 * 2 ^ 59
def prefixEnd_7054764 : Nat := 4983230072969 + 3 ^ 40 * 7054764 * 2
def baseEnd_7054764 : Nat := 3622484836035541437105737

theorem tailTrace_7054764 : CollatzResearch.WordTrace tailWord_7054764 prefixEnd_7054764 3622484836035541437105737 := by
  unfold tailWord_7054764
  simp only [CollatzResearch.WordTrace]
  refine ⟨128654190906901180306341673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171538921209201573741788897 128654190906901180306341673)
  ·
    refine ⟨96490643180175885229756255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128654190906901180306341673 96490643180175885229756255)
    ·
      refine ⟨144735964770263827844634383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96490643180175885229756255 144735964770263827844634383)
      ·
        refine ⟨217103947155395741766951575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144735964770263827844634383 217103947155395741766951575)
        ·
          refine ⟨325655920733093612650427363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217103947155395741766951575 325655920733093612650427363)
          ·
            refine ⟨488483881099640418975641045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325655920733093612650427363 488483881099640418975641045)
            ·
              refine ⟨11448840963272822319741587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 488483881099640418975641045 11448840963272822319741587)
              ·
                refine ⟨17173261444909233479612381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11448840963272822319741587 17173261444909233479612381)
                ·
                  refine ⟨6439973041840962554854643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17173261444909233479612381 6439973041840962554854643)
                  ·
                    refine ⟨9659959562761443832281965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6439973041840962554854643 9659959562761443832281965)
                    ·
                      refine ⟨3622484836035541437105737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9659959562761443832281965 3622484836035541437105737)
                      ·
                        rfl

theorem cell23_7054764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_7054764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054764 prefixEnd_7054764 := by exact prefixLift 7054764
  have htrace : WordTrace (prefixWord ++ tailWord_7054764) baseStart_7054764 baseEnd_7054764 := by
    simpa [prefixWord, tailWord_7054764, baseEnd_7054764] using wordTrace_append hprefix tailTrace_7054764
  have hstable : (prefixWord ++ tailWord_7054764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054764).length < 2 ^ (prefixWord ++ tailWord_7054764).sum := by decide
  have hdescent : baseEnd_7054764 < baseStart_7054764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054787 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 2, 6, 2]
def baseStart_7054787 : Nat := 118140960795 + 7054787 * 2 ^ 59
def prefixEnd_7054787 : Nat := 4983230072969 + 3 ^ 40 * 7054787 * 2
def baseEnd_7054787 : Nat := 3622496646090594847118131

theorem tailTrace_7054787 : CollatzResearch.WordTrace tailWord_7054787 prefixEnd_7054787 3622496646090594847118131 := by
  unfold tailWord_7054787
  simp only [CollatzResearch.WordTrace]
  refine ⟨257309220692719035540770615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171539480461812690360513743 257309220692719035540770615)
  ·
    refine ⟨385963831039078553311155923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257309220692719035540770615 385963831039078553311155923)
    ·
      refine ⟨578945746558617829966733885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385963831039078553311155923 578945746558617829966733885)
      ·
        refine ⟨217104654959481686237525207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 578945746558617829966733885 217104654959481686237525207)
        ·
          refine ⟨325656982439222529356287811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217104654959481686237525207 325656982439222529356287811)
          ·
            refine ⟨488485473658833794034431717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325656982439222529356287811 488485473658833794034431717)
            ·
              refine ⟨91591026311031336381455947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 488485473658833794034431717 91591026311031336381455947)
              ·
                refine ⟨137386539466547004572183921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91591026311031336381455947 137386539466547004572183921)
                ·
                  refine ⟨103039904599910253429137941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137386539466547004572183921 103039904599910253429137941)
                  ·
                    refine ⟨4829995528120793129490841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103039904599910253429137941 4829995528120793129490841)
                    ·
                      refine ⟨3622496646090594847118131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4829995528120793129490841 3622496646090594847118131)
                      ·
                        rfl

theorem cell23_7054787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 6, 2].length) (baseStart_7054787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054787 prefixEnd_7054787 := by exact prefixLift 7054787
  have htrace : WordTrace (prefixWord ++ tailWord_7054787) baseStart_7054787 baseEnd_7054787 := by
    simpa [prefixWord, tailWord_7054787, baseEnd_7054787] using wordTrace_append hprefix tailTrace_7054787
  have hstable : (prefixWord ++ tailWord_7054787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054787).length < 2 ^ (prefixWord ++ tailWord_7054787).sum := by decide
  have hdescent : baseEnd_7054787 < baseStart_7054787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054810 : List Nat := [3, 1, 1, 2, 3, 13]
def baseStart_7054810 : Nat := 118140960795 + 7054810 * 2 ^ 59
def prefixEnd_7054810 : Nat := 4983230072969 + 3 ^ 40 * 7054810 * 2
def baseEnd_7054810 : Nat := 14907442206360692416175

theorem tailTrace_7054810 : CollatzResearch.WordTrace tailWord_7054810 prefixEnd_7054810 14907442206360692416175 := by
  unfold tailWord_7054810
  simp only [CollatzResearch.WordTrace]
  refine ⟨64327514892908927617214471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171540039714423806979238589 64327514892908927617214471)
  ·
    refine ⟨96491272339363391425821707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64327514892908927617214471 96491272339363391425821707)
    ·
      refine ⟨144736908509045087138732561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96491272339363391425821707 144736908509045087138732561)
      ·
        refine ⟨108552681381783815354049421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144736908509045087138732561 108552681381783815354049421)
        ·
          refine ⟨40707255518168930757768533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108552681381783815354049421 40707255518168930757768533)
          ·
            refine ⟨14907442206360692416175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 40707255518168930757768533 14907442206360692416175)
            ·
              rfl

theorem cell23_7054810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 13].length) (baseStart_7054810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054810 prefixEnd_7054810 := by exact prefixLift 7054810
  have htrace : WordTrace (prefixWord ++ tailWord_7054810) baseStart_7054810 baseEnd_7054810 := by
    simpa [prefixWord, tailWord_7054810, baseEnd_7054810] using wordTrace_append hprefix tailTrace_7054810
  have hstable : (prefixWord ++ tailWord_7054810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054810).length < 2 ^ (prefixWord ++ tailWord_7054810).sum := by decide
  have hdescent : baseEnd_7054810 < baseStart_7054810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054834 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_7054834 : Nat := 118140960795 + 7054834 * 2 ^ 59
def prefixEnd_7054834 : Nat := 4983230072969 + 3 ^ 40 * 7054834 * 2
def baseEnd_7054834 : Nat := 3622520779681356163230415

theorem tailTrace_7054834 : CollatzResearch.WordTrace tailWord_7054834 prefixEnd_7054834 3622520779681356163230415 := by
  unfold tailWord_7054834
  simp only [CollatzResearch.WordTrace]
  refine ⟨64327733730887190641932889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171540623282365841711821037 64327733730887190641932889)
  ·
    refine ⟨48245800298165392981449667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64327733730887190641932889 48245800298165392981449667)
    ·
      refine ⟨72368700447248089472174501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48245800298165392981449667 72368700447248089472174501)
      ·
        refine ⟨13569131333859016776032719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72368700447248089472174501 13569131333859016776032719)
        ·
          refine ⟨20353697000788525164049079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13569131333859016776032719 20353697000788525164049079)
          ·
            refine ⟨30530545501182787746073619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20353697000788525164049079 30530545501182787746073619)
            ·
              refine ⟨45795818251774181619110429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30530545501182787746073619 45795818251774181619110429)
              ·
                refine ⟨17173431844415318107166411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45795818251774181619110429 17173431844415318107166411)
                ·
                  refine ⟨25760147766622977160749617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17173431844415318107166411 25760147766622977160749617)
                  ·
                    refine ⟨19320110824967232870562213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25760147766622977160749617 19320110824967232870562213)
                    ·
                      refine ⟨3622520779681356163230415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19320110824967232870562213 3622520779681356163230415)
                      ·
                        rfl

theorem cell23_7054834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_7054834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054834 prefixEnd_7054834 := by exact prefixLift 7054834
  have htrace : WordTrace (prefixWord ++ tailWord_7054834) baseStart_7054834 baseEnd_7054834 := by
    simpa [prefixWord, tailWord_7054834, baseEnd_7054834] using wordTrace_append hprefix tailTrace_7054834
  have hstable : (prefixWord ++ tailWord_7054834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054834).length < 2 ^ (prefixWord ++ tailWord_7054834).sum := by decide
  have hdescent : baseEnd_7054834 < baseStart_7054834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054838 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2]
def baseStart_7054838 : Nat := 118140960795 + 7054838 * 2 ^ 59
def prefixEnd_7054838 : Nat := 4983230072969 + 3 ^ 40 * 7054838 * 2
def baseEnd_7054838 : Nat := 3622522833603974147580397

theorem tailTrace_7054838 : CollatzResearch.WordTrace tailWord_7054838 prefixEnd_7054838 3622522833603974147580397 := by
  unfold tailWord_7054838
  simp only [CollatzResearch.WordTrace]
  refine ⟨16081942550970891953179823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171540720543689514167251445 16081942550970891953179823)
  ·
    refine ⟨24122913826456337929769735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16081942550970891953179823 24122913826456337929769735)
    ·
      refine ⟨36184370739684506894654603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24122913826456337929769735 36184370739684506894654603)
      ·
        refine ⟨54276556109526760341981905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36184370739684506894654603 54276556109526760341981905)
        ·
          refine ⟨40707417082145070256486429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54276556109526760341981905 40707417082145070256486429)
          ·
            refine ⟨15265281405804401346182411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40707417082145070256486429 15265281405804401346182411)
            ·
              refine ⟨22897922108706602019273617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15265281405804401346182411 22897922108706602019273617)
              ·
                refine ⟨17173441581529951514455213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22897922108706602019273617 17173441581529951514455213)
                ·
                  refine ⟨6440040593073731817920705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17173441581529951514455213 6440040593073731817920705)
                  ·
                    refine ⟨4830030444805298863440529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6440040593073731817920705 4830030444805298863440529)
                    ·
                      refine ⟨3622522833603974147580397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4830030444805298863440529 3622522833603974147580397)
                      ·
                        rfl

theorem cell23_7054838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_7054838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054838 prefixEnd_7054838 := by exact prefixLift 7054838
  have htrace : WordTrace (prefixWord ++ tailWord_7054838) baseStart_7054838 baseEnd_7054838 := by
    simpa [prefixWord, tailWord_7054838, baseEnd_7054838] using wordTrace_append hprefix tailTrace_7054838
  have hstable : (prefixWord ++ tailWord_7054838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054838).length < 2 ^ (prefixWord ++ tailWord_7054838).sum := by decide
  have hdescent : baseEnd_7054838 < baseStart_7054838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054855 : List Nat := [1, 1, 4, 3, 2, 2, 2, 3, 1, 2, 2]
def baseStart_7054855 : Nat := 118140960795 + 7054855 * 2 ^ 59
def prefixEnd_7054855 : Nat := 4983230072969 + 3 ^ 40 * 7054855 * 2
def baseEnd_7054855 : Nat := 3622531562775100581067819

theorem tailTrace_7054855 : CollatzResearch.WordTrace tailWord_7054855 prefixEnd_7054855 3622531562775100581067819 := by
  unfold tailWord_7054855
  simp only [CollatzResearch.WordTrace]
  refine ⟨257311700856472683154246019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171541133904315122102830679 257311700856472683154246019)
  ·
    refine ⟨385967551284709024731369029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257311700856472683154246019 385967551284709024731369029)
    ·
      refine ⟨72368915865882942137131693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385967551284709024731369029 72368915865882942137131693)
      ·
        refine ⟨27138343449706103301424385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72368915865882942137131693 27138343449706103301424385)
        ·
          refine ⟨20353757587279577476068289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27138343449706103301424385 20353757587279577476068289)
          ·
            refine ⟨15265318190459683107051217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20353757587279577476068289 15265318190459683107051217)
            ·
              refine ⟨11448988642844762330288413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15265318190459683107051217 11448988642844762330288413)
              ·
                refine ⟨4293370741066785873858155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11448988642844762330288413 4293370741066785873858155)
                ·
                  refine ⟨6440056111600178810787233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4293370741066785873858155 6440056111600178810787233)
                  ·
                    refine ⟨4830042083700134108090425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6440056111600178810787233 4830042083700134108090425)
                    ·
                      refine ⟨3622531562775100581067819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4830042083700134108090425 3622531562775100581067819)
                      ·
                        rfl

theorem cell23_7054855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_7054855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054855 prefixEnd_7054855 := by exact prefixLift 7054855
  have htrace : WordTrace (prefixWord ++ tailWord_7054855) baseStart_7054855 baseEnd_7054855 := by
    simpa [prefixWord, tailWord_7054855, baseEnd_7054855] using wordTrace_append hprefix tailTrace_7054855
  have hstable : (prefixWord ++ tailWord_7054855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054855).length < 2 ^ (prefixWord ++ tailWord_7054855).sum := by decide
  have hdescent : baseEnd_7054855 < baseStart_7054855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054858 : List Nat := [3, 1, 2, 2, 2, 4, 2, 1, 1, 2, 3]
def baseStart_7054858 : Nat := 118140960795 + 7054858 * 2 ^ 59
def prefixEnd_7054858 : Nat := 4983230072969 + 3 ^ 40 * 7054858 * 2
def baseEnd_7054858 : Nat := 3622533103217064069330305

theorem tailTrace_7054858 : CollatzResearch.WordTrace tailWord_7054858 prefixEnd_7054858 3622533103217064069330305 := by
  unfold tailWord_7054858
  simp only [CollatzResearch.WordTrace]
  refine ⟨64327952568865453666651307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171541206850307876444403485 64327952568865453666651307)
  ·
    refine ⟨96491928853298180499976961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64327952568865453666651307 96491928853298180499976961)
    ·
      refine ⟨72368946639973635374982721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96491928853298180499976961 72368946639973635374982721)
      ·
        refine ⟨54276709979980226531237041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72368946639973635374982721 54276709979980226531237041)
        ·
          refine ⟨40707532484985169898427781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54276709979980226531237041 40707532484985169898427781)
          ·
            refine ⟨7632662340934719355955209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40707532484985169898427781 7632662340934719355955209)
            ·
              refine ⟨5724496755701039516966407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7632662340934719355955209 5724496755701039516966407)
              ·
                refine ⟨8586745133551559275449611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5724496755701039516966407 8586745133551559275449611)
                ·
                  refine ⟨12880117700327338913174417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8586745133551559275449611 12880117700327338913174417)
                  ·
                    refine ⟨9660088275245504184880813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12880117700327338913174417 9660088275245504184880813)
                    ·
                      refine ⟨3622533103217064069330305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9660088275245504184880813 3622533103217064069330305)
                      ·
                        rfl

theorem cell23_7054858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_7054858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054858 prefixEnd_7054858 := by exact prefixLift 7054858
  have htrace : WordTrace (prefixWord ++ tailWord_7054858) baseStart_7054858 baseEnd_7054858 := by
    simpa [prefixWord, tailWord_7054858, baseEnd_7054858] using wordTrace_append hprefix tailTrace_7054858
  have hstable : (prefixWord ++ tailWord_7054858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054858).length < 2 ^ (prefixWord ++ tailWord_7054858).sum := by decide
  have hdescent : baseEnd_7054858 < baseStart_7054858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054861 : List Nat := [1, 7, 1, 1, 2, 1, 10]
def baseStart_7054861 : Nat := 118140960795 + 7054861 * 2 ^ 59
def prefixEnd_7054861 : Nat := 4983230072969 + 3 ^ 40 * 7054861 * 2
def baseEnd_7054861 : Nat := 44722649921716389599911

theorem tailTrace_7054861 : CollatzResearch.WordTrace tailWord_7054861 prefixEnd_7054861 44722649921716389599911 := by
  unfold tailWord_7054861
  simp only [CollatzResearch.WordTrace]
  refine ⟨257311919694450946178964437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171541279796300630785976291 257311919694450946178964437)
  ·
    refine ⟨6030748117838694051069479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 257311919694450946178964437 6030748117838694051069479)
    ·
      refine ⟨9046122176758041076604219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6030748117838694051069479 9046122176758041076604219)
      ·
        refine ⟨13569183265137061614906329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9046122176758041076604219 13569183265137061614906329)
        ·
          refine ⟨10176887448852796211179747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13569183265137061614906329 10176887448852796211179747)
          ·
            refine ⟨15265331173279194316769621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10176887448852796211179747 15265331173279194316769621)
            ·
              refine ⟨44722649921716389599911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15265331173279194316769621 44722649921716389599911)
              ·
                rfl

theorem cell23_7054861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 10].length) (baseStart_7054861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054861 prefixEnd_7054861 := by exact prefixLift 7054861
  have htrace : WordTrace (prefixWord ++ tailWord_7054861) baseStart_7054861 baseEnd_7054861 := by
    simpa [prefixWord, tailWord_7054861, baseEnd_7054861] using wordTrace_append hprefix tailTrace_7054861
  have hstable : (prefixWord ++ tailWord_7054861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054861).length < 2 ^ (prefixWord ++ tailWord_7054861).sum := by decide
  have hdescent : baseEnd_7054861 < baseStart_7054861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054888 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_7054888 : Nat := 118140960795 + 7054888 * 2 ^ 59
def prefixEnd_7054888 : Nat := 4983230072969 + 3 ^ 40 * 7054888 * 2
def baseEnd_7054888 : Nat := 3622548507636698951955167

theorem tailTrace_7054888 : CollatzResearch.WordTrace tailWord_7054888 prefixEnd_7054888 3622548507636698951955167 := by
  unfold tailWord_7054888
  simp only [CollatzResearch.WordTrace]
  refine ⟨128656452232676564895098659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171541936310235419860131545 128656452232676564895098659)
  ·
    refine ⟨192984678349014847342647989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128656452232676564895098659 192984678349014847342647989)
    ·
      refine ⟨18092313595220141938373249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192984678349014847342647989 18092313595220141938373249)
      ·
        refine ⟨13569235196415106453779937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18092313595220141938373249 13569235196415106453779937)
        ·
          refine ⟨10176926397311329840334953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13569235196415106453779937 10176926397311329840334953)
          ·
            refine ⟨7632694797983497380251215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10176926397311329840334953 7632694797983497380251215)
            ·
              refine ⟨11449042196975246070376823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7632694797983497380251215 11449042196975246070376823)
              ·
                refine ⟨17173563295462869105565235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11449042196975246070376823 17173563295462869105565235)
                ·
                  refine ⟨25760344943194303658347853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17173563295462869105565235 25760344943194303658347853)
                  ·
                    refine ⟨9660129353697863871880445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25760344943194303658347853 9660129353697863871880445)
                    ·
                      refine ⟨3622548507636698951955167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9660129353697863871880445 3622548507636698951955167)
                      ·
                        rfl

theorem cell23_7054888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_7054888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054888 prefixEnd_7054888 := by exact prefixLift 7054888
  have htrace : WordTrace (prefixWord ++ tailWord_7054888) baseStart_7054888 baseEnd_7054888 := by
    simpa [prefixWord, tailWord_7054888, baseEnd_7054888] using wordTrace_append hprefix tailTrace_7054888
  have hstable : (prefixWord ++ tailWord_7054888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054888).length < 2 ^ (prefixWord ++ tailWord_7054888).sum := by decide
  have hdescent : baseEnd_7054888 < baseStart_7054888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054897 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 2, 1, 5]
def baseStart_7054897 : Nat := 118140960795 + 7054897 * 2 ^ 59
def prefixEnd_7054897 : Nat := 4983230072969 + 3 ^ 40 * 7054897 * 2
def baseEnd_7054897 : Nat := 3622553128962589416742625

theorem tailTrace_7054897 : CollatzResearch.WordTrace tailWord_7054897 prefixEnd_7054897 3622553128962589416742625 := by
  unfold tailWord_7054897
  simp only [CollatzResearch.WordTrace]
  refine ⟨257313232722320524327274945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171542155148213682884849963 257313232722320524327274945)
  ·
    refine ⟨192984924541740393245456209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257313232722320524327274945 192984924541740393245456209)
    ·
      refine ⟨144738693406305294934092157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192984924541740393245456209 144738693406305294934092157)
      ·
        refine ⟨54277010027364485600284559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144738693406305294934092157 54277010027364485600284559)
        ·
          refine ⟨81415515041046728400426839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54277010027364485600284559 81415515041046728400426839)
          ·
            refine ⟨122123272561570092600640259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81415515041046728400426839 122123272561570092600640259)
            ·
              refine ⟨183184908842355138900960389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122123272561570092600640259 183184908842355138900960389)
              ·
                refine ⟨34347170407941588543930073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183184908842355138900960389 34347170407941588543930073)
                ·
                  refine ⟨25760377805956191407947555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34347170407941588543930073 25760377805956191407947555)
                  ·
                    refine ⟨38640566708934287111921333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25760377805956191407947555 38640566708934287111921333)
                    ·
                      refine ⟨3622553128962589416742625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38640566708934287111921333 3622553128962589416742625)
                      ·
                        rfl

theorem cell23_7054897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_7054897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054897 prefixEnd_7054897 := by exact prefixLift 7054897
  have htrace : WordTrace (prefixWord ++ tailWord_7054897) baseStart_7054897 baseEnd_7054897 := by
    simpa [prefixWord, tailWord_7054897, baseEnd_7054897] using wordTrace_append hprefix tailTrace_7054897
  have hstable : (prefixWord ++ tailWord_7054897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054897).length < 2 ^ (prefixWord ++ tailWord_7054897).sum := by decide
  have hdescent : baseEnd_7054897 < baseStart_7054897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054911 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 4, 2, 2]
def baseStart_7054911 : Nat := 118140960795 + 7054911 * 2 ^ 59
def prefixEnd_7054911 : Nat := 4983230072969 + 3 ^ 40 * 7054911 * 2
def baseEnd_7054911 : Nat := 3622560317691752361967561

theorem tailTrace_7054911 : CollatzResearch.WordTrace tailWord_7054911 prefixEnd_7054911 3622560317691752361967561 := by
  unfold tailWord_7054911
  simp only [CollatzResearch.WordTrace]
  refine ⟨257313743344269804718284587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171542495562846536478856391 257313743344269804718284587)
  ·
    refine ⟨385970615016404707077426881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257313743344269804718284587 385970615016404707077426881)
    ·
      refine ⟨289477961262303530308070161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385970615016404707077426881 289477961262303530308070161)
      ·
        refine ⟨217108470946727647731052621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289477961262303530308070161 217108470946727647731052621)
        ·
          refine ⟨81415676605022867899144733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217108470946727647731052621 81415676605022867899144733)
          ·
            refine ⟨30530878726883575462179275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81415676605022867899144733 30530878726883575462179275)
            ·
              refine ⟨45796318090325363193268913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30530878726883575462179275 45796318090325363193268913)
              ·
                refine ⟨34347238567744022394951685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45796318090325363193268913 34347238567744022394951685)
                ·
                  refine ⟨6440107231452004199053441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34347238567744022394951685 6440107231452004199053441)
                  ·
                    refine ⟨4830080423589003149290081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6440107231452004199053441 4830080423589003149290081)
                    ·
                      refine ⟨3622560317691752361967561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4830080423589003149290081 3622560317691752361967561)
                      ·
                        rfl

theorem cell23_7054911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 2, 2].length) (baseStart_7054911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054911 prefixEnd_7054911 := by exact prefixLift 7054911
  have htrace : WordTrace (prefixWord ++ tailWord_7054911) baseStart_7054911 baseEnd_7054911 := by
    simpa [prefixWord, tailWord_7054911, baseEnd_7054911] using wordTrace_append hprefix tailTrace_7054911
  have hstable : (prefixWord ++ tailWord_7054911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054911).length < 2 ^ (prefixWord ++ tailWord_7054911).sum := by decide
  have hdescent : baseEnd_7054911 < baseStart_7054911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7054987 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 5]
def baseStart_7054987 : Nat := 118140960795 + 7054987 * 2 ^ 59
def prefixEnd_7054987 : Nat := 4983230072969 + 3 ^ 40 * 7054987 * 2
def baseEnd_7054987 : Nat := 3622599342221494064617211

theorem tailTrace_7054987 : CollatzResearch.WordTrace tailWord_7054987 prefixEnd_7054987 3622599342221494064617211 := by
  unfold tailWord_7054987
  simp only [CollatzResearch.WordTrace]
  refine ⟨257316515291994469698051215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171544343527996313132034143 257316515291994469698051215)
  ·
    refine ⟨385974772937991704547076823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257316515291994469698051215 385974772937991704547076823)
    ·
      refine ⟨578962159406987556820615235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385974772937991704547076823 578962159406987556820615235)
      ·
        refine ⟨868443239110481335230922853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578962159406987556820615235 868443239110481335230922853)
        ·
          refine ⟨162833107333215250355798035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 868443239110481335230922853 162833107333215250355798035)
          ·
            refine ⟨244249660999822875533697053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162833107333215250355798035 244249660999822875533697053)
            ·
              refine ⟨91593622874933578325136395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244249660999822875533697053 91593622874933578325136395)
              ·
                refine ⟨137390434312400367487704593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91593622874933578325136395 137390434312400367487704593)
                ·
                  refine ⟨103042825734300275615778445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137390434312400367487704593 103042825734300275615778445)
                  ·
                    refine ⟨38641059650362603355916917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103042825734300275615778445 38641059650362603355916917)
                    ·
                      refine ⟨3622599342221494064617211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38641059650362603355916917 3622599342221494064617211)
                      ·
                        rfl

theorem cell23_7054987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 5].length) (baseStart_7054987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7054987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7054987 prefixEnd_7054987 := by exact prefixLift 7054987
  have htrace : WordTrace (prefixWord ++ tailWord_7054987) baseStart_7054987 baseEnd_7054987 := by
    simpa [prefixWord, tailWord_7054987, baseEnd_7054987] using wordTrace_append hprefix tailTrace_7054987
  have hstable : (prefixWord ++ tailWord_7054987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7054987).length < 2 ^ (prefixWord ++ tailWord_7054987).sum := by decide
  have hdescent : baseEnd_7054987 < baseStart_7054987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7054987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055021 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_7055021 : Nat := 118140960795 + 7055021 * 2 ^ 59
def prefixEnd_7055021 : Nat := 4983230072969 + 3 ^ 40 * 7055021 * 2
def baseEnd_7055021 : Nat := 3622616800563746931592055

theorem tailTrace_7055021 : CollatzResearch.WordTrace tailWord_7055021 prefixEnd_7055021 3622616800563746931592055 := by
  unfold tailWord_7055021
  simp only [CollatzResearch.WordTrace]
  refine ⟨257317755373871293504788917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171545170249247529003192611 257317755373871293504788917)
  ·
    refine ⟨24123539566300433766073961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257317755373871293504788917 24123539566300433766073961)
    ·
      refine ⟨18092654674725325324555471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24123539566300433766073961 18092654674725325324555471)
      ·
        refine ⟨27138982012087987986833207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18092654674725325324555471 27138982012087987986833207)
        ·
          refine ⟨40708473018131981980249811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27138982012087987986833207 40708473018131981980249811)
          ·
            refine ⟨61062709527197972970374717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40708473018131981980249811 61062709527197972970374717)
            ·
              refine ⟨22898516072699239863890519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61062709527197972970374717 22898516072699239863890519)
              ·
                refine ⟨34347774109048859795835779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22898516072699239863890519 34347774109048859795835779)
                ·
                  refine ⟨51521661163573289693753669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34347774109048859795835779 51521661163573289693753669)
                  ·
                    refine ⟨9660311468169991817578813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51521661163573289693753669 9660311468169991817578813)
                    ·
                      refine ⟨3622616800563746931592055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9660311468169991817578813 3622616800563746931592055)
                      ·
                        rfl

theorem cell23_7055021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_7055021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055021 prefixEnd_7055021 := by exact prefixLift 7055021
  have htrace : WordTrace (prefixWord ++ tailWord_7055021) baseStart_7055021 baseEnd_7055021 := by
    simpa [prefixWord, tailWord_7055021, baseEnd_7055021] using wordTrace_append hprefix tailTrace_7055021
  have hstable : (prefixWord ++ tailWord_7055021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055021).length < 2 ^ (prefixWord ++ tailWord_7055021).sum := by decide
  have hdescent : baseEnd_7055021 < baseStart_7055021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055044 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_7055044 : Nat := 118140960795 + 7055044 * 2 ^ 59
def prefixEnd_7055044 : Nat := 4983230072969 + 3 ^ 40 * 7055044 * 2
def baseEnd_7055044 : Nat := 3622628610618800341604449

theorem tailTrace_7055044 : CollatzResearch.WordTrace tailWord_7055044 prefixEnd_7055044 3622628610618800341604449 := by
  unfold tailWord_7055044
  simp only [CollatzResearch.WordTrace]
  refine ⟨128659297126393984216438093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171545729501858645621917457 128659297126393984216438093)
  ·
    refine ⟨48247236422397744081164285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128659297126393984216438093 48247236422397744081164285)
    ·
      refine ⟨18092713658399154030436607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48247236422397744081164285 18092713658399154030436607)
      ·
        refine ⟨27139070487598731045654911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18092713658399154030436607 27139070487598731045654911)
        ·
          refine ⟨40708605731398096568482367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27139070487598731045654911 40708605731398096568482367)
          ·
            refine ⟨61062908597097144852723551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40708605731398096568482367 61062908597097144852723551)
            ·
              refine ⟨91594362895645717279085327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61062908597097144852723551 91594362895645717279085327)
              ·
                refine ⟨137391544343468575918627991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91594362895645717279085327 137391544343468575918627991)
                ·
                  refine ⟨206087316515202863877941987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137391544343468575918627991 206087316515202863877941987)
                  ·
                    refine ⟨309130974772804295816912981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 206087316515202863877941987 309130974772804295816912981)
                    ·
                      refine ⟨3622628610618800341604449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 309130974772804295816912981 3622628610618800341604449)
                      ·
                        rfl

theorem cell23_7055044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_7055044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055044 prefixEnd_7055044 := by exact prefixLift 7055044
  have htrace : WordTrace (prefixWord ++ tailWord_7055044) baseStart_7055044 baseEnd_7055044 := by
    simpa [prefixWord, tailWord_7055044, baseEnd_7055044] using wordTrace_append hprefix tailTrace_7055044
  have hstable : (prefixWord ++ tailWord_7055044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055044).length < 2 ^ (prefixWord ++ tailWord_7055044).sum := by decide
  have hdescent : baseEnd_7055044 < baseStart_7055044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055058 : List Nat := [3, 2, 2, 2, 2, 2, 3, 1, 6]
def baseStart_7055058 : Nat := 118140960795 + 7055058 * 2 ^ 59
def prefixEnd_7055058 : Nat := 4983230072969 + 3 ^ 40 * 7055058 * 2
def baseEnd_7055058 : Nat := 402515088816440365203265

theorem tailTrace_7055058 : CollatzResearch.WordTrace tailWord_7055058 prefixEnd_7055058 402515088816440365203265 := by
  unfold tailWord_7055058
  simp only [CollatzResearch.WordTrace]
  refine ⟨64329776218684312205971457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171546069916491499215923885 64329776218684312205971457)
  ·
    refine ⟨48247332164013234154478593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64329776218684312205971457 48247332164013234154478593)
    ·
      refine ⟨36185499123009925615858945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48247332164013234154478593 36185499123009925615858945)
      ·
        refine ⟨27139124342257444211894209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36185499123009925615858945 27139124342257444211894209)
        ·
          refine ⟨20354343256693083158920657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27139124342257444211894209 20354343256693083158920657)
          ·
            refine ⟨15265757442519812369190493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20354343256693083158920657 15265757442519812369190493)
            ·
              refine ⟨5724659040944929638446435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15265757442519812369190493 5724659040944929638446435)
              ·
                refine ⟨8586988561417394457669653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5724659040944929638446435 8586988561417394457669653)
                ·
                  refine ⟨402515088816440365203265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8586988561417394457669653 402515088816440365203265)
                  ·
                    rfl

theorem cell23_7055058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_7055058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055058 prefixEnd_7055058 := by exact prefixLift 7055058
  have htrace : WordTrace (prefixWord ++ tailWord_7055058) baseStart_7055058 baseEnd_7055058 := by
    simpa [prefixWord, tailWord_7055058, baseEnd_7055058] using wordTrace_append hprefix tailTrace_7055058
  have hstable : (prefixWord ++ tailWord_7055058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055058).length < 2 ^ (prefixWord ++ tailWord_7055058).sum := by decide
  have hdescent : baseEnd_7055058 < baseStart_7055058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055071 : List Nat := [1, 1, 2, 3, 2, 2, 4, 2, 1, 5]
def baseStart_7055071 : Nat := 118140960795 + 7055071 * 2 ^ 59
def prefixEnd_7055071 : Nat := 4983230072969 + 3 ^ 40 * 7055071 * 2
def baseEnd_7055071 : Nat := 1207547491532157245322275

theorem tailTrace_7055071 : CollatzResearch.WordTrace tailWord_7055071 prefixEnd_7055071 1207547491532157245322275 := by
  unfold tailWord_7055071
  simp only [CollatzResearch.WordTrace]
  refine ⟨257319579023690152044109067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171546386015793434696072711 257319579023690152044109067)
  ·
    refine ⟨385979368535535228066163601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257319579023690152044109067 385979368535535228066163601)
    ·
      refine ⟨289484526401651421049622701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385979368535535228066163601 289484526401651421049622701)
      ·
        refine ⟨108556697400619282893608513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289484526401651421049622701 108556697400619282893608513)
        ·
          refine ⟨81417523050464462170206385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108556697400619282893608513 81417523050464462170206385)
          ·
            refine ⟨61063142287848346627654789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81417523050464462170206385 61063142287848346627654789)
            ·
              refine ⟨11449339178971564992685273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61063142287848346627654789 11449339178971564992685273)
              ·
                refine ⟨8587004384228673744513955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11449339178971564992685273 8587004384228673744513955)
                ·
                  refine ⟨12880506576343010616770933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8587004384228673744513955 12880506576343010616770933)
                  ·
                    refine ⟨1207547491532157245322275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12880506576343010616770933 1207547491532157245322275)
                    ·
                      rfl

theorem cell23_7055071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 5].length) (baseStart_7055071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055071 prefixEnd_7055071 := by exact prefixLift 7055071
  have htrace : WordTrace (prefixWord ++ tailWord_7055071) baseStart_7055071 baseEnd_7055071 := by
    simpa [prefixWord, tailWord_7055071, baseEnd_7055071] using wordTrace_append hprefix tailTrace_7055071
  have hstable : (prefixWord ++ tailWord_7055071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055071).length < 2 ^ (prefixWord ++ tailWord_7055071).sum := by decide
  have hdescent : baseEnd_7055071 < baseStart_7055071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055079 : List Nat := [1, 1, 5, 4, 2, 1, 1, 3, 1, 4]
def baseStart_7055079 : Nat := 118140960795 + 7055079 * 2 ^ 59
def prefixEnd_7055079 : Nat := 4983230072969 + 3 ^ 40 * 7055079 * 2
def baseEnd_7055079 : Nat := 1207548860813902568222263

theorem tailTrace_7055079 : CollatzResearch.WordTrace tailWord_7055079 prefixEnd_7055079 1207548860813902568222263 := by
  unfold tailWord_7055079
  simp only [CollatzResearch.WordTrace]
  refine ⟨257319870807661169410400291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171546580538440779606933527 257319870807661169410400291)
  ·
    refine ⟨385979806211491754115600437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257319870807661169410400291 385979806211491754115600437)
    ·
      refine ⟨36185606832327351948337541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 385979806211491754115600437 36185606832327351948337541)
      ·
        refine ⟨6784801281061378490313289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36185606832327351948337541 6784801281061378490313289)
        ·
          refine ⟨5088600960796033867734967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6784801281061378490313289 5088600960796033867734967)
          ·
            refine ⟨7632901441194050801602451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5088600960796033867734967 7632901441194050801602451)
            ·
              refine ⟨11449352161791076202403677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7632901441194050801602451 11449352161791076202403677)
              ·
                refine ⟨4293507060671653575901379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11449352161791076202403677 4293507060671653575901379)
                ·
                  refine ⟨6440260591007480363852069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4293507060671653575901379 6440260591007480363852069)
                  ·
                    refine ⟨1207548860813902568222263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6440260591007480363852069 1207548860813902568222263)
                    ·
                      rfl

theorem cell23_7055079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_7055079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055079 prefixEnd_7055079 := by exact prefixLift 7055079
  have htrace : WordTrace (prefixWord ++ tailWord_7055079) baseStart_7055079 baseEnd_7055079 := by
    simpa [prefixWord, tailWord_7055079, baseEnd_7055079] using wordTrace_append hprefix tailTrace_7055079
  have hstable : (prefixWord ++ tailWord_7055079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055079).length < 2 ^ (prefixWord ++ tailWord_7055079).sum := by decide
  have hdescent : baseEnd_7055079 < baseStart_7055079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055084 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 1, 6]
def baseStart_7055084 : Nat := 118140960795 + 7055084 * 2 ^ 59
def prefixEnd_7055084 : Nat := 4983230072969 + 3 ^ 40 * 7055084 * 2
def baseEnd_7055084 : Nat := 1207549716614993395034755

theorem tailTrace_7055084 : CollatzResearch.WordTrace tailWord_7055084 prefixEnd_7055084 1207549716614993395034755 := by
  unfold tailWord_7055084
  simp only [CollatzResearch.WordTrace]
  refine ⟨128660026586321527632166153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171546702115095370176221537 128660026586321527632166153)
  ·
    refine ⟨96495019939741145724124615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128660026586321527632166153 96495019939741145724124615)
    ·
      refine ⟨144742529909611718586186923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96495019939741145724124615 144742529909611718586186923)
      ·
        refine ⟨217113794864417577879280385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144742529909611718586186923 217113794864417577879280385)
        ·
          refine ⟨162835346148313183409460289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217113794864417577879280385 162835346148313183409460289)
          ·
            refine ⟨122126509611234887557095217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162835346148313183409460289 122126509611234887557095217)
            ·
              refine ⟨91594882208426165667821413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122126509611234887557095217 91594882208426165667821413)
              ·
                refine ⟨17174040414079906062716515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91594882208426165667821413 17174040414079906062716515)
                ·
                  refine ⟨25761060621119859094074773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17174040414079906062716515 25761060621119859094074773)
                  ·
                    refine ⟨1207549716614993395034755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25761060621119859094074773 1207549716614993395034755)
                    ·
                      rfl

theorem cell23_7055084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_7055084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055084 prefixEnd_7055084 := by exact prefixLift 7055084
  have htrace : WordTrace (prefixWord ++ tailWord_7055084) baseStart_7055084 baseEnd_7055084 := by
    simpa [prefixWord, tailWord_7055084, baseEnd_7055084] using wordTrace_append hprefix tailTrace_7055084
  have hstable : (prefixWord ++ tailWord_7055084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055084).length < 2 ^ (prefixWord ++ tailWord_7055084).sum := by decide
  have hdescent : baseEnd_7055084 < baseStart_7055084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055091 : List Nat := [1, 1, 1, 2, 2, 3, 4, 3, 1, 1, 4]
def baseStart_7055091 : Nat := 118140960795 + 7055091 * 2 ^ 59
def prefixEnd_7055091 : Nat := 4983230072969 + 3 ^ 40 * 7055091 * 2
def baseEnd_7055091 : Nat := 3622652744209561657716733

theorem tailTrace_7055091 : CollatzResearch.WordTrace tailWord_7055091 prefixEnd_7055091 3622652744209561657716733 := by
  unfold tailWord_7055091
  simp only [CollatzResearch.WordTrace]
  refine ⟨257320308483617695459837127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171546872322411796973224751 257320308483617695459837127)
  ·
    refine ⟨385980462725426543189755691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257320308483617695459837127 385980462725426543189755691)
    ·
      refine ⟨578970694088139814784633537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385980462725426543189755691 578970694088139814784633537)
      ·
        refine ⟨434228020566104861088475153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578970694088139814784633537 434228020566104861088475153)
        ·
          refine ⟨325671015424578645816356365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434228020566104861088475153 325671015424578645816356365)
          ·
            refine ⟨122126630784216992181133637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325671015424578645816356365 122126630784216992181133637)
            ·
              refine ⟨22898743272040686033962557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122126630784216992181133637 22898743272040686033962557)
              ·
                refine ⟨8587028727015257262735959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22898743272040686033962557 8587028727015257262735959)
                ·
                  refine ⟨12880543090522885894103939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8587028727015257262735959 12880543090522885894103939)
                  ·
                    refine ⟨19320814635784328841155909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12880543090522885894103939 19320814635784328841155909)
                    ·
                      refine ⟨3622652744209561657716733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19320814635784328841155909 3622652744209561657716733)
                      ·
                        rfl

theorem cell23_7055091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 1, 4].length) (baseStart_7055091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055091 prefixEnd_7055091 := by exact prefixLift 7055091
  have htrace : WordTrace (prefixWord ++ tailWord_7055091) baseStart_7055091 baseEnd_7055091 := by
    simpa [prefixWord, tailWord_7055091, baseEnd_7055091] using wordTrace_append hprefix tailTrace_7055091
  have hstable : (prefixWord ++ tailWord_7055091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055091).length < 2 ^ (prefixWord ++ tailWord_7055091).sum := by decide
  have hdescent : baseEnd_7055091 < baseStart_7055091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055102 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_7055102 : Nat := 118140960795 + 7055102 * 2 ^ 59
def prefixEnd_7055102 : Nat := 4983230072969 + 3 ^ 40 * 7055102 * 2
def baseEnd_7055102 : Nat := 3622658392496761114679183

theorem tailTrace_7055102 : CollatzResearch.WordTrace tailWord_7055102 prefixEnd_7055102 3622658392496761114679183 := by
  unfold tailWord_7055102
  simp only [CollatzResearch.WordTrace]
  refine ⟨32165088710822230542310945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171547139791051896225658373 32165088710822230542310945)
  ·
    refine ⟨24123816533116672906733209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32165088710822230542310945 24123816533116672906733209)
    ·
      refine ⟨18092862399837504680049907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24123816533116672906733209 18092862399837504680049907)
      ·
        refine ⟨27139293599756257020074861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18092862399837504680049907 27139293599756257020074861)
        ·
          refine ⟨10177235099908596382528073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27139293599756257020074861 10177235099908596382528073)
          ·
            refine ⟨7632926324931447286896055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10177235099908596382528073 7632926324931447286896055)
            ·
              refine ⟨11449389487397170930344083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7632926324931447286896055 11449389487397170930344083)
              ·
                refine ⟨17174084231095756395516125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11449389487397170930344083 17174084231095756395516125)
                ·
                  refine ⟨6440281586660908648318547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17174084231095756395516125 6440281586660908648318547)
                  ·
                    refine ⟨9660422379991362972477821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6440281586660908648318547 9660422379991362972477821)
                    ·
                      refine ⟨3622658392496761114679183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9660422379991362972477821 3622658392496761114679183)
                      ·
                        rfl

theorem cell23_7055102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_7055102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055102 prefixEnd_7055102 := by exact prefixLift 7055102
  have htrace : WordTrace (prefixWord ++ tailWord_7055102) baseStart_7055102 baseEnd_7055102 := by
    simpa [prefixWord, tailWord_7055102, baseEnd_7055102] using wordTrace_append hprefix tailTrace_7055102
  have hstable : (prefixWord ++ tailWord_7055102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055102).length < 2 ^ (prefixWord ++ tailWord_7055102).sum := by decide
  have hdescent : baseEnd_7055102 < baseStart_7055102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055104 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 4]
def baseStart_7055104 : Nat := 118140960795 + 7055104 * 2 ^ 59
def prefixEnd_7055104 : Nat := 4983230072969 + 3 ^ 40 * 7055104 * 2
def baseEnd_7055104 : Nat := 3622659419458070106854173

theorem tailTrace_7055104 : CollatzResearch.WordTrace tailWord_7055104 prefixEnd_7055104 3622659419458070106854173 := by
  unfold tailWord_7055104
  simp only [CollatzResearch.WordTrace]
  refine ⟨128660391316285299340030183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171547188421713732453373577 128660391316285299340030183)
  ·
    refine ⟨192990586974427949010045275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128660391316285299340030183 192990586974427949010045275)
    ·
      refine ⟨289485880461641923515067913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192990586974427949010045275 289485880461641923515067913)
      ·
        refine ⟨217114410346231442636300935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289485880461641923515067913 217114410346231442636300935)
        ·
          refine ⟨325671615519347163954451403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217114410346231442636300935 325671615519347163954451403)
          ·
            refine ⟨488507423279020745931677105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325671615519347163954451403 488507423279020745931677105)
            ·
              refine ⟨366380567459265559448757829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488507423279020745931677105 366380567459265559448757829)
              ·
                refine ⟨68696356398612292396642093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366380567459265559448757829 68696356398612292396642093)
                ·
                  refine ⟨25761133649479609648740785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68696356398612292396642093 25761133649479609648740785)
                  ·
                    refine ⟨19320850237109707236555589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25761133649479609648740785 19320850237109707236555589)
                    ·
                      refine ⟨3622659419458070106854173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19320850237109707236555589 3622659419458070106854173)
                      ·
                        rfl

theorem cell23_7055104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_7055104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055104 prefixEnd_7055104 := by exact prefixLift 7055104
  have htrace : WordTrace (prefixWord ++ tailWord_7055104) baseStart_7055104 baseEnd_7055104 := by
    simpa [prefixWord, tailWord_7055104, baseEnd_7055104] using wordTrace_append hprefix tailTrace_7055104
  have hstable : (prefixWord ++ tailWord_7055104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055104).length < 2 ^ (prefixWord ++ tailWord_7055104).sum := by decide
  have hdescent : baseEnd_7055104 < baseStart_7055104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055114 : List Nat := [3, 1, 2, 2, 1, 3, 1, 10]
def baseStart_7055114 : Nat := 118140960795 + 7055114 * 2 ^ 59
def prefixEnd_7055114 : Nat := 4983230072969 + 3 ^ 40 * 7055114 * 2
def baseEnd_7055114 : Nat := 134172761269059817323301

theorem tailTrace_7055114 : CollatzResearch.WordTrace tailWord_7055114 prefixEnd_7055114 134172761269059817323301 := by
  unfold tailWord_7055114
  simp only [CollatzResearch.WordTrace]
  refine ⟨64330286840633592596981099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171547431575022913591949597 64330286840633592596981099)
  ·
    refine ⟨96495430260950388895471649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64330286840633592596981099 96495430260950388895471649)
    ·
      refine ⟨72371572695712791671603737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96495430260950388895471649 72371572695712791671603737)
      ·
        refine ⟨54278679521784593753702803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72371572695712791671603737 54278679521784593753702803)
        ·
          refine ⟨81418019282676890630554205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54278679521784593753702803 81418019282676890630554205)
          ·
            refine ⟨30531757231003833986457827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81418019282676890630554205 30531757231003833986457827)
            ·
              refine ⟨45797635846505750979686741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30531757231003833986457827 45797635846505750979686741)
              ·
                refine ⟨134172761269059817323301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45797635846505750979686741 134172761269059817323301)
                ·
                  rfl

theorem cell23_7055114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 10].length) (baseStart_7055114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055114 prefixEnd_7055114 := by exact prefixLift 7055114
  have htrace : WordTrace (prefixWord ++ tailWord_7055114) baseStart_7055114 baseEnd_7055114 := by
    simpa [prefixWord, tailWord_7055114, baseEnd_7055114] using wordTrace_append hprefix tailTrace_7055114
  have hstable : (prefixWord ++ tailWord_7055114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055114).length < 2 ^ (prefixWord ++ tailWord_7055114).sum := by decide
  have hdescent : baseEnd_7055114 < baseStart_7055114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055128 : List Nat := [2, 1, 2, 3, 1, 1, 5, 2, 1, 2, 3]
def baseStart_7055128 : Nat := 118140960795 + 7055128 * 2 ^ 59
def prefixEnd_7055128 : Nat := 4983230072969 + 3 ^ 40 * 7055128 * 2
def baseEnd_7055128 : Nat := 3622671742993778012954063

theorem tailTrace_7055128 : CollatzResearch.WordTrace tailWord_7055128 prefixEnd_7055128 3622671742993778012954063 := by
  unfold tailWord_7055128
  simp only [CollatzResearch.WordTrace]
  refine ⟨128660828992241825389467019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171547771989655767185956025 128660828992241825389467019)
  ·
    refine ⟨192991243488362738084200529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128660828992241825389467019 192991243488362738084200529)
    ·
      refine ⟨144743432616272053563150397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192991243488362738084200529 144743432616272053563150397)
      ·
        refine ⟨54278787231102020086181399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144743432616272053563150397 54278787231102020086181399)
        ·
          refine ⟨81418180846653030129272099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54278787231102020086181399 81418180846653030129272099)
          ·
            refine ⟨122127271269979545193908149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81418180846653030129272099 122127271269979545193908149)
            ·
              refine ⟨11449431681560582361928889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122127271269979545193908149 11449431681560582361928889)
              ·
                refine ⟨8587073761170436771446667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11449431681560582361928889 8587073761170436771446667)
                ·
                  refine ⟨12880610641755655157170001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8587073761170436771446667 12880610641755655157170001)
                  ·
                    refine ⟨9660457981316741367877501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12880610641755655157170001 9660457981316741367877501)
                    ·
                      refine ⟨3622671742993778012954063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9660457981316741367877501 3622671742993778012954063)
                      ·
                        rfl

theorem cell23_7055128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_7055128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055128 prefixEnd_7055128 := by exact prefixLift 7055128
  have htrace : WordTrace (prefixWord ++ tailWord_7055128) baseStart_7055128 baseEnd_7055128 := by
    simpa [prefixWord, tailWord_7055128, baseEnd_7055128] using wordTrace_append hprefix tailTrace_7055128
  have hstable : (prefixWord ++ tailWord_7055128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055128).length < 2 ^ (prefixWord ++ tailWord_7055128).sum := by decide
  have hdescent : baseEnd_7055128 < baseStart_7055128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055141 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 3, 3, 3]
def baseStart_7055141 : Nat := 118140960795 + 7055141 * 2 ^ 59
def prefixEnd_7055141 : Nat := 4983230072969 + 3 ^ 40 * 7055141 * 2
def baseEnd_7055141 : Nat := 3622678418242286462091503

theorem tailTrace_7055141 : CollatzResearch.WordTrace tailWord_7055141 prefixEnd_7055141 3622678418242286462091503 := by
  unfold tailWord_7055141
  simp only [CollatzResearch.WordTrace]
  refine ⟨257322132133436553999157277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171548088088957702666104851 257322132133436553999157277)
  ·
    refine ⟨96495799550038707749683979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257322132133436553999157277 96495799550038707749683979)
    ·
      refine ⟨144743699325058061624525969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96495799550038707749683979 144743699325058061624525969)
      ·
        refine ⟨108557774493793546218394477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144743699325058061624525969 108557774493793546218394477)
        ·
          refine ⟨40709165435172579831897929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108557774493793546218394477 40709165435172579831897929)
          ·
            refine ⟨30531874076379434873923447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40709165435172579831897929 30531874076379434873923447)
            ·
              refine ⟨45797811114569152310885171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30531874076379434873923447 45797811114569152310885171)
              ·
                refine ⟨68696716671853728466327757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45797811114569152310885171 68696716671853728466327757)
                ·
                  refine ⟨25761268751945148174872909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68696716671853728466327757 25761268751945148174872909)
                  ·
                    refine ⟨9660475781979430565577341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25761268751945148174872909 9660475781979430565577341)
                    ·
                      refine ⟨3622678418242286462091503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9660475781979430565577341 3622678418242286462091503)
                      ·
                        rfl

theorem cell23_7055141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_7055141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055141 prefixEnd_7055141 := by exact prefixLift 7055141
  have htrace : WordTrace (prefixWord ++ tailWord_7055141) baseStart_7055141 baseEnd_7055141 := by
    simpa [prefixWord, tailWord_7055141, baseEnd_7055141] using wordTrace_append hprefix tailTrace_7055141
  have hstable : (prefixWord ++ tailWord_7055141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055141).length < 2 ^ (prefixWord ++ tailWord_7055141).sum := by decide
  have hdescent : baseEnd_7055141 < baseStart_7055141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055202 : List Nat := [3, 3, 2, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_7055202 : Nat := 118140960795 + 7055202 * 2 ^ 59
def prefixEnd_7055202 : Nat := 4983230072969 + 3 ^ 40 * 7055202 * 2
def baseEnd_7055202 : Nat := 3622709740562210723428723

theorem tailTrace_7055202 : CollatzResearch.WordTrace tailWord_7055202 prefixEnd_7055202 3622709740562210723428723 := by
  unfold tailWord_7055202
  simp only [CollatzResearch.WordTrace]
  refine ⟨64331089246553890354281965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171549571324143707611418573 64331089246553890354281965)
  ·
    refine ⟨24124158467457708882855737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64331089246553890354281965 24124158467457708882855737)
    ·
      refine ⟨18093118850593281662141803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24124158467457708882855737 18093118850593281662141803)
      ·
        refine ⟨27139678275889922493212705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18093118850593281662141803 27139678275889922493212705)
        ·
          refine ⟨20354758706917441869909529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27139678275889922493212705 20354758706917441869909529)
          ·
            refine ⟨15266069030188081402432147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20354758706917441869909529 15266069030188081402432147)
            ·
              refine ⟨22899103545282122103648221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15266069030188081402432147 22899103545282122103648221)
              ·
                refine ⟨8587163829480795788868083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22899103545282122103648221 8587163829480795788868083)
                ·
                  refine ⟨12880745744221193683302125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8587163829480795788868083 12880745744221193683302125)
                  ·
                    refine ⟨4830279654082947631238297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12880745744221193683302125 4830279654082947631238297)
                    ·
                      refine ⟨3622709740562210723428723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4830279654082947631238297 3622709740562210723428723)
                      ·
                        rfl

theorem cell23_7055202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_7055202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055202 prefixEnd_7055202 := by exact prefixLift 7055202
  have htrace : WordTrace (prefixWord ++ tailWord_7055202) baseStart_7055202 baseEnd_7055202 := by
    simpa [prefixWord, tailWord_7055202, baseEnd_7055202] using wordTrace_append hprefix tailTrace_7055202
  have hstable : (prefixWord ++ tailWord_7055202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055202).length < 2 ^ (prefixWord ++ tailWord_7055202).sum := by decide
  have hdescent : baseEnd_7055202 < baseStart_7055202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055232 : List Nat := [2, 1, 1, 2, 1, 2, 7, 1, 2, 2, 2]
def baseStart_7055232 : Nat := 118140960795 + 7055232 * 2 ^ 59
def prefixEnd_7055232 : Nat := 4983230072969 + 3 ^ 40 * 7055232 * 2
def baseEnd_7055232 : Nat := 3622725144981845606053585

theorem tailTrace_7055232 : CollatzResearch.WordTrace tailWord_7055232 prefixEnd_7055232 3622725144981845606053585 := by
  unfold tailWord_7055232
  simp only [CollatzResearch.WordTrace]
  refine ⟨128662725588053438270359975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171550300784071251027146633 128662725588053438270359975)
  ·
    refine ⟨192994088382080157405539963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128662725588053438270359975 192994088382080157405539963)
    ·
      refine ⟨289491132573120236108309945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192994088382080157405539963 289491132573120236108309945)
      ·
        refine ⟨217118349429840177081232459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289491132573120236108309945 217118349429840177081232459)
        ·
          refine ⟨325677524144760265621848689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217118349429840177081232459 325677524144760265621848689)
          ·
            refine ⟨244258143108570199216386517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325677524144760265621848689 244258143108570199216386517)
            ·
              refine ⟨5724800229107114044134059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 244258143108570199216386517 5724800229107114044134059)
              ·
                refine ⟨8587200343660671066201089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5724800229107114044134059 8587200343660671066201089)
                ·
                  refine ⟨6440400257745503299650817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8587200343660671066201089 6440400257745503299650817)
                  ·
                    refine ⟨4830300193309127474738113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6440400257745503299650817 4830300193309127474738113)
                    ·
                      refine ⟨3622725144981845606053585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4830300193309127474738113 3622725144981845606053585)
                      ·
                        rfl

theorem cell23_7055232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 2, 2, 2].length) (baseStart_7055232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055232 prefixEnd_7055232 := by exact prefixLift 7055232
  have htrace : WordTrace (prefixWord ++ tailWord_7055232) baseStart_7055232 baseEnd_7055232 := by
    simpa [prefixWord, tailWord_7055232, baseEnd_7055232] using wordTrace_append hprefix tailTrace_7055232
  have hstable : (prefixWord ++ tailWord_7055232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055232).length < 2 ^ (prefixWord ++ tailWord_7055232).sum := by decide
  have hdescent : baseEnd_7055232 < baseStart_7055232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055255 : List Nat := [1, 1, 3, 3, 1, 5, 1, 3, 5]
def baseStart_7055255 : Nat := 118140960795 + 7055255 * 2 ^ 59
def prefixEnd_7055255 : Nat := 4983230072969 + 3 ^ 40 * 7055255 * 2
def baseEnd_7055255 : Nat := 402526328337433224007331

theorem tailTrace_7055255 : CollatzResearch.WordTrace tailWord_7055255 prefixEnd_7055255 402526328337433224007331 := by
  unfold tailWord_7055255
  simp only [CollatzResearch.WordTrace]
  refine ⟨257326290055023551468807219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171550860036682367645871479 257326290055023551468807219)
  ·
    refine ⟨385989435082535327203210829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257326290055023551468807219 385989435082535327203210829)
    ·
      refine ⟨144746038155950747701204061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385989435082535327203210829 144746038155950747701204061)
      ·
        refine ⟨54279764308481530387951523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144746038155950747701204061 54279764308481530387951523)
        ·
          refine ⟨81419646462722295581927285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54279764308481530387951523 81419646462722295581927285)
          ·
            refine ⟨7633091855880215210805683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81419646462722295581927285 7633091855880215210805683)
            ·
              refine ⟨11449637783820322816208525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7633091855880215210805683 11449637783820322816208525)
              ·
                refine ⟨4293614168932621056078197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11449637783820322816208525 4293614168932621056078197)
                ·
                  refine ⟨402526328337433224007331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4293614168932621056078197 402526328337433224007331)
                  ·
                    rfl

theorem cell23_7055255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 5].length) (baseStart_7055255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055255 prefixEnd_7055255 := by exact prefixLift 7055255
  have htrace : WordTrace (prefixWord ++ tailWord_7055255) baseStart_7055255 baseEnd_7055255 := by
    simpa [prefixWord, tailWord_7055255, baseEnd_7055255] using wordTrace_append hprefix tailTrace_7055255
  have hstable : (prefixWord ++ tailWord_7055255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055255).length < 2 ^ (prefixWord ++ tailWord_7055255).sum := by decide
  have hdescent : baseEnd_7055255 < baseStart_7055255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055268 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_7055268 : Nat := 118140960795 + 7055268 * 2 ^ 59
def prefixEnd_7055268 : Nat := 4983230072969 + 3 ^ 40 * 7055268 * 2
def baseEnd_7055268 : Nat := 1207581210095135821734473

theorem tailTrace_7055268 : CollatzResearch.WordTrace tailWord_7055268 prefixEnd_7055268 1207581210095135821734473 := by
  unfold tailWord_7055268
  simp only [CollatzResearch.WordTrace]
  refine ⟨128663382101988227344515229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171551176135984303126020305 128663382101988227344515229)
  ·
    refine ⟨48248768288245585254193211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128663382101988227344515229 48248768288245585254193211)
    ·
      refine ⟨72373152432368377881289817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48248768288245585254193211 72373152432368377881289817)
      ·
        refine ⟨54279864324276283410967363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72373152432368377881289817 54279864324276283410967363)
        ·
          refine ⟨81419796486414425116451045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54279864324276283410967363 81419796486414425116451045)
          ·
            refine ⟨15266211841202704709334571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81419796486414425116451045 15266211841202704709334571)
            ·
              refine ⟨22899317761804057064001857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15266211841202704709334571 22899317761804057064001857)
              ·
                refine ⟨17174488321353042798001393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22899317761804057064001857 17174488321353042798001393)
                ·
                  refine ⟨12880866241014782098501045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17174488321353042798001393 12880866241014782098501045)
                  ·
                    refine ⟨1207581210095135821734473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12880866241014782098501045 1207581210095135821734473)
                    ·
                      rfl

theorem cell23_7055268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_7055268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055268 prefixEnd_7055268 := by exact prefixLift 7055268
  have htrace : WordTrace (prefixWord ++ tailWord_7055268) baseStart_7055268 baseEnd_7055268 := by
    simpa [prefixWord, tailWord_7055268, baseEnd_7055268] using wordTrace_append hprefix tailTrace_7055268
  have hstable : (prefixWord ++ tailWord_7055268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055268).length < 2 ^ (prefixWord ++ tailWord_7055268).sum := by decide
  have hdescent : baseEnd_7055268 < baseStart_7055268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055272 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 7]
def baseStart_7055272 : Nat := 118140960795 + 7055272 * 2 ^ 59
def prefixEnd_7055272 : Nat := 4983230072969 + 3 ^ 40 * 7055272 * 2
def baseEnd_7055272 : Nat := 402527298245336161061489

theorem tailTrace_7055272 : CollatzResearch.WordTrace tailWord_7055272 prefixEnd_7055272 402527298245336161061489 := by
  unfold tailWord_7055272
  simp only [CollatzResearch.WordTrace]
  refine ⟨128663455047980981686088035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171551273397307975581450713 128663455047980981686088035)
  ·
    refine ⟨192995182571971472529132053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128663455047980981686088035 192995182571971472529132053)
    ·
      refine ⟨9046649183061162774803065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 192995182571971472529132053 9046649183061162774803065)
      ·
        refine ⟨6784986887295872081102299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9046649183061162774803065 6784986887295872081102299)
        ·
          refine ⟨10177480330943808121653449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6784986887295872081102299 10177480330943808121653449)
          ·
            refine ⟨7633110248207856091240087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10177480330943808121653449 7633110248207856091240087)
            ·
              refine ⟨11449665372311784136860131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7633110248207856091240087 11449665372311784136860131)
              ·
                refine ⟨17174498058467676205290197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11449665372311784136860131 17174498058467676205290197)
                ·
                  refine ⟨402527298245336161061489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17174498058467676205290197 402527298245336161061489)
                  ·
                    rfl

theorem cell23_7055272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 7].length) (baseStart_7055272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055272 prefixEnd_7055272 := by exact prefixLift 7055272
  have htrace : WordTrace (prefixWord ++ tailWord_7055272) baseStart_7055272 baseEnd_7055272 := by
    simpa [prefixWord, tailWord_7055272, baseEnd_7055272] using wordTrace_append hprefix tailTrace_7055272
  have hstable : (prefixWord ++ tailWord_7055272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055272).length < 2 ^ (prefixWord ++ tailWord_7055272).sum := by decide
  have hdescent : baseEnd_7055272 < baseStart_7055272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055288 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 1, 6, 2]
def baseStart_7055288 : Nat := 118140960795 + 7055288 * 2 ^ 59
def prefixEnd_7055288 : Nat := 4983230072969 + 3 ^ 40 * 7055288 * 2
def baseEnd_7055288 : Nat := 3622753899898497386953327

theorem tailTrace_7055288 : CollatzResearch.WordTrace tailWord_7055288 prefixEnd_7055288 3622753899898497386953327 := by
  unfold tailWord_7055288
  simp only [CollatzResearch.WordTrace]
  refine ⟨128663746831951999052379259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171551662442602665403172345 128663746831951999052379259)
  ·
    refine ⟨192995620247927998578568889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128663746831951999052379259 192995620247927998578568889)
    ·
      refine ⟨144746715185945998933926667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192995620247927998578568889 144746715185945998933926667)
      ·
        refine ⟨217120072778918998400890001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144746715185945998933926667 217120072778918998400890001)
        ·
          refine ⟨162840054584189248800667501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217120072778918998400890001 162840054584189248800667501)
          ·
            refine ⟨61065020469070968300250313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162840054584189248800667501 61065020469070968300250313)
            ·
              refine ⟨45798765351803226225187735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61065020469070968300250313 45798765351803226225187735)
              ·
                refine ⟨68698148027704839337781603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45798765351803226225187735 68698148027704839337781603)
                ·
                  refine ⟨103047222041557259006672405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68698148027704839337781603 103047222041557259006672405)
                  ·
                    refine ⟨4830338533197996515937769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103047222041557259006672405 4830338533197996515937769)
                    ·
                      refine ⟨3622753899898497386953327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4830338533197996515937769 3622753899898497386953327)
                      ·
                        rfl

theorem cell23_7055288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 6, 2].length) (baseStart_7055288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055288 prefixEnd_7055288 := by exact prefixLift 7055288
  have htrace : WordTrace (prefixWord ++ tailWord_7055288) baseStart_7055288 baseEnd_7055288 := by
    simpa [prefixWord, tailWord_7055288, baseEnd_7055288] using wordTrace_append hprefix tailTrace_7055288
  have hstable : (prefixWord ++ tailWord_7055288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055288).length < 2 ^ (prefixWord ++ tailWord_7055288).sum := by decide
  have hdescent : baseEnd_7055288 < baseStart_7055288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055365 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 1, 5, 2]
def baseStart_7055365 : Nat := 118140960795 + 7055365 * 2 ^ 59
def prefixEnd_7055365 : Nat := 4983230072969 + 3 ^ 40 * 7055365 * 2
def baseEnd_7055365 : Nat := 3622793437908893585690473

theorem tailTrace_7055365 : CollatzResearch.WordTrace tailWord_7055365 prefixEnd_7055365 3622793437908893585690473 := by
  unfold tailWord_7055365
  simp only [CollatzResearch.WordTrace]
  refine ⟨257330302084625040255311549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171553534723083360170207699 257330302084625040255311549)
  ·
    refine ⟨96498863281734390095741831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257330302084625040255311549 96498863281734390095741831)
    ·
      refine ⟨144748294922601585143612747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96498863281734390095741831 144748294922601585143612747)
      ·
        refine ⟨217122442383902377715419121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144748294922601585143612747 217122442383902377715419121)
        ·
          refine ⟨162841831787926783286564341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217122442383902377715419121 162841831787926783286564341)
          ·
            refine ⟨15266421730118135933115407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162841831787926783286564341 15266421730118135933115407)
            ·
              refine ⟨22899632595177203899673111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15266421730118135933115407 22899632595177203899673111)
              ·
                refine ⟨34349448892765805849509667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22899632595177203899673111 34349448892765805849509667)
                ·
                  refine ⟨51524173339148708774264501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34349448892765805849509667 51524173339148708774264501)
                  ·
                    refine ⟨4830391250545191447587297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51524173339148708774264501 4830391250545191447587297)
                    ·
                      refine ⟨3622793437908893585690473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4830391250545191447587297 3622793437908893585690473)
                      ·
                        rfl

theorem cell23_7055365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 5, 2].length) (baseStart_7055365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055365 prefixEnd_7055365 := by exact prefixLift 7055365
  have htrace : WordTrace (prefixWord ++ tailWord_7055365) baseStart_7055365 baseEnd_7055365 := by
    simpa [prefixWord, tailWord_7055365, baseEnd_7055365] using wordTrace_append hprefix tailTrace_7055365
  have hstable : (prefixWord ++ tailWord_7055365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055365).length < 2 ^ (prefixWord ++ tailWord_7055365).sum := by decide
  have hdescent : baseEnd_7055365 < baseStart_7055365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055389 : List Nat := [1, 4, 2, 2, 2, 1, 2, 4, 1, 1, 3]
def baseStart_7055389 : Nat := 118140960795 + 7055389 * 2 ^ 59
def prefixEnd_7055389 : Nat := 4983230072969 + 3 ^ 40 * 7055389 * 2
def baseEnd_7055389 : Nat := 3622805761444601491790363

theorem tailTrace_7055389 : CollatzResearch.WordTrace tailWord_7055389 prefixEnd_7055389 3622805761444601491790363 := by
  unfold tailWord_7055389
  simp only [CollatzResearch.WordTrace]
  refine ⟨257331177436538092354185221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171554118291025394902790147 257331177436538092354185221)
  ·
    refine ⟨48249595769350892316409729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257331177436538092354185221 48249595769350892316409729)
    ·
      refine ⟨36187196827013169237307297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48249595769350892316409729 36187196827013169237307297)
      ·
        refine ⟨27140397620259876927980473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36187196827013169237307297 27140397620259876927980473)
        ·
          refine ⟨20355298215194907695985355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27140397620259876927980473 20355298215194907695985355)
          ·
            refine ⟨30532947322792361543978033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20355298215194907695985355 30532947322792361543978033)
            ·
              refine ⟨22899710492094271157983525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30532947322792361543978033 22899710492094271157983525)
              ·
                refine ⟨4293695717267675842121911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22899710492094271157983525 4293695717267675842121911)
                ·
                  refine ⟨6440543575901513763182867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4293695717267675842121911 6440543575901513763182867)
                  ·
                    refine ⟨9660815363852270644774301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6440543575901513763182867 9660815363852270644774301)
                    ·
                      refine ⟨3622805761444601491790363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9660815363852270644774301 3622805761444601491790363)
                      ·
                        rfl

theorem cell23_7055389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_7055389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055389 prefixEnd_7055389 := by exact prefixLift 7055389
  have htrace : WordTrace (prefixWord ++ tailWord_7055389) baseStart_7055389 baseEnd_7055389 := by
    simpa [prefixWord, tailWord_7055389, baseEnd_7055389] using wordTrace_append hprefix tailTrace_7055389
  have hstable : (prefixWord ++ tailWord_7055389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055389).length < 2 ^ (prefixWord ++ tailWord_7055389).sum := by decide
  have hdescent : baseEnd_7055389 < baseStart_7055389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055408 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 6]
def baseStart_7055408 : Nat := 118140960795 + 7055408 * 2 ^ 59
def prefixEnd_7055408 : Nat := 4983230072969 + 3 ^ 40 * 7055408 * 2
def baseEnd_7055408 : Nat := 3622815517577036917452775

theorem tailTrace_7055408 : CollatzResearch.WordTrace tailWord_7055408 prefixEnd_7055408 3622815517577036917452775 := by
  unfold tailWord_7055408
  simp only [CollatzResearch.WordTrace]
  refine ⟨128665935211734629299563439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171554580282312839066084585 128665935211734629299563439)
  ·
    refine ⟨192998902817601943949345159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128665935211734629299563439 192998902817601943949345159)
    ·
      refine ⟨289498354226402915924017739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192998902817601943949345159 289498354226402915924017739)
      ·
        refine ⟨434247531339604373886026609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289498354226402915924017739 434247531339604373886026609)
        ·
          refine ⟨325685648504703280414519957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434247531339604373886026609 325685648504703280414519957)
          ·
            refine ⟨15266514773657966269430623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 325685648504703280414519957 15266514773657966269430623)
            ·
              refine ⟨22899772160486949404145935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15266514773657966269430623 22899772160486949404145935)
              ·
                refine ⟨34349658240730424106218903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22899772160486949404145935 34349658240730424106218903)
                ·
                  refine ⟨51524487361095636159328355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34349658240730424106218903 51524487361095636159328355)
                  ·
                    refine ⟨77286731041643454238992533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51524487361095636159328355 77286731041643454238992533)
                    ·
                      refine ⟨3622815517577036917452775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77286731041643454238992533 3622815517577036917452775)
                      ·
                        rfl

theorem cell23_7055408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_7055408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055408 prefixEnd_7055408 := by exact prefixLift 7055408
  have htrace : WordTrace (prefixWord ++ tailWord_7055408) baseStart_7055408 baseEnd_7055408 := by
    simpa [prefixWord, tailWord_7055408, baseEnd_7055408] using wordTrace_append hprefix tailTrace_7055408
  have hstable : (prefixWord ++ tailWord_7055408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055408).length < 2 ^ (prefixWord ++ tailWord_7055408).sum := by decide
  have hdescent : baseEnd_7055408 < baseStart_7055408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055415 : List Nat := [1, 1, 3, 1, 2, 2, 3, 4, 1, 2, 3]
def baseStart_7055415 : Nat := 118140960795 + 7055415 * 2 ^ 59
def prefixEnd_7055415 : Nat := 4983230072969 + 3 ^ 40 * 7055415 * 2
def baseEnd_7055415 : Nat := 3622819111941618390065243

theorem tailTrace_7055415 : CollatzResearch.WordTrace tailWord_7055415 prefixEnd_7055415 3622819111941618390065243 := by
  unfold tailWord_7055415
  simp only [CollatzResearch.WordTrace]
  refine ⟨257332125734443898794631699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171554750489629265863087799 257332125734443898794631699)
  ·
    refine ⟨385998188601665848191947549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257332125734443898794631699 385998188601665848191947549)
    ·
      refine ⟨144749320725624693071980331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385998188601665848191947549 144749320725624693071980331)
      ·
        refine ⟨217123981088437039607970497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144749320725624693071980331 217123981088437039607970497)
        ·
          refine ⟨162842985816327779705977873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217123981088437039607970497 162842985816327779705977873)
          ·
            refine ⟨122132239362245834779483405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162842985816327779705977873 122132239362245834779483405)
            ·
              refine ⟨45799589760842188042306277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122132239362245834779483405 45799589760842188042306277)
              ·
                refine ⟨8587423080157910257932427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45799589760842188042306277 8587423080157910257932427)
                ·
                  refine ⟨12881134620236865386898641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8587423080157910257932427 12881134620236865386898641)
                  ·
                    refine ⟨9660850965177649040173981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12881134620236865386898641 9660850965177649040173981)
                    ·
                      refine ⟨3622819111941618390065243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9660850965177649040173981 3622819111941618390065243)
                      ·
                        rfl

theorem cell23_7055415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_7055415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055415 prefixEnd_7055415 := by exact prefixLift 7055415
  have htrace : WordTrace (prefixWord ++ tailWord_7055415) baseStart_7055415 baseEnd_7055415 := by
    simpa [prefixWord, tailWord_7055415, baseEnd_7055415] using wordTrace_append hprefix tailTrace_7055415
  have hstable : (prefixWord ++ tailWord_7055415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055415).length < 2 ^ (prefixWord ++ tailWord_7055415).sum := by decide
  have hdescent : baseEnd_7055415 < baseStart_7055415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055466 : List Nat := [3, 1, 3, 2, 4, 1, 1, 2, 1, 2, 3]
def baseStart_7055466 : Nat := 118140960795 + 7055466 * 2 ^ 59
def prefixEnd_7055466 : Nat := 4983230072969 + 3 ^ 40 * 7055466 * 2
def baseEnd_7055466 : Nat := 3622845299454997690527509

theorem tailTrace_7055466 : CollatzResearch.WordTrace tailWord_7055466 prefixEnd_7055466 3622845299454997690527509 := by
  unfold tailWord_7055466
  simp only [CollatzResearch.WordTrace]
  refine ⟨64333496464314783626184563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171555990571506089669825501 64333496464314783626184563)
  ·
    refine ⟨96500244696472175439276845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64333496464314783626184563 96500244696472175439276845)
    ·
      refine ⟨36187591761177065789728817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96500244696472175439276845 36187591761177065789728817)
      ·
        refine ⟨27140693820882799342296613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36187591761177065789728817 27140693820882799342296613)
        ·
          refine ⟨5088880091415524876680615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27140693820882799342296613 5088880091415524876680615)
          ·
            refine ⟨7633320137123287315020923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5088880091415524876680615 7633320137123287315020923)
            ·
              refine ⟨11449980205684930972531385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7633320137123287315020923 11449980205684930972531385)
              ·
                refine ⟨8587485154263698229398539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11449980205684930972531385 8587485154263698229398539)
                ·
                  refine ⟨12881227731395547344097809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8587485154263698229398539 12881227731395547344097809)
                  ·
                    refine ⟨9660920798546660508073357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12881227731395547344097809 9660920798546660508073357)
                    ·
                      refine ⟨3622845299454997690527509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9660920798546660508073357 3622845299454997690527509)
                      ·
                        rfl

theorem cell23_7055466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_7055466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055466 prefixEnd_7055466 := by exact prefixLift 7055466
  have htrace : WordTrace (prefixWord ++ tailWord_7055466) baseStart_7055466 baseEnd_7055466 := by
    simpa [prefixWord, tailWord_7055466, baseEnd_7055466] using wordTrace_append hprefix tailTrace_7055466
  have hstable : (prefixWord ++ tailWord_7055466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055466).length < 2 ^ (prefixWord ++ tailWord_7055466).sum := by decide
  have hdescent : baseEnd_7055466 < baseStart_7055466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055472 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 3, 3, 2]
def baseStart_7055472 : Nat := 118140960795 + 7055472 * 2 ^ 59
def prefixEnd_7055472 : Nat := 4983230072969 + 3 ^ 40 * 7055472 * 2
def baseEnd_7055472 : Nat := 3622848380338924667052481

theorem tailTrace_7055472 : CollatzResearch.WordTrace tailWord_7055472 prefixEnd_7055472 3622848380338924667052481 := by
  unfold tailWord_7055472
  simp only [CollatzResearch.WordTrace]
  refine ⟨128667102347618698764728335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171556136463491598352971113 128667102347618698764728335)
  ·
    refine ⟨193000653521428048147092503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128667102347618698764728335 193000653521428048147092503)
    ·
      refine ⟨289500980282142072220638755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193000653521428048147092503 289500980282142072220638755)
      ·
        refine ⟨434251470423213108330958133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289500980282142072220638755 434251470423213108330958133)
        ·
          refine ⟨40711075352176228906027325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 434251470423213108330958133 40711075352176228906027325)
          ·
            refine ⟨15266653257066085839760247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40711075352176228906027325 15266653257066085839760247)
            ·
              refine ⟨22899979885599128759640371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15266653257066085839760247 22899979885599128759640371)
              ·
                refine ⟨34349969828398693139460557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22899979885599128759640371 34349969828398693139460557)
                ·
                  refine ⟨12881238685649509927297709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34349969828398693139460557 12881238685649509927297709)
                  ·
                    refine ⟨4830464507118566222736641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12881238685649509927297709 4830464507118566222736641)
                    ·
                      refine ⟨3622848380338924667052481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4830464507118566222736641 3622848380338924667052481)
                      ·
                        rfl

theorem cell23_7055472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 3, 3, 2].length) (baseStart_7055472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055472 prefixEnd_7055472 := by exact prefixLift 7055472
  have htrace : WordTrace (prefixWord ++ tailWord_7055472) baseStart_7055472 baseEnd_7055472 := by
    simpa [prefixWord, tailWord_7055472, baseEnd_7055472] using wordTrace_append hprefix tailTrace_7055472
  have hstable : (prefixWord ++ tailWord_7055472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055472).length < 2 ^ (prefixWord ++ tailWord_7055472).sum := by decide
  have hdescent : baseEnd_7055472 < baseStart_7055472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055519 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 1, 4, 2]
def baseStart_7055519 : Nat := 118140960795 + 7055519 * 2 ^ 59
def prefixEnd_7055519 : Nat := 4983230072969 + 3 ^ 40 * 7055519 * 2
def baseEnd_7055519 : Nat := 3622872513929685983164765

theorem tailTrace_7055519 : CollatzResearch.WordTrace tailWord_7055519 prefixEnd_7055519 3622872513929685983164765 := by
  unfold tailWord_7055519
  simp only [CollatzResearch.WordTrace]
  refine ⟨257335918926067124556417611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171557279284044749704278407 257335918926067124556417611)
  ·
    refine ⟨386003878389100686834626417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257335918926067124556417611 386003878389100686834626417)
    ·
      refine ⟨289502908791825515125969813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386003878389100686834626417 289502908791825515125969813)
      ·
        refine ⟨13570448849616821021529835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 289502908791825515125969813 13570448849616821021529835)
        ·
          refine ⟨20355673274425231532294753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13570448849616821021529835 20355673274425231532294753)
          ·
            refine ⟨15266754955818923649221065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20355673274425231532294753 15266754955818923649221065)
            ·
              refine ⟨11450066216864192736915799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15266754955818923649221065 11450066216864192736915799)
              ·
                refine ⟨17175099325296289105373699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11450066216864192736915799 17175099325296289105373699)
                ·
                  refine ⟨25762648987944433658060549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17175099325296289105373699 25762648987944433658060549)
                  ·
                    refine ⟨4830496685239581310886353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25762648987944433658060549 4830496685239581310886353)
                    ·
                      refine ⟨3622872513929685983164765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4830496685239581310886353 3622872513929685983164765)
                      ·
                        rfl

theorem cell23_7055519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_7055519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055519 prefixEnd_7055519 := by exact prefixLift 7055519
  have htrace : WordTrace (prefixWord ++ tailWord_7055519) baseStart_7055519 baseEnd_7055519 := by
    simpa [prefixWord, tailWord_7055519, baseEnd_7055519] using wordTrace_append hprefix tailTrace_7055519
  have hstable : (prefixWord ++ tailWord_7055519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055519).length < 2 ^ (prefixWord ++ tailWord_7055519).sum := by decide
  have hdescent : baseEnd_7055519 < baseStart_7055519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055540 : List Nat := [2, 5, 3, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_7055540 : Nat := 118140960795 + 7055540 * 2 ^ 59
def prefixEnd_7055540 : Nat := 4983230072969 + 3 ^ 40 * 7055540 * 2
def baseEnd_7055540 : Nat := 3622883297023430401002169

theorem tailTrace_7055540 : CollatzResearch.WordTrace tailWord_7055540 prefixEnd_7055540 3622883297023430401002169 := by
  unfold tailWord_7055540
  simp only [CollatzResearch.WordTrace]
  refine ⟨128668342429495522571466037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171557789905994030095288049 128668342429495522571466037)
  ·
    refine ⟨12062657102765205241074941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128668342429495522571466037 12062657102765205241074941)
    ·
      refine ⟨4523496413536951965403103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12062657102765205241074941 4523496413536951965403103)
      ·
        refine ⟨6785244620305427948104655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4523496413536951965403103 6785244620305427948104655)
        ·
          refine ⟨10177866930458141922156983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6785244620305427948104655 10177866930458141922156983)
          ·
            refine ⟨15266800395687212883235475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10177866930458141922156983 15266800395687212883235475)
            ·
              refine ⟨22900200593530819324853213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15266800395687212883235475 22900200593530819324853213)
              ·
                refine ⟨8587575222574057246819955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22900200593530819324853213 8587575222574057246819955)
                ·
                  refine ⟨12881362833861085870229933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8587575222574057246819955 12881362833861085870229933)
                  ·
                    refine ⟨4830511062697907201336225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12881362833861085870229933 4830511062697907201336225)
                    ·
                      refine ⟨3622883297023430401002169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4830511062697907201336225 3622883297023430401002169)
                      ·
                        rfl

theorem cell23_7055540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_7055540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055540 prefixEnd_7055540 := by exact prefixLift 7055540
  have htrace : WordTrace (prefixWord ++ tailWord_7055540) baseStart_7055540 baseEnd_7055540 := by
    simpa [prefixWord, tailWord_7055540, baseEnd_7055540] using wordTrace_append hprefix tailTrace_7055540
  have hstable : (prefixWord ++ tailWord_7055540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055540).length < 2 ^ (prefixWord ++ tailWord_7055540).sum := by decide
  have hdescent : baseEnd_7055540 < baseStart_7055540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055595 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 3]
def baseStart_7055595 : Nat := 118140960795 + 7055595 * 2 ^ 59
def prefixEnd_7055595 : Nat := 4983230072969 + 3 ^ 40 * 7055595 * 2
def baseEnd_7055595 : Nat := 3622911538459427685814415

theorem tailTrace_7055595 : CollatzResearch.WordTrace tailWord_7055595 prefixEnd_7055595 3622911538459427685814415 := by
  unfold tailWord_7055595
  simp only [CollatzResearch.WordTrace]
  refine ⟨257338690873791789536184239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171559127249194526357456159 257338690873791789536184239)
  ·
    refine ⟨386008036310687684304276359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257338690873791789536184239 386008036310687684304276359)
    ·
      refine ⟨579012054466031526456414539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386008036310687684304276359 579012054466031526456414539)
      ·
        refine ⟨868518081699047289684621809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579012054466031526456414539 868518081699047289684621809)
        ·
          refine ⟨651388561274285467263466357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 868518081699047289684621809 651388561274285467263466357)
          ·
            refine ⟨61067677619464262555949971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 651388561274285467263466357 61067677619464262555949971)
            ·
              refine ⟨91601516429196393833924957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61067677619464262555949971 91601516429196393833924957)
              ·
                refine ⟨34350568660948647687721859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91601516429196393833924957 34350568660948647687721859)
                ·
                  refine ⟨51525852991422971531582789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34350568660948647687721859 51525852991422971531582789)
                  ·
                    refine ⟨9661097435891807162171773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51525852991422971531582789 9661097435891807162171773)
                    ·
                      refine ⟨3622911538459427685814415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9661097435891807162171773 3622911538459427685814415)
                      ·
                        rfl

theorem cell23_7055595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 3].length) (baseStart_7055595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055595 prefixEnd_7055595 := by exact prefixLift 7055595
  have htrace : WordTrace (prefixWord ++ tailWord_7055595) baseStart_7055595 baseEnd_7055595 := by
    simpa [prefixWord, tailWord_7055595, baseEnd_7055595] using wordTrace_append hprefix tailTrace_7055595
  have hstable : (prefixWord ++ tailWord_7055595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055595).length < 2 ^ (prefixWord ++ tailWord_7055595).sum := by decide
  have hdescent : baseEnd_7055595 < baseStart_7055595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055612 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 4, 2, 3]
def baseStart_7055612 : Nat := 118140960795 + 7055612 * 2 ^ 59
def prefixEnd_7055612 : Nat := 4983230072969 + 3 ^ 40 * 7055612 * 2
def baseEnd_7055612 : Nat := 3622920267630554119301837

theorem tailTrace_7055612 : CollatzResearch.WordTrace tailWord_7055612 prefixEnd_7055612 3622920267630554119301837 := by
  unfold tailWord_7055612
  simp only [CollatzResearch.WordTrace]
  refine ⟨128669655457365100719776545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171559540609820134293035393 128669655457365100719776545)
  ·
    refine ⟨96502241593023825539832409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128669655457365100719776545 96502241593023825539832409)
    ·
      refine ⟨72376681194767869154874307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96502241593023825539832409 72376681194767869154874307)
      ·
        refine ⟨108565021792151803732311461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72376681194767869154874307 108565021792151803732311461)
        ·
          refine ⟨20355941586028463199808399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108565021792151803732311461 20355941586028463199808399)
          ·
            refine ⟨30533912379042694799712599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20355941586028463199808399 30533912379042694799712599)
            ·
              refine ⟨45800868568564042199568899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30533912379042694799712599 45800868568564042199568899)
              ·
                refine ⟨68701302852846063299353349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45800868568564042199568899 68701302852846063299353349)
                ·
                  refine ⟨12881494284908636868628753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68701302852846063299353349 12881494284908636868628753)
                  ·
                    refine ⟨9661120713681477651471565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12881494284908636868628753 9661120713681477651471565)
                    ·
                      refine ⟨3622920267630554119301837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9661120713681477651471565 3622920267630554119301837)
                      ·
                        rfl

theorem cell23_7055612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_7055612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055612 prefixEnd_7055612 := by exact prefixLift 7055612
  have htrace : WordTrace (prefixWord ++ tailWord_7055612) baseStart_7055612 baseEnd_7055612 := by
    simpa [prefixWord, tailWord_7055612, baseEnd_7055612] using wordTrace_append hprefix tailTrace_7055612
  have hstable : (prefixWord ++ tailWord_7055612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055612).length < 2 ^ (prefixWord ++ tailWord_7055612).sum := by decide
  have hdescent : baseEnd_7055612 < baseStart_7055612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055615 : List Nat := [1, 1, 2, 2, 1, 4, 2, 4, 6]
def baseStart_7055615 : Nat := 118140960795 + 7055615 * 2 ^ 59
def prefixEnd_7055615 : Nat := 4983230072969 + 3 ^ 40 * 7055615 * 2
def baseEnd_7055615 : Nat := 402546867563613067507147

theorem tailTrace_7055615 : CollatzResearch.WordTrace tailWord_7055615 prefixEnd_7055615 402546867563613067507147 := by
  unfold tailWord_7055615
  simp only [CollatzResearch.WordTrace]
  refine ⟨257339420333719332951912299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171559613555812888634608199 257339420333719332951912299)
  ·
    refine ⟨386009130500578999427868449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257339420333719332951912299 386009130500578999427868449)
    ·
      refine ⟨289506847875434249570901337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386009130500578999427868449 289506847875434249570901337)
      ·
        refine ⟨217130135906575687178176003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289506847875434249570901337 217130135906575687178176003)
        ·
          refine ⟨325695203859863530767264005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217130135906575687178176003 325695203859863530767264005)
          ·
            refine ⟨61067850723724412018862001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 325695203859863530767264005 61067850723724412018862001)
            ·
              refine ⟨45800888042793309014146501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61067850723724412018862001 45800888042793309014146501)
              ·
                refine ⟨8587666508023745440152469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45800888042793309014146501 8587666508023745440152469)
                ·
                  refine ⟨402546867563613067507147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8587666508023745440152469 402546867563613067507147)
                  ·
                    rfl

theorem cell23_7055615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 6].length) (baseStart_7055615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055615 prefixEnd_7055615 := by exact prefixLift 7055615
  have htrace : WordTrace (prefixWord ++ tailWord_7055615) baseStart_7055615 baseEnd_7055615 := by
    simpa [prefixWord, tailWord_7055615, baseEnd_7055615] using wordTrace_append hprefix tailTrace_7055615
  have hstable : (prefixWord ++ tailWord_7055615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055615).length < 2 ^ (prefixWord ++ tailWord_7055615).sum := by decide
  have hdescent : baseEnd_7055615 < baseStart_7055615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055646 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_7055646 : Nat := 118140960795 + 7055646 * 2 ^ 59
def prefixEnd_7055646 : Nat := 4983230072969 + 3 ^ 40 * 7055646 * 2
def baseEnd_7055646 : Nat := 3622937725972806986276681

theorem tailTrace_7055646 : CollatzResearch.WordTrace tailWord_7055646 prefixEnd_7055646 3622937725972806986276681 := by
  unfold tailWord_7055646
  simp only [CollatzResearch.WordTrace]
  refine ⟨32167568874575878155786349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171560367331071350164193861 32167568874575878155786349)
  ·
    refine ⟨12062838327965954308419881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32167568874575878155786349 12062838327965954308419881)
    ·
      refine ⟨9047128745974465731314911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12062838327965954308419881 9047128745974465731314911)
      ·
        refine ⟨13570693118961698596972367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9047128745974465731314911 13570693118961698596972367)
        ·
          refine ⟨20356039678442547895458551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13570693118961698596972367 20356039678442547895458551)
          ·
            refine ⟨30534059517663821843187827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20356039678442547895458551 30534059517663821843187827)
            ·
              refine ⟨45801089276495732764781741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30534059517663821843187827 45801089276495732764781741)
              ·
                refine ⟨17175408478685899786793153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45801089276495732764781741 17175408478685899786793153)
                ·
                  refine ⟨12881556359014424840094865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17175408478685899786793153 12881556359014424840094865)
                  ·
                    refine ⟨9661167269260818630071149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12881556359014424840094865 9661167269260818630071149)
                    ·
                      refine ⟨3622937725972806986276681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9661167269260818630071149 3622937725972806986276681)
                      ·
                        rfl

theorem cell23_7055646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_7055646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055646 prefixEnd_7055646 := by exact prefixLift 7055646
  have htrace : WordTrace (prefixWord ++ tailWord_7055646) baseStart_7055646 baseEnd_7055646 := by
    simpa [prefixWord, tailWord_7055646, baseEnd_7055646] using wordTrace_append hprefix tailTrace_7055646
  have hstable : (prefixWord ++ tailWord_7055646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055646).length < 2 ^ (prefixWord ++ tailWord_7055646).sum := by decide
  have hdescent : baseEnd_7055646 < baseStart_7055646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055669 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 2, 3, 2]
def baseStart_7055669 : Nat := 118140960795 + 7055669 * 2 ^ 59
def prefixEnd_7055669 : Nat := 4983230072969 + 3 ^ 40 * 7055669 * 2
def baseEnd_7055669 : Nat := 3622949536027860396289075

theorem tailTrace_7055669 : CollatzResearch.WordTrace tailWord_7055669 prefixEnd_7055669 3622949536027860396289075 := by
  unfold tailWord_7055669
  simp only [CollatzResearch.WordTrace]
  refine ⟨257341389875523700174378061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171560926583682466782918707 257341389875523700174378061)
  ·
    refine ⟨96503021203321387565391773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257341389875523700174378061 96503021203321387565391773)
    ·
      refine ⟨36188632951245520337021915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96503021203321387565391773 36188632951245520337021915)
      ·
        refine ⟨54282949426868280505532873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36188632951245520337021915 54282949426868280505532873)
        ·
          refine ⟨40712212070151210379149655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54282949426868280505532873 40712212070151210379149655)
          ·
            refine ⟨61068318105226815568724483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40712212070151210379149655 61068318105226815568724483)
            ·
              refine ⟨91602477157840223353086725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61068318105226815568724483 91602477157840223353086725)
              ·
                refine ⟨17175464467095041878703761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91602477157840223353086725 17175464467095041878703761)
                ·
                  refine ⟨12881598350321281409027821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17175464467095041878703761 12881598350321281409027821)
                  ·
                    refine ⟨4830599381370480528385433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12881598350321281409027821 4830599381370480528385433)
                    ·
                      refine ⟨3622949536027860396289075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4830599381370480528385433 3622949536027860396289075)
                      ·
                        rfl

theorem cell23_7055669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_7055669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055669 prefixEnd_7055669 := by exact prefixLift 7055669
  have htrace : WordTrace (prefixWord ++ tailWord_7055669) baseStart_7055669 baseEnd_7055669 := by
    simpa [prefixWord, tailWord_7055669, baseEnd_7055669] using wordTrace_append hprefix tailTrace_7055669
  have hstable : (prefixWord ++ tailWord_7055669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055669).length < 2 ^ (prefixWord ++ tailWord_7055669).sum := by decide
  have hdescent : baseEnd_7055669 < baseStart_7055669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055676 : List Nat := [2, 2, 2, 2, 1, 2, 3, 4, 1, 1, 3]
def baseStart_7055676 : Nat := 118140960795 + 7055676 * 2 ^ 59
def prefixEnd_7055676 : Nat := 4983230072969 + 3 ^ 40 * 7055676 * 2
def baseEnd_7055676 : Nat := 3622953130392441868901543

theorem tailTrace_7055676 : CollatzResearch.WordTrace tailWord_7055676 prefixEnd_7055676 3622953130392441868901543 := by
  unfold tailWord_7055676
  simp only [CollatzResearch.WordTrace]
  refine ⟨128670822593249170184941441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171561096790998893579921921 128670822593249170184941441)
  ·
    refine ⟨96503116944936877638706081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128670822593249170184941441 96503116944936877638706081)
    ·
      refine ⟨72377337708702658229029561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96503116944936877638706081 72377337708702658229029561)
      ·
        refine ⟨54283003281526993671772171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72377337708702658229029561 54283003281526993671772171)
        ·
          refine ⟨81424504922290490507658257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54283003281526993671772171 81424504922290490507658257)
          ·
            refine ⟨61068378691717867880743693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81424504922290490507658257 61068378691717867880743693)
            ·
              refine ⟨22900642009394200455278885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61068378691717867880743693 22900642009394200455278885)
              ·
                refine ⟨4293870376761412585364791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22900642009394200455278885 4293870376761412585364791)
                ·
                  refine ⟨6440805565142118878047187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4293870376761412585364791 6440805565142118878047187)
                  ·
                    refine ⟨9661208347713178317070781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6440805565142118878047187 9661208347713178317070781)
                    ·
                      refine ⟨3622953130392441868901543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9661208347713178317070781 3622953130392441868901543)
                      ·
                        rfl

theorem cell23_7055676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_7055676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055676 prefixEnd_7055676 := by exact prefixLift 7055676
  have htrace : WordTrace (prefixWord ++ tailWord_7055676) baseStart_7055676 baseEnd_7055676 := by
    simpa [prefixWord, tailWord_7055676, baseEnd_7055676] using wordTrace_append hprefix tailTrace_7055676
  have hstable : (prefixWord ++ tailWord_7055676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055676).length < 2 ^ (prefixWord ++ tailWord_7055676).sum := by decide
  have hdescent : baseEnd_7055676 < baseStart_7055676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055692 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 1, 6]
def baseStart_7055692 : Nat := 118140960795 + 7055692 * 2 ^ 59
def prefixEnd_7055692 : Nat := 4983230072969 + 3 ^ 40 * 7055692 * 2
def baseEnd_7055692 : Nat := 1207653782027637935433823

theorem tailTrace_7055692 : CollatzResearch.WordTrace tailWord_7055692 prefixEnd_7055692 1207653782027637935433823 := by
  unfold tailWord_7055692
  simp only [CollatzResearch.WordTrace]
  refine ⟨128671114377220187551232665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171561485836293583401643553 128671114377220187551232665)
  ·
    refine ⟨96503335782915140663424499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128671114377220187551232665 96503335782915140663424499)
    ·
      refine ⟨144755003674372710995136749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96503335782915140663424499 144755003674372710995136749)
      ·
        refine ⟨54283126377889766623176281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144755003674372710995136749 54283126377889766623176281)
        ·
          refine ⟨40712344783417324967382211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54283126377889766623176281 40712344783417324967382211)
          ·
            refine ⟨61068517175125987451073317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40712344783417324967382211 61068517175125987451073317)
            ·
              refine ⟨11450346970336122647076247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61068517175125987451073317 11450346970336122647076247)
              ·
                refine ⟨17175520455504183970614371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11450346970336122647076247 17175520455504183970614371)
                ·
                  refine ⟨25763280683256275955921557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17175520455504183970614371 25763280683256275955921557)
                  ·
                    refine ⟨1207653782027637935433823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25763280683256275955921557 1207653782027637935433823)
                    ·
                      rfl

theorem cell23_7055692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_7055692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055692 prefixEnd_7055692 := by exact prefixLift 7055692
  have htrace : WordTrace (prefixWord ++ tailWord_7055692) baseStart_7055692 baseEnd_7055692 := by
    simpa [prefixWord, tailWord_7055692, baseEnd_7055692] using wordTrace_append hprefix tailTrace_7055692
  have hstable : (prefixWord ++ tailWord_7055692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055692).length < 2 ^ (prefixWord ++ tailWord_7055692).sum := by decide
  have hdescent : baseEnd_7055692 < baseStart_7055692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055722 : List Nat := [3, 1, 3, 3, 1, 2, 10]
def baseStart_7055722 : Nat := 118140960795 + 7055722 * 2 ^ 59
def prefixEnd_7055722 : Nat := 4983230072969 + 3 ^ 40 * 7055722 * 2
def baseEnd_7055722 : Nat := 44728108030895662826251

theorem tailTrace_7055722 : CollatzResearch.WordTrace tailWord_7055722 prefixEnd_7055722 44728108030895662826251 := by
  unfold tailWord_7055722
  simp only [CollatzResearch.WordTrace]
  refine ⟨64335830736082922556514355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171562215296221126817371613 64335830736082922556514355)
  ·
    refine ⟨96503746104124383834771533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64335830736082922556514355 96503746104124383834771533)
    ·
      refine ⟨36188904789046643938039325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96503746104124383834771533 36188904789046643938039325)
      ·
        refine ⟨13570839295892491476764747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36188904789046643938039325 13570839295892491476764747)
        ·
          refine ⟨20356258943838737215147121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13570839295892491476764747 20356258943838737215147121)
          ·
            refine ⟨15267194207879052911360341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20356258943838737215147121 15267194207879052911360341)
            ·
              refine ⟨44728108030895662826251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15267194207879052911360341 44728108030895662826251)
              ·
                rfl

theorem cell23_7055722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 10].length) (baseStart_7055722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055722 prefixEnd_7055722 := by exact prefixLift 7055722
  have htrace : WordTrace (prefixWord ++ tailWord_7055722) baseStart_7055722 baseEnd_7055722 := by
    simpa [prefixWord, tailWord_7055722, baseEnd_7055722] using wordTrace_append hprefix tailTrace_7055722
  have hstable : (prefixWord ++ tailWord_7055722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055722).length < 2 ^ (prefixWord ++ tailWord_7055722).sum := by decide
  have hdescent : baseEnd_7055722 < baseStart_7055722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055733 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_7055733 : Nat := 118140960795 + 7055733 * 2 ^ 59
def prefixEnd_7055733 : Nat := 4983230072969 + 3 ^ 40 * 7055733 * 2
def baseEnd_7055733 : Nat := 3622982398789748145888781

theorem tailTrace_7055733 : CollatzResearch.WordTrace tailWord_7055733 prefixEnd_7055733 3622982398789748145888781 := by
  unfold tailWord_7055733
  simp only [CollatzResearch.WordTrace]
  refine ⟨257343724147291839104707853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171562482764861226069805235 257343724147291839104707853)
  ·
    refine ⟨96503896555234439664265445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257343724147291839104707853 96503896555234439664265445)
    ·
      refine ⟨18094480604106457437049771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96503896555234439664265445 18094480604106457437049771)
      ·
        refine ⟨27141720906159686155574657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18094480604106457437049771 27141720906159686155574657)
        ·
          refine ⟨20356290679619764616680993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27141720906159686155574657 20356290679619764616680993)
          ·
            refine ⟨15267218009714823462510745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20356290679619764616680993 15267218009714823462510745)
            ·
              refine ⟨11450413507286117596883059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15267218009714823462510745 11450413507286117596883059)
              ·
                refine ⟨17175620260929176395324589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11450413507286117596883059 17175620260929176395324589)
                ·
                  refine ⟨6440857597848441148246721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17175620260929176395324589 6440857597848441148246721)
                  ·
                    refine ⟨4830643198386330861185041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6440857597848441148246721 4830643198386330861185041)
                    ·
                      refine ⟨3622982398789748145888781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4830643198386330861185041 3622982398789748145888781)
                      ·
                        rfl

theorem cell23_7055733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_7055733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055733 prefixEnd_7055733 := by exact prefixLift 7055733
  have htrace : WordTrace (prefixWord ++ tailWord_7055733) baseStart_7055733 baseEnd_7055733 := by
    simpa [prefixWord, tailWord_7055733, baseEnd_7055733] using wordTrace_append hprefix tailTrace_7055733
  have hstable : (prefixWord ++ tailWord_7055733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055733).length < 2 ^ (prefixWord ++ tailWord_7055733).sum := by decide
  have hdescent : baseEnd_7055733 < baseStart_7055733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055735 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 2, 7]
def baseStart_7055735 : Nat := 118140960795 + 7055735 * 2 ^ 59
def prefixEnd_7055735 : Nat := 4983230072969 + 3 ^ 40 * 7055735 * 2
def baseEnd_7055735 : Nat := 1207661141917019046021257

theorem tailTrace_7055735 : CollatzResearch.WordTrace tailWord_7055735 prefixEnd_7055735 1207661141917019046021257 := by
  unfold tailWord_7055735
  simp only [CollatzResearch.WordTrace]
  refine ⟨257343797093284593446280659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171562531395523062297520439 257343797093284593446280659)
  ·
    refine ⟨386015695639926890169420989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257343797093284593446280659 386015695639926890169420989)
    ·
      refine ⟨144755885864972583813532871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386015695639926890169420989 144755885864972583813532871)
      ·
        refine ⟨217133828797458875720299307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144755885864972583813532871 217133828797458875720299307)
        ·
          refine ⟨325700743196188313580448961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217133828797458875720299307 325700743196188313580448961)
          ·
            refine ⟨244275557397141235185336721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325700743196188313580448961 244275557397141235185336721)
            ·
              refine ⟨183206668047855926389002541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244275557397141235185336721 183206668047855926389002541)
              ·
                refine ⟨68702500517945972395875953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183206668047855926389002541 68702500517945972395875953)
                ·
                  refine ⟨51526875388459479296906965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68702500517945972395875953 51526875388459479296906965)
                  ·
                    refine ⟨1207661141917019046021257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51526875388459479296906965 1207661141917019046021257)
                    ·
                      rfl

theorem cell23_7055735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_7055735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055735 prefixEnd_7055735 := by exact prefixLift 7055735
  have htrace : WordTrace (prefixWord ++ tailWord_7055735) baseStart_7055735 baseEnd_7055735 := by
    simpa [prefixWord, tailWord_7055735, baseEnd_7055735] using wordTrace_append hprefix tailTrace_7055735
  have hstable : (prefixWord ++ tailWord_7055735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055735).length < 2 ^ (prefixWord ++ tailWord_7055735).sum := by decide
  have hdescent : baseEnd_7055735 < baseStart_7055735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055746 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_7055746 : Nat := 118140960795 + 7055746 * 2 ^ 59
def prefixEnd_7055746 : Nat := 4983230072969 + 3 ^ 40 * 7055746 * 2
def baseEnd_7055746 : Nat := 3622989074038256595026221

theorem tailTrace_7055746 : CollatzResearch.WordTrace tailWord_7055746 prefixEnd_7055746 3622989074038256595026221 := by
  unfold tailWord_7055746
  simp only [CollatzResearch.WordTrace]
  refine ⟨64336049574061185581232773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171562798864163161549954061 64336049574061185581232773)
  ·
    refine ⟨12063009295136472296481145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64336049574061185581232773 12063009295136472296481145)
    ·
      refine ⟨9047256971352354222360859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12063009295136472296481145 9047256971352354222360859)
      ·
        refine ⟨13570885457028531333541289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9047256971352354222360859 13570885457028531333541289)
        ·
          refine ⟨10178164092771398500155967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13570885457028531333541289 10178164092771398500155967)
          ·
            refine ⟨15267246139157097750233951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10178164092771398500155967 15267246139157097750233951)
            ·
              refine ⟨22900869208735646625350927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15267246139157097750233951 22900869208735646625350927)
              ·
                refine ⟨34351303813103469938026391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22900869208735646625350927 34351303813103469938026391)
                ·
                  refine ⟨51526955719655204907039587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34351303813103469938026391 51526955719655204907039587)
                  ·
                    refine ⟨77290433579482807360559381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51526955719655204907039587 77290433579482807360559381)
                    ·
                      refine ⟨3622989074038256595026221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77290433579482807360559381 3622989074038256595026221)
                      ·
                        rfl

theorem cell23_7055746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_7055746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055746 prefixEnd_7055746 := by exact prefixLift 7055746
  have htrace : WordTrace (prefixWord ++ tailWord_7055746) baseStart_7055746 baseEnd_7055746 := by
    simpa [prefixWord, tailWord_7055746, baseEnd_7055746] using wordTrace_append hprefix tailTrace_7055746
  have hstable : (prefixWord ++ tailWord_7055746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055746).length < 2 ^ (prefixWord ++ tailWord_7055746).sum := by decide
  have hdescent : baseEnd_7055746 < baseStart_7055746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055776 : List Nat := [2, 1, 1, 4, 1, 3, 2, 3, 1, 3, 2]
def baseStart_7055776 : Nat := 118140960795 + 7055776 * 2 ^ 59
def prefixEnd_7055776 : Nat := 4983230072969 + 3 ^ 40 * 7055776 * 2
def baseEnd_7055776 : Nat := 3623004478457891477651083

theorem tailTrace_7055776 : CollatzResearch.WordTrace tailWord_7055776 prefixEnd_7055776 3623004478457891477651083 := by
  unfold tailWord_7055776
  simp only [CollatzResearch.WordTrace]
  refine ⟨128672646243068028724261591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171563528324090704965682121 128672646243068028724261591)
  ·
    refine ⟨193008969364602043086392387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128672646243068028724261591 193008969364602043086392387)
    ·
      refine ⟨289513454046903064629588581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193008969364602043086392387 289513454046903064629588581)
      ·
        refine ⟨54283772633794324618047859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289513454046903064629588581 54283772633794324618047859)
        ·
          refine ⟨81425658950691486927071789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54283772633794324618047859 81425658950691486927071789)
          ·
            refine ⟨30534622106509307597651921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81425658950691486927071789 30534622106509307597651921)
            ·
              refine ⟨22900966579881980698238941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30534622106509307597651921 22900966579881980698238941)
              ·
                refine ⟨8587862467455742761839603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22900966579881980698238941 8587862467455742761839603)
                ·
                  refine ⟨12881793701183614142759405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8587862467455742761839603 12881793701183614142759405)
                  ·
                    refine ⟨4830672637943855303534777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12881793701183614142759405 4830672637943855303534777)
                    ·
                      refine ⟨3623004478457891477651083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4830672637943855303534777 3623004478457891477651083)
                      ·
                        rfl

theorem cell23_7055776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_7055776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055776 prefixEnd_7055776 := by exact prefixLift 7055776
  have htrace : WordTrace (prefixWord ++ tailWord_7055776) baseStart_7055776 baseEnd_7055776 := by
    simpa [prefixWord, tailWord_7055776, baseEnd_7055776] using wordTrace_append hprefix tailTrace_7055776
  have hstable : (prefixWord ++ tailWord_7055776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055776).length < 2 ^ (prefixWord ++ tailWord_7055776).sum := by decide
  have hdescent : baseEnd_7055776 < baseStart_7055776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055802 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4]
def baseStart_7055802 : Nat := 118140960795 + 7055802 * 2 ^ 59
def prefixEnd_7055802 : Nat := 4983230072969 + 3 ^ 40 * 7055802 * 2
def baseEnd_7055802 : Nat := 3623017828954908375925963

theorem tailTrace_7055802 : CollatzResearch.WordTrace tailWord_7055802 prefixEnd_7055802 3623017828954908375925963 := by
  unfold tailWord_7055802
  simp only [CollatzResearch.WordTrace]
  refine ⟨64336560196010465972242415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171564160522694575925979773 64336560196010465972242415)
  ·
    refine ⟨96504840294015698958363623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64336560196010465972242415 96504840294015698958363623)
    ·
      refine ⟨144757260441023548437545435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96504840294015698958363623 144757260441023548437545435)
      ·
        refine ⟨217135890661535322656318153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144757260441023548437545435 217135890661535322656318153)
        ·
          refine ⟨162851917996151491992238615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217135890661535322656318153 162851917996151491992238615)
          ·
            refine ⟨244277876994227237988357923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162851917996151491992238615 244277876994227237988357923)
            ·
              refine ⟨366416815491340856982536885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244277876994227237988357923 366416815491340856982536885)
              ·
                refine ⟨34351576452313205342112833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 366416815491340856982536885 34351576452313205342112833)
                ·
                  refine ⟨25763682339234904006584625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34351576452313205342112833 25763682339234904006584625)
                  ·
                    refine ⟨19322761754426178004938469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25763682339234904006584625 19322761754426178004938469)
                    ·
                      refine ⟨3623017828954908375925963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19322761754426178004938469 3623017828954908375925963)
                      ·
                        rfl

theorem cell23_7055802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_7055802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055802 prefixEnd_7055802 := by exact prefixLift 7055802
  have htrace : WordTrace (prefixWord ++ tailWord_7055802) baseStart_7055802 baseEnd_7055802 := by
    simpa [prefixWord, tailWord_7055802, baseEnd_7055802] using wordTrace_append hprefix tailTrace_7055802
  have hstable : (prefixWord ++ tailWord_7055802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055802).length < 2 ^ (prefixWord ++ tailWord_7055802).sum := by decide
  have hdescent : baseEnd_7055802 < baseStart_7055802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055852 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 5]
def baseStart_7055852 : Nat := 118140960795 + 7055852 * 2 ^ 59
def prefixEnd_7055852 : Nat := 4983230072969 + 3 ^ 40 * 7055852 * 2
def baseEnd_7055852 : Nat := 3623043502987633180300733

theorem tailTrace_7055852 : CollatzResearch.WordTrace tailWord_7055852 prefixEnd_7055852 3623043502987633180300733 := by
  unfold tailWord_7055852
  simp only [CollatzResearch.WordTrace]
  refine ⟨128674032216930361214144905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171565376289240481618859873 128674032216930361214144905)
  ·
    refine ⟨96505524162697770910608679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128674032216930361214144905 96505524162697770910608679)
    ·
      refine ⟨144758286244046656365913019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96505524162697770910608679 144758286244046656365913019)
      ·
        refine ⟨217137429366069984548869529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144758286244046656365913019 217137429366069984548869529)
        ·
          refine ⟨162853072024552488411652147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217137429366069984548869529 162853072024552488411652147)
          ·
            refine ⟨244279608036828732617478221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162853072024552488411652147 244279608036828732617478221)
            ·
              refine ⟨91604853013810774731554333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244279608036828732617478221 91604853013810774731554333)
              ·
                refine ⟨34351819880179040524332875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91604853013810774731554333 34351819880179040524332875)
                ·
                  refine ⟨51527729820268560786499313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34351819880179040524332875 51527729820268560786499313)
                  ·
                    refine ⟨38645797365201420589874485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51527729820268560786499313 38645797365201420589874485)
                    ·
                      refine ⟨3623043502987633180300733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38645797365201420589874485 3623043502987633180300733)
                      ·
                        rfl

theorem cell23_7055852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_7055852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055852 prefixEnd_7055852 := by exact prefixLift 7055852
  have htrace : WordTrace (prefixWord ++ tailWord_7055852) baseStart_7055852 baseEnd_7055852 := by
    simpa [prefixWord, tailWord_7055852, baseEnd_7055852] using wordTrace_append hprefix tailTrace_7055852
  have hstable : (prefixWord ++ tailWord_7055852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055852).length < 2 ^ (prefixWord ++ tailWord_7055852).sum := by decide
  have hdescent : baseEnd_7055852 < baseStart_7055852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055876 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 2, 5]
def baseStart_7055876 : Nat := 118140960795 + 7055876 * 2 ^ 59
def prefixEnd_7055876 : Nat := 4983230072969 + 3 ^ 40 * 7055876 * 2
def baseEnd_7055876 : Nat := 1207685275507780362133541

theorem tailTrace_7055876 : CollatzResearch.WordTrace tailWord_7055876 prefixEnd_7055876 1207685275507780362133541 := by
  unfold tailWord_7055876
  simp only [CollatzResearch.WordTrace]
  refine ⟨128674469892886887263581741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171565959857182516351442321 128674469892886887263581741)
  ·
    refine ⟨48252926209832582723843153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128674469892886887263581741 48252926209832582723843153)
    ·
      refine ⟨36189694657374437042882365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48252926209832582723843153 36189694657374437042882365)
      ·
        refine ⟨13571135496515413891080887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36189694657374437042882365 13571135496515413891080887)
        ·
          refine ⟨20356703244773120836621331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13571135496515413891080887 20356703244773120836621331)
          ·
            refine ⟨30535054867159681254931997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20356703244773120836621331 30535054867159681254931997)
            ·
              refine ⟨11450645575184880470599499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30535054867159681254931997 11450645575184880470599499)
              ·
                refine ⟨17175968362777320705899249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11450645575184880470599499 17175968362777320705899249)
                ·
                  refine ⟨12881976272082990529424437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17175968362777320705899249 12881976272082990529424437)
                  ·
                    refine ⟨1207685275507780362133541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12881976272082990529424437 1207685275507780362133541)
                    ·
                      rfl

theorem cell23_7055876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_7055876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055876 prefixEnd_7055876 := by exact prefixLift 7055876
  have htrace : WordTrace (prefixWord ++ tailWord_7055876) baseStart_7055876 baseEnd_7055876 := by
    simpa [prefixWord, tailWord_7055876, baseEnd_7055876] using wordTrace_append hprefix tailTrace_7055876
  have hstable : (prefixWord ++ tailWord_7055876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055876).length < 2 ^ (prefixWord ++ tailWord_7055876).sum := by decide
  have hdescent : baseEnd_7055876 < baseStart_7055876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055896 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 2, 4, 2]
def baseStart_7055896 : Nat := 118140960795 + 7055896 * 2 ^ 59
def prefixEnd_7055896 : Nat := 4983230072969 + 3 ^ 40 * 7055896 * 2
def baseEnd_7055896 : Nat := 3623066096136431008150531

theorem tailTrace_7055896 : CollatzResearch.WordTrace tailWord_7055896 prefixEnd_7055896 3623066096136431008150531 := by
  unfold tailWord_7055896
  simp only [CollatzResearch.WordTrace]
  refine ⟨128674834622850658971445771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171566446163800878628594361 128674834622850658971445771)
  ·
    refine ⟨193012251934275988457168657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128674834622850658971445771 193012251934275988457168657)
    ·
      refine ⟨144759188950706991342876493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193012251934275988457168657 144759188950706991342876493)
      ·
        refine ⟨54284695856515121753578685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144759188950706991342876493 54284695856515121753578685)
        ·
          refine ⟨20356760946193170657592007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54284695856515121753578685 20356760946193170657592007)
          ·
            refine ⟨30535141419289755986388011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20356760946193170657592007 30535141419289755986388011)
            ·
              refine ⟨45802712128934633979582017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30535141419289755986388011 45802712128934633979582017)
              ·
                refine ⟨34352034096700975484686513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45802712128934633979582017 34352034096700975484686513)
                ·
                  refine ⟨25764025572525731613514885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34352034096700975484686513 25764025572525731613514885)
                  ·
                    refine ⟨4830754794848574677534041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25764025572525731613514885 4830754794848574677534041)
                    ·
                      refine ⟨3623066096136431008150531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4830754794848574677534041 3623066096136431008150531)
                      ·
                        rfl

theorem cell23_7055896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_7055896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055896 prefixEnd_7055896 := by exact prefixLift 7055896
  have htrace : WordTrace (prefixWord ++ tailWord_7055896) baseStart_7055896 baseEnd_7055896 := by
    simpa [prefixWord, tailWord_7055896, baseEnd_7055896] using wordTrace_append hprefix tailTrace_7055896
  have hstable : (prefixWord ++ tailWord_7055896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055896).length < 2 ^ (prefixWord ++ tailWord_7055896).sum := by decide
  have hdescent : baseEnd_7055896 < baseStart_7055896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055929 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 2, 5, 3]
def baseStart_7055929 : Nat := 118140960795 + 7055929 * 2 ^ 59
def prefixEnd_7055929 : Nat := 4983230072969 + 3 ^ 40 * 7055929 * 2
def baseEnd_7055929 : Nat := 3623083040998029379037879

theorem tailTrace_7055929 : CollatzResearch.WordTrace tailWord_7055929 prefixEnd_7055929 3623083040998029379037879 := by
  unfold tailWord_7055929
  simp only [CollatzResearch.WordTrace]
  refine ⟨257350872854581764578842841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171567248569721176385895227 257350872854581764578842841)
  ·
    refine ⟨193013154640936323434132131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257350872854581764578842841 193013154640936323434132131)
    ·
      refine ⟨289519731961404485151198197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193013154640936323434132131 289519731961404485151198197)
      ·
        refine ⟨27142474871381670482924831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 289519731961404485151198197 27142474871381670482924831)
        ·
          refine ⟨40713712307072505724387247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27142474871381670482924831 40713712307072505724387247)
          ·
            refine ⟨61070568460608758586580871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40713712307072505724387247 61070568460608758586580871)
            ·
              refine ⟨91605852690913137879871307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61070568460608758586580871 91605852690913137879871307)
              ·
                refine ⟨137408779036369706819806961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91605852690913137879871307 137408779036369706819806961)
                ·
                  refine ⟨103056584277277280114855221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137408779036369706819806961 103056584277277280114855221)
                  ·
                    refine ⟨9661554775994745010767677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103056584277277280114855221 9661554775994745010767677)
                    ·
                      refine ⟨3623083040998029379037879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9661554775994745010767677 3623083040998029379037879)
                      ·
                        rfl

theorem cell23_7055929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_7055929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055929 prefixEnd_7055929 := by exact prefixLift 7055929
  have htrace : WordTrace (prefixWord ++ tailWord_7055929) baseStart_7055929 baseEnd_7055929 := by
    simpa [prefixWord, tailWord_7055929, baseEnd_7055929] using wordTrace_append hprefix tailTrace_7055929
  have hstable : (prefixWord ++ tailWord_7055929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055929).length < 2 ^ (prefixWord ++ tailWord_7055929).sum := by decide
  have hdescent : baseEnd_7055929 < baseStart_7055929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7055979 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 6, 4]
def baseStart_7055979 : Nat := 118140960795 + 7055979 * 2 ^ 59
def prefixEnd_7055979 : Nat := 4983230072969 + 3 ^ 40 * 7055979 * 2
def baseEnd_7055979 : Nat := 1207702905010251394470883

theorem tailTrace_7055979 : CollatzResearch.WordTrace tailWord_7055979 prefixEnd_7055979 1207702905010251394470883 := by
  unfold tailWord_7055979
  simp only [CollatzResearch.WordTrace]
  refine ⟨257352696504400623118162991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171568464336267082078775327 257352696504400623118162991)
  ·
    refine ⟨386029044756600934677244487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257352696504400623118162991 386029044756600934677244487)
    ·
      refine ⟨579043567134901402015866731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386029044756600934677244487 579043567134901402015866731)
      ·
        refine ⟨868565350702352103023800097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579043567134901402015866731 868565350702352103023800097)
        ·
          refine ⟨651424013026764077267850073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 868565350702352103023800097 651424013026764077267850073)
          ·
            refine ⟨488568009770073057950887555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651424013026764077267850073 488568009770073057950887555)
            ·
              refine ⟨732852014655109586926331333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488568009770073057950887555 732852014655109586926331333)
              ·
                refine ⟨137409752747833047548687125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 732852014655109586926331333 137409752747833047548687125)
                ·
                  refine ⟨6441082160054674103844709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137409752747833047548687125 6441082160054674103844709)
                  ·
                    refine ⟨1207702905010251394470883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6441082160054674103844709 1207702905010251394470883)
                    ·
                      rfl

theorem cell23_7055979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 4].length) (baseStart_7055979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7055979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7055979 prefixEnd_7055979 := by exact prefixLift 7055979
  have htrace : WordTrace (prefixWord ++ tailWord_7055979) baseStart_7055979 baseEnd_7055979 := by
    simpa [prefixWord, tailWord_7055979, baseEnd_7055979] using wordTrace_append hprefix tailTrace_7055979
  have hstable : (prefixWord ++ tailWord_7055979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7055979).length < 2 ^ (prefixWord ++ tailWord_7055979).sum := by decide
  have hdescent : baseEnd_7055979 < baseStart_7055979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7055979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056029 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_7056029 : Nat := 118140960795 + 7056029 * 2 ^ 59
def prefixEnd_7056029 : Nat := 4983230072969 + 3 ^ 40 * 7056029 * 2
def baseEnd_7056029 : Nat := 3623134389063478987787419

theorem tailTrace_7056029 : CollatzResearch.WordTrace tailWord_7056029 prefixEnd_7056029 3623134389063478987787419 := by
  unfold tailWord_7056029
  simp only [CollatzResearch.WordTrace]
  refine ⟨257354520154219481657483141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171569680102812987771655427 257354520154219481657483141)
  ·
    refine ⟨48253972528916152810778089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257354520154219481657483141 48253972528916152810778089)
    ·
      refine ⟨36190479396687114608083567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48253972528916152810778089 36190479396687114608083567)
      ·
        refine ⟨54285719095030671912125351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36190479396687114608083567 54285719095030671912125351)
        ·
          refine ⟨81428578642546007868188027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54285719095030671912125351 81428578642546007868188027)
          ·
            refine ⟨122142867963819011802282041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81428578642546007868188027 122142867963819011802282041)
            ·
              refine ⟨91607150972864258851711531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122142867963819011802282041 91607150972864258851711531)
              ·
                refine ⟨137410726459296388277567297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91607150972864258851711531 137410726459296388277567297)
                ·
                  refine ⟨103058044844472291208175473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137410726459296388277567297 103058044844472291208175473)
                  ·
                    refine ⟨77293533633354218406131605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103058044844472291208175473 77293533633354218406131605)
                    ·
                      refine ⟨3623134389063478987787419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77293533633354218406131605 3623134389063478987787419)
                      ·
                        rfl

theorem cell23_7056029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_7056029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056029 prefixEnd_7056029 := by exact prefixLift 7056029
  have htrace : WordTrace (prefixWord ++ tailWord_7056029) baseStart_7056029 baseEnd_7056029 := by
    simpa [prefixWord, tailWord_7056029, baseEnd_7056029] using wordTrace_append hprefix tailTrace_7056029
  have hstable : (prefixWord ++ tailWord_7056029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056029).length < 2 ^ (prefixWord ++ tailWord_7056029).sum := by decide
  have hdescent : baseEnd_7056029 < baseStart_7056029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056033 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 1, 2, 4]
def baseStart_7056033 : Nat := 118140960795 + 7056033 * 2 ^ 59
def prefixEnd_7056033 : Nat := 4983230072969 + 3 ^ 40 * 7056033 * 2
def baseEnd_7056033 : Nat := 3623136442986096972137401

theorem tailTrace_7056033 : CollatzResearch.WordTrace tailWord_7056033 prefixEnd_7056033 3623136442986096972137401 := by
  unfold tailWord_7056033
  simp only [CollatzResearch.WordTrace]
  refine ⟨257354666046204990340628753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171569777364136660227085835 257354666046204990340628753)
  ·
    refine ⟨193015999534653742755471565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257354666046204990340628753 193015999534653742755471565)
    ·
      refine ⟨72380999825495153533301837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193015999534653742755471565 72380999825495153533301837)
      ·
        refine ⟨27142874934560682574988189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72380999825495153533301837 27142874934560682574988189)
        ·
          refine ⟨10178578100460255965620571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27142874934560682574988189 10178578100460255965620571)
          ·
            refine ⟨15267867150690383948430857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10178578100460255965620571 15267867150690383948430857)
            ·
              refine ⟨11450900363017787961323143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15267867150690383948430857 11450900363017787961323143)
              ·
                refine ⟨17176350544526681941984715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11450900363017787961323143 17176350544526681941984715)
                ·
                  refine ⟨25764525816790022912977073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17176350544526681941984715 25764525816790022912977073)
                  ·
                    refine ⟨19323394362592517184732805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25764525816790022912977073 19323394362592517184732805)
                    ·
                      refine ⟨3623136442986096972137401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19323394362592517184732805 3623136442986096972137401)
                      ·
                        rfl

theorem cell23_7056033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_7056033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056033 prefixEnd_7056033 := by exact prefixLift 7056033
  have htrace : WordTrace (prefixWord ++ tailWord_7056033) baseStart_7056033 baseEnd_7056033 := by
    simpa [prefixWord, tailWord_7056033, baseEnd_7056033] using wordTrace_append hprefix tailTrace_7056033
  have hstable : (prefixWord ++ tailWord_7056033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056033).length < 2 ^ (prefixWord ++ tailWord_7056033).sum := by decide
  have hdescent : baseEnd_7056033 < baseStart_7056033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056053 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_7056053 : Nat := 118140960795 + 7056053 * 2 ^ 59
def prefixEnd_7056053 : Nat := 4983230072969 + 3 ^ 40 * 7056053 * 2
def baseEnd_7056053 : Nat := 3623146712599186893887309

theorem tailTrace_7056053 : CollatzResearch.WordTrace tailWord_7056053 prefixEnd_7056053 3623146712599186893887309 := by
  unfold tailWord_7056053
  simp only [CollatzResearch.WordTrace]
  refine ⟨257355395506132533756356813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171570263670755022504237875 257355395506132533756356813)
  ·
    refine ⟨96508273314799700158633805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257355395506132533756356813 96508273314799700158633805)
    ·
      refine ⟨36190602493049887559487677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96508273314799700158633805 36190602493049887559487677)
      ·
        refine ⟨13571475934893707834807879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36190602493049887559487677 13571475934893707834807879)
        ·
          refine ⟨20357213902340561752211819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13571475934893707834807879 20357213902340561752211819)
          ·
            refine ⟨30535820853510842628317729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20357213902340561752211819 30535820853510842628317729)
            ·
              refine ⟨22901865640133131971238297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30535820853510842628317729 22901865640133131971238297)
              ·
                refine ⟨17176399230099848978428723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22901865640133131971238297 17176399230099848978428723)
                ·
                  refine ⟨25764598845149773467643085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17176399230099848978428723 25764598845149773467643085)
                  ·
                    refine ⟨9661724566931165050366157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25764598845149773467643085 9661724566931165050366157)
                    ·
                      refine ⟨3623146712599186893887309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9661724566931165050366157 3623146712599186893887309)
                      ·
                        rfl

theorem cell23_7056053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_7056053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056053 prefixEnd_7056053 := by exact prefixLift 7056053
  have htrace : WordTrace (prefixWord ++ tailWord_7056053) baseStart_7056053 baseEnd_7056053 := by
    simpa [prefixWord, tailWord_7056053, baseEnd_7056053] using wordTrace_append hprefix tailTrace_7056053
  have hstable : (prefixWord ++ tailWord_7056053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056053).length < 2 ^ (prefixWord ++ tailWord_7056053).sum := by decide
  have hdescent : baseEnd_7056053 < baseStart_7056053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056054 : List Nat := [5, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_7056054 : Nat := 118140960795 + 7056054 * 2 ^ 59
def prefixEnd_7056054 : Nat := 4983230072969 + 3 ^ 40 * 7056054 * 2
def baseEnd_7056054 : Nat := 3623147226079841389974805

theorem tailTrace_7056054 : CollatzResearch.WordTrace tailWord_7056054 prefixEnd_7056054 3623147226079841389974805 := by
  unfold tailWord_7056054
  simp only [CollatzResearch.WordTrace]
  refine ⟨16084714498695556932946451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171570287986085940618095477 16084714498695556932946451)
  ·
    refine ⟨24127071748043335399419677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16084714498695556932946451 24127071748043335399419677)
    ·
      refine ⟨9047651905516250774782379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24127071748043335399419677 9047651905516250774782379)
      ·
        refine ⟨13571477858274376162173569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9047651905516250774782379 13571477858274376162173569)
        ·
          refine ⟨10178608393705782121630177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13571477858274376162173569 10178608393705782121630177)
          ·
            refine ⟨7633956295279336591222633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10178608393705782121630177 7633956295279336591222633)
            ·
              refine ⟨5725467221459502443416975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7633956295279336591222633 5725467221459502443416975)
              ·
                refine ⟨8588200832189253665125463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5725467221459502443416975 8588200832189253665125463)
                ·
                  refine ⟨12882301248283880497688195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8588200832189253665125463 12882301248283880497688195)
                  ·
                    refine ⟨19323451872425820746532293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12882301248283880497688195 19323451872425820746532293)
                    ·
                      refine ⟨3623147226079841389974805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19323451872425820746532293 3623147226079841389974805)
                      ·
                        rfl

theorem cell23_7056054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_7056054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056054 prefixEnd_7056054 := by exact prefixLift 7056054
  have htrace : WordTrace (prefixWord ++ tailWord_7056054) baseStart_7056054 baseEnd_7056054 := by
    simpa [prefixWord, tailWord_7056054, baseEnd_7056054] using wordTrace_append hprefix tailTrace_7056054
  have hstable : (prefixWord ++ tailWord_7056054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056054).length < 2 ^ (prefixWord ++ tailWord_7056054).sum := by decide
  have hdescent : baseEnd_7056054 < baseStart_7056054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056079 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 5]
def baseStart_7056079 : Nat := 118140960795 + 7056079 * 2 ^ 59
def prefixEnd_7056079 : Nat := 4983230072969 + 3 ^ 40 * 7056079 * 2
def baseEnd_7056079 : Nat := 3623160063096203792162189

theorem tailTrace_7056079 : CollatzResearch.WordTrace tailWord_7056079 prefixEnd_7056079 3623160063096203792162189 := by
  unfold tailWord_7056079
  simp only [CollatzResearch.WordTrace]
  refine ⟨257356343804038340196803291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171570895869358893464535527 257356343804038340196803291)
  ·
    refine ⟨386034515706057510295204937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257356343804038340196803291 386034515706057510295204937)
    ·
      refine ⟨289525886779543132721403703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386034515706057510295204937 289525886779543132721403703)
      ·
        refine ⟨434288830169314699082105555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289525886779543132721403703 434288830169314699082105555)
        ·
          refine ⟨651433245253972048623158333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434288830169314699082105555 651433245253972048623158333)
          ·
            refine ⟨244287466970239518233684375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 651433245253972048623158333 244287466970239518233684375)
            ·
              refine ⟨366431200455359277350526563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244287466970239518233684375 366431200455359277350526563)
              ·
                refine ⟨549646800683038916025789845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366431200455359277350526563 549646800683038916025789845)
                ·
                  refine ⟨25764693782017449188708899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 549646800683038916025789845 25764693782017449188708899)
                  ·
                    refine ⟨38647040673026173783063349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25764693782017449188708899 38647040673026173783063349)
                    ·
                      refine ⟨3623160063096203792162189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38647040673026173783063349 3623160063096203792162189)
                      ·
                        rfl

theorem cell23_7056079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_7056079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056079 prefixEnd_7056079 := by exact prefixLift 7056079
  have htrace : WordTrace (prefixWord ++ tailWord_7056079) baseStart_7056079 baseEnd_7056079 := by
    simpa [prefixWord, tailWord_7056079, baseEnd_7056079] using wordTrace_append hprefix tailTrace_7056079
  have hstable : (prefixWord ++ tailWord_7056079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056079).length < 2 ^ (prefixWord ++ tailWord_7056079).sum := by decide
  have hdescent : baseEnd_7056079 < baseStart_7056079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056110 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 4, 2, 2]
def baseStart_7056110 : Nat := 118140960795 + 7056110 * 2 ^ 59
def prefixEnd_7056110 : Nat := 4983230072969 + 3 ^ 40 * 7056110 * 2
def baseEnd_7056110 : Nat := 3623175980996493170874547

theorem tailTrace_7056110 : CollatzResearch.WordTrace tailWord_7056110 prefixEnd_7056110 3623175980996493170874547 := by
  unfold tailWord_7056110
  simp only [CollatzResearch.WordTrace]
  refine ⟨32169684308365754061397723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171571649644617354994121189 32169684308365754061397723)
  ·
    refine ⟨48254526462548631092096585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32169684308365754061397723 48254526462548631092096585)
    ·
      refine ⟨36190894846911473319072439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48254526462548631092096585 36190894846911473319072439)
      ·
        refine ⟨54286342270367209978608659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36190894846911473319072439 54286342270367209978608659)
        ·
          refine ⟨81429513405550814967912989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54286342270367209978608659 81429513405550814967912989)
          ·
            refine ⟨30536067527081555612967371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81429513405550814967912989 30536067527081555612967371)
            ·
              refine ⟨45804101290622333419451057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30536067527081555612967371 45804101290622333419451057)
              ·
                refine ⟨34353075967966750064588293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45804101290622333419451057 34353075967966750064588293)
                ·
                  refine ⟨6441201743993765637110305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34353075967966750064588293 6441201743993765637110305)
                  ·
                    refine ⟨4830901307995324227832729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6441201743993765637110305 4830901307995324227832729)
                    ·
                      refine ⟨3623175980996493170874547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4830901307995324227832729 3623175980996493170874547)
                      ·
                        rfl

theorem cell23_7056110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_7056110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056110 prefixEnd_7056110 := by exact prefixLift 7056110
  have htrace : WordTrace (prefixWord ++ tailWord_7056110) baseStart_7056110 baseEnd_7056110 := by
    simpa [prefixWord, tailWord_7056110, baseEnd_7056110] using wordTrace_append hprefix tailTrace_7056110
  have hstable : (prefixWord ++ tailWord_7056110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056110).length < 2 ^ (prefixWord ++ tailWord_7056110).sum := by decide
  have hdescent : baseEnd_7056110 < baseStart_7056110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056183 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 2, 4, 2]
def baseStart_7056183 : Nat := 118140960795 + 7056183 * 2 ^ 59
def prefixEnd_7056183 : Nat := 4983230072969 + 3 ^ 40 * 7056183 * 2
def baseEnd_7056183 : Nat := 3623213465084271385261711

theorem tailTrace_7056183 : CollatzResearch.WordTrace tailWord_7056183 prefixEnd_7056183 3623213465084271385261711 := by
  unfold tailWord_7056183
  simp only [CollatzResearch.WordTrace]
  refine ⟨257360136995661565958589203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171573424663774377305726135 257360136995661565958589203)
  ·
    refine ⟨386040205493492348937883805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257360136995661565958589203 386040205493492348937883805)
    ·
      refine ⟨144765077060059630851706427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386040205493492348937883805 144765077060059630851706427)
      ·
        refine ⟨217147615590089446277559641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144765077060059630851706427 217147615590089446277559641)
        ·
          refine ⟨162860711692567084708169731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217147615590089446277559641 162860711692567084708169731)
          ·
            refine ⟨244291067538850627062254597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162860711692567084708169731 244291067538850627062254597)
            ·
              refine ⟨45804575163534492574172737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244291067538850627062254597 45804575163534492574172737)
              ·
                refine ⟨34353431372650869430629553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45804575163534492574172737 34353431372650869430629553)
                ·
                  refine ⟨25765073529488152072972165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34353431372650869430629553 25765073529488152072972165)
                  ·
                    refine ⟨4830951286779028513682281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25765073529488152072972165 4830951286779028513682281)
                    ·
                      refine ⟨3623213465084271385261711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4830951286779028513682281 3623213465084271385261711)
                      ·
                        rfl

theorem cell23_7056183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 4, 2].length) (baseStart_7056183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056183 prefixEnd_7056183 := by exact prefixLift 7056183
  have htrace : WordTrace (prefixWord ++ tailWord_7056183) baseStart_7056183 baseEnd_7056183 := by
    simpa [prefixWord, tailWord_7056183, baseEnd_7056183] using wordTrace_append hprefix tailTrace_7056183
  have hstable : (prefixWord ++ tailWord_7056183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056183).length < 2 ^ (prefixWord ++ tailWord_7056183).sum := by decide
  have hdescent : baseEnd_7056183 < baseStart_7056183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056220 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_7056220 : Nat := 118140960795 + 7056220 * 2 ^ 59
def prefixEnd_7056220 : Nat := 4983230072969 + 3 ^ 40 * 7056220 * 2
def baseEnd_7056220 : Nat := 3623232463868487740499041

theorem tailTrace_7056220 : CollatzResearch.WordTrace tailWord_7056220 prefixEnd_7056220 3623232463868487740499041 := by
  unfold tailWord_7056220
  simp only [CollatzResearch.WordTrace]
  refine ⟨128680743248263760638843057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171574324331018347518457409 128680743248263760638843057)
  ·
    refine ⟨96510557436197820479132293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128680743248263760638843057 96510557436197820479132293)
    ·
      refine ⟨18095729519287091339837305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96510557436197820479132293 18095729519287091339837305)
      ·
        refine ⟨13571797139465318504877979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18095729519287091339837305 13571797139465318504877979)
        ·
          refine ⟨20357695709197977757316969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13571797139465318504877979 20357695709197977757316969)
          ·
            refine ⟨15268271781898483317987727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20357695709197977757316969 15268271781898483317987727)
            ·
              refine ⟨22902407672847724976981591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15268271781898483317987727 22902407672847724976981591)
              ·
                refine ⟨34353611509271587465472387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22902407672847724976981591 34353611509271587465472387)
                ·
                  refine ⟨51530417263907381198208581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34353611509271587465472387 51530417263907381198208581)
                  ·
                    refine ⟨9661953236982633974664109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51530417263907381198208581 9661953236982633974664109)
                    ·
                      refine ⟨3623232463868487740499041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9661953236982633974664109 3623232463868487740499041)
                      ·
                        rfl

theorem cell23_7056220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_7056220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056220 prefixEnd_7056220 := by exact prefixLift 7056220
  have htrace : WordTrace (prefixWord ++ tailWord_7056220) baseStart_7056220 baseEnd_7056220 := by
    simpa [prefixWord, tailWord_7056220, baseEnd_7056220] using wordTrace_append hprefix tailTrace_7056220
  have hstable : (prefixWord ++ tailWord_7056220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056220).length < 2 ^ (prefixWord ++ tailWord_7056220).sum := by decide
  have hdescent : baseEnd_7056220 < baseStart_7056220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056227 : List Nat := [1, 1, 1, 5, 3, 2, 2, 3, 1, 4]
def baseStart_7056227 : Nat := 118140960795 + 7056227 * 2 ^ 59
def prefixEnd_7056227 : Nat := 4983230072969 + 3 ^ 40 * 7056227 * 2
def baseEnd_7056227 : Nat := 1207745352744356404370503

theorem tailTrace_7056227 : CollatzResearch.WordTrace tailWord_7056227 prefixEnd_7056227 1207745352744356404370503 := by
  unfold tailWord_7056227
  simp only [CollatzResearch.WordTrace]
  refine ⟨257361741807502161473190935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171574494538334774315460623 257361741807502161473190935)
  ·
    refine ⟨386042612711253242209786403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257361741807502161473190935 386042612711253242209786403)
    ·
      refine ⟨579063919066879863314679605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386042612711253242209786403 579063919066879863314679605)
      ·
        refine ⟨54287242412519987185751213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 579063919066879863314679605 54287242412519987185751213)
        ·
          refine ⟨20357715904694995194656705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54287242412519987185751213 20357715904694995194656705)
          ·
            refine ⟨15268286928521246395992529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20357715904694995194656705 15268286928521246395992529)
            ·
              refine ⟨11451215196390934796994397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15268286928521246395992529 11451215196390934796994397)
              ·
                refine ⟨4294205698646600548872899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11451215196390934796994397 4294205698646600548872899)
                ·
                  refine ⟨6441308547969900823309349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4294205698646600548872899 6441308547969900823309349)
                  ·
                    refine ⟨1207745352744356404370503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6441308547969900823309349 1207745352744356404370503)
                    ·
                      rfl

theorem cell23_7056227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 1, 4].length) (baseStart_7056227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056227 prefixEnd_7056227 := by exact prefixLift 7056227
  have htrace : WordTrace (prefixWord ++ tailWord_7056227) baseStart_7056227 baseEnd_7056227 := by
    simpa [prefixWord, tailWord_7056227, baseEnd_7056227] using wordTrace_append hprefix tailTrace_7056227
  have hstable : (prefixWord ++ tailWord_7056227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056227).length < 2 ^ (prefixWord ++ tailWord_7056227).sum := by decide
  have hdescent : baseEnd_7056227 < baseStart_7056227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056256 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 4]
def baseStart_7056256 : Nat := 118140960795 + 7056256 * 2 ^ 59
def prefixEnd_7056256 : Nat := 4983230072969 + 3 ^ 40 * 7056256 * 2
def baseEnd_7056256 : Nat := 3623250949172049599648875

theorem tailTrace_7056256 : CollatzResearch.WordTrace tailWord_7056256 prefixEnd_7056256 3623250949172049599648875 := by
  unfold tailWord_7056256
  simp only [CollatzResearch.WordTrace]
  refine ⟨128681399762198549712998311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171575199682931399617331081 128681399762198549712998311)
  ·
    refine ⟨193022099643297824569497467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128681399762198549712998311 193022099643297824569497467)
    ·
      refine ⟨289533149464946736854246201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193022099643297824569497467 289533149464946736854246201)
      ·
        refine ⟨217149862098710052640684651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289533149464946736854246201 217149862098710052640684651)
        ·
          refine ⟨325724793148065078961026977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217149862098710052640684651 325724793148065078961026977)
          ·
            refine ⟨244293594861048809220770233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325724793148065078961026977 244293594861048809220770233)
            ·
              refine ⟨183220196145786606915577675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244293594861048809220770233 183220196145786606915577675)
              ·
                refine ⟨274830294218679910373366513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183220196145786606915577675 274830294218679910373366513)
                ·
                  refine ⟨206122720664009932780024885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274830294218679910373366513 206122720664009932780024885)
                  ·
                    refine ⟨19324005062250931198127333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 206122720664009932780024885 19324005062250931198127333)
                    ·
                      refine ⟨3623250949172049599648875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19324005062250931198127333 3623250949172049599648875)
                      ·
                        rfl

theorem cell23_7056256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_7056256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056256 prefixEnd_7056256 := by exact prefixLift 7056256
  have htrace : WordTrace (prefixWord ++ tailWord_7056256) baseStart_7056256 baseEnd_7056256 := by
    simpa [prefixWord, tailWord_7056256, baseEnd_7056256] using wordTrace_append hprefix tailTrace_7056256
  have hstable : (prefixWord ++ tailWord_7056256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056256).length < 2 ^ (prefixWord ++ tailWord_7056256).sum := by decide
  have hdescent : baseEnd_7056256 < baseStart_7056256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056273 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 1, 8, 2]
def baseStart_7056273 : Nat := 118140960795 + 7056273 * 2 ^ 59
def prefixEnd_7056273 : Nat := 4983230072969 + 3 ^ 40 * 7056273 * 2
def baseEnd_7056273 : Nat := 3623259678343176033136297

theorem tailTrace_7056273 : CollatzResearch.WordTrace tailWord_7056273 prefixEnd_7056273 3623259678343176033136297 := by
  unfold tailWord_7056273
  simp only [CollatzResearch.WordTrace]
  refine ⟨257363419565335511329365473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171575613043557007552910315 257363419565335511329365473)
  ·
    refine ⟨193022564674001633497024105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257363419565335511329365473 193022564674001633497024105)
    ·
      refine ⟨144766923505501225122768079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193022564674001633497024105 144766923505501225122768079)
      ·
        refine ⟨217150385258251837684152119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144766923505501225122768079 217150385258251837684152119)
        ·
          refine ⟨325725577887377756526228179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217150385258251837684152119 325725577887377756526228179)
          ·
            refine ⟨488588366831066634789342269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325725577887377756526228179 488588366831066634789342269)
            ·
              refine ⟨183220637561649988046003351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 488588366831066634789342269 183220637561649988046003351)
              ·
                refine ⟨274830956342474982069005027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183220637561649988046003351 274830956342474982069005027)
                ·
                  refine ⟨412246434513712473103507541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274830956342474982069005027 412246434513712473103507541)
                  ·
                    refine ⟨4831012904457568044181729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 412246434513712473103507541 4831012904457568044181729)
                    ·
                      refine ⟨3623259678343176033136297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4831012904457568044181729 3623259678343176033136297)
                      ·
                        rfl

theorem cell23_7056273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 8, 2].length) (baseStart_7056273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056273 prefixEnd_7056273 := by exact prefixLift 7056273
  have htrace : WordTrace (prefixWord ++ tailWord_7056273) baseStart_7056273 baseEnd_7056273 := by
    simpa [prefixWord, tailWord_7056273, baseEnd_7056273] using wordTrace_append hprefix tailTrace_7056273
  have hstable : (prefixWord ++ tailWord_7056273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056273).length < 2 ^ (prefixWord ++ tailWord_7056273).sum := by decide
  have hdescent : baseEnd_7056273 < baseStart_7056273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056278 : List Nat := [5, 3, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_7056278 : Nat := 118140960795 + 7056278 * 2 ^ 59
def prefixEnd_7056278 : Nat := 4983230072969 + 3 ^ 40 * 7056278 * 2
def baseEnd_7056278 : Nat := 1207754081915482837857925

theorem tailTrace_7056278 : CollatzResearch.WordTrace tailWord_7056278 prefixEnd_7056278 1207754081915482837857925 := by
  unfold tailWord_7056278
  simp only [CollatzResearch.WordTrace]
  refine ⟨16085225120644837323956093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171575734620211598122198325 16085225120644837323956093)
  ·
    refine ⟨6031959420241813996483535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16085225120644837323956093 6031959420241813996483535)
    ·
      refine ⟨9047939130362720994725303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6031959420241813996483535 9047939130362720994725303)
      ·
        refine ⟨13571908695544081492087955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9047939130362720994725303 13571908695544081492087955)
        ·
          refine ⟨20357863043316122238131933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13571908695544081492087955 20357863043316122238131933)
          ·
            refine ⟨7634198641243545839299475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20357863043316122238131933 7634198641243545839299475)
            ·
              refine ⟨11451297961865318758949213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7634198641243545839299475 11451297961865318758949213)
              ·
                refine ⟨4294236735699494534605955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11451297961865318758949213 4294236735699494534605955)
                ·
                  refine ⟨6441355103549241801908933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4294236735699494534605955 6441355103549241801908933)
                  ·
                    refine ⟨1207754081915482837857925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6441355103549241801908933 1207754081915482837857925)
                    ·
                      rfl

theorem cell23_7056278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_7056278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056278 prefixEnd_7056278 := by exact prefixLift 7056278
  have htrace : WordTrace (prefixWord ++ tailWord_7056278) baseStart_7056278 baseEnd_7056278 := by
    simpa [prefixWord, tailWord_7056278, baseEnd_7056278] using wordTrace_append hprefix tailTrace_7056278
  have hstable : (prefixWord ++ tailWord_7056278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056278).length < 2 ^ (prefixWord ++ tailWord_7056278).sum := by decide
  have hdescent : baseEnd_7056278 < baseStart_7056278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056293 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 7, 2, 3]
def baseStart_7056293 : Nat := 118140960795 + 7056293 * 2 ^ 59
def prefixEnd_7056293 : Nat := 4983230072969 + 3 ^ 40 * 7056293 * 2
def baseEnd_7056293 : Nat := 3623269947956265954886205

theorem tailTrace_7056293 : CollatzResearch.WordTrace tailWord_7056293 prefixEnd_7056293 3623269947956265954886205 := by
  unfold tailWord_7056293
  simp only [CollatzResearch.WordTrace]
  refine ⟨257364149025263054745093533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171576099350175369830062355 257364149025263054745093533)
  ·
    refine ⟨96511555884473645529410075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257364149025263054745093533 96511555884473645529410075)
    ·
      refine ⟨144767333826710468294115113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96511555884473645529410075 144767333826710468294115113)
      ·
        refine ⟨108575500370032851220586335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144767333826710468294115113 108575500370032851220586335)
        ·
          refine ⟨162863250555049276830879503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108575500370032851220586335 162863250555049276830879503)
          ·
            refine ⟨244294875832573915246319255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162863250555049276830879503 244294875832573915246319255)
            ·
              refine ⟨366442313748860872869478883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244294875832573915246319255 366442313748860872869478883)
              ·
                refine ⟨549663470623291309304218325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366442313748860872869478883 549663470623291309304218325)
                ·
                  refine ⟨12882737592733390061817617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 549663470623291309304218325 12882737592733390061817617)
                  ·
                    refine ⟨9662053194550042546363213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12882737592733390061817617 9662053194550042546363213)
                    ·
                      refine ⟨3623269947956265954886205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9662053194550042546363213 3623269947956265954886205)
                      ·
                        rfl

theorem cell23_7056293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_7056293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056293 prefixEnd_7056293 := by exact prefixLift 7056293
  have htrace : WordTrace (prefixWord ++ tailWord_7056293) baseStart_7056293 baseEnd_7056293 := by
    simpa [prefixWord, tailWord_7056293, baseEnd_7056293] using wordTrace_append hprefix tailTrace_7056293
  have hstable : (prefixWord ++ tailWord_7056293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056293).length < 2 ^ (prefixWord ++ tailWord_7056293).sum := by decide
  have hdescent : baseEnd_7056293 < baseStart_7056293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056301 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_7056301 : Nat := 118140960795 + 7056301 * 2 ^ 59
def prefixEnd_7056301 : Nat := 4983230072969 + 3 ^ 40 * 7056301 * 2
def baseEnd_7056301 : Nat := 3623274055801501923586169

theorem tailTrace_7056301 : CollatzResearch.WordTrace tailWord_7056301 prefixEnd_7056301 3623274055801501923586169 := by
  unfold tailWord_7056301
  simp only [CollatzResearch.WordTrace]
  refine ⟨257364440809234072111384757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171576293872822714740923171 257364440809234072111384757)
  ·
    refine ⟨24127916325865694260442321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257364440809234072111384757 24127916325865694260442321)
    ·
      refine ⟨18095937244399270695331741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24127916325865694260442321 18095937244399270695331741)
      ·
        refine ⟨6785976466649726510749403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18095937244399270695331741 6785976466649726510749403)
        ·
          refine ⟨10178964699974589766124105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6785976466649726510749403 10178964699974589766124105)
          ·
            refine ⟨7634223524980942324593079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10178964699974589766124105 7634223524980942324593079)
            ·
              refine ⟨11451335287471413486889619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7634223524980942324593079 11451335287471413486889619)
              ·
                refine ⟨17177002931207120230334429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11451335287471413486889619 17177002931207120230334429)
                ·
                  refine ⟨6441376099202670086375411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17177002931207120230334429 6441376099202670086375411)
                  ·
                    refine ⟨9662064148804005129563117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6441376099202670086375411 9662064148804005129563117)
                    ·
                      refine ⟨3623274055801501923586169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9662064148804005129563117 3623274055801501923586169)
                      ·
                        rfl

theorem cell23_7056301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_7056301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056301 prefixEnd_7056301 := by exact prefixLift 7056301
  have htrace : WordTrace (prefixWord ++ tailWord_7056301) baseStart_7056301 baseEnd_7056301 := by
    simpa [prefixWord, tailWord_7056301, baseEnd_7056301] using wordTrace_append hprefix tailTrace_7056301
  have hstable : (prefixWord ++ tailWord_7056301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056301).length < 2 ^ (prefixWord ++ tailWord_7056301).sum := by decide
  have hdescent : baseEnd_7056301 < baseStart_7056301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056313 : List Nat := [1, 2, 1, 4, 2, 3, 2, 8]
def baseStart_7056313 : Nat := 118140960795 + 7056313 * 2 ^ 59
def prefixEnd_7056313 : Nat := 4983230072969 + 3 ^ 40 * 7056313 * 2
def baseEnd_7056313 : Nat := 134195563613679847282819

theorem tailTrace_7056313 : CollatzResearch.WordTrace tailWord_7056313 prefixEnd_7056313 134195563613679847282819 := by
  unfold tailWord_7056313
  simp only [CollatzResearch.WordTrace]
  refine ⟨257364878485190598160821593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171576585656793732107214395 257364878485190598160821593)
  ·
    refine ⟨193023658863892948620616195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257364878485190598160821593 193023658863892948620616195)
    ·
      refine ⟨289535488295839422930924293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193023658863892948620616195 289535488295839422930924293)
      ·
        refine ⟨54287904055469891799548305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289535488295839422930924293 54287904055469891799548305)
        ·
          refine ⟨40715928041602418849661229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54287904055469891799548305 40715928041602418849661229)
          ·
            refine ⟨15268473015600907068622961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40715928041602418849661229 15268473015600907068622961)
            ·
              refine ⟨11451354761700680301467221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15268473015600907068622961 11451354761700680301467221)
              ·
                refine ⟨134195563613679847282819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11451354761700680301467221 134195563613679847282819)
                ·
                  rfl

theorem cell23_7056313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 8].length) (baseStart_7056313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056313 prefixEnd_7056313 := by exact prefixLift 7056313
  have htrace : WordTrace (prefixWord ++ tailWord_7056313) baseStart_7056313 baseEnd_7056313 := by
    simpa [prefixWord, tailWord_7056313, baseEnd_7056313] using wordTrace_append hprefix tailTrace_7056313
  have hstable : (prefixWord ++ tailWord_7056313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056313).length < 2 ^ (prefixWord ++ tailWord_7056313).sum := by decide
  have hdescent : baseEnd_7056313 < baseStart_7056313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056317 : List Nat := [1, 4, 1, 2, 4, 1, 1, 3, 2, 4]
def baseStart_7056317 : Nat := 118140960795 + 7056317 * 2 ^ 59
def prefixEnd_7056317 : Nat := 4983230072969 + 3 ^ 40 * 7056317 * 2
def baseEnd_7056317 : Nat := 1207760757163991286995365

theorem tailTrace_7056317 : CollatzResearch.WordTrace tailWord_7056317 prefixEnd_7056317 1207760757163991286995365 := by
  unfold tailWord_7056317
  simp only [CollatzResearch.WordTrace]
  refine ⟨257365024377176106843967205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171576682918117404562644803 257365024377176106843967205)
  ·
    refine ⟨48255942070720520033243851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257365024377176106843967205 48255942070720520033243851)
    ·
      refine ⟨72383913106080780049865777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48255942070720520033243851 72383913106080780049865777)
      ·
        refine ⟨54287934829560585037399333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72383913106080780049865777 54287934829560585037399333)
        ·
          refine ⟨10178987780542609694512375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54287934829560585037399333 10178987780542609694512375)
          ·
            refine ⟨15268481670813914541768563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10178987780542609694512375 15268481670813914541768563)
            ·
              refine ⟨22902722506220871812652845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15268481670813914541768563 22902722506220871812652845)
              ·
                refine ⟨8588520939832826929744817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22902722506220871812652845 8588520939832826929744817)
                ·
                  refine ⟨6441390704874620197308613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8588520939832826929744817 6441390704874620197308613)
                  ·
                    refine ⟨1207760757163991286995365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6441390704874620197308613 1207760757163991286995365)
                    ·
                      rfl

theorem cell23_7056317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_7056317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056317 prefixEnd_7056317 := by exact prefixLift 7056317
  have htrace : WordTrace (prefixWord ++ tailWord_7056317) baseStart_7056317 baseEnd_7056317 := by
    simpa [prefixWord, tailWord_7056317, baseEnd_7056317] using wordTrace_append hprefix tailTrace_7056317
  have hstable : (prefixWord ++ tailWord_7056317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056317).length < 2 ^ (prefixWord ++ tailWord_7056317).sum := by decide
  have hdescent : baseEnd_7056317 < baseStart_7056317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056340 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_7056340 : Nat := 118140960795 + 7056340 * 2 ^ 59
def prefixEnd_7056340 : Nat := 4983230072969 + 3 ^ 40 * 7056340 * 2
def baseEnd_7056340 : Nat := 3623294081547027270998489

theorem tailTrace_7056340 : CollatzResearch.WordTrace tailWord_7056340 prefixEnd_7056340 3623294081547027270998489 := by
  unfold tailWord_7056340
  simp only [CollatzResearch.WordTrace]
  refine ⟨128682931628046390886027237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171577242170728521181369649 128682931628046390886027237)
  ·
    refine ⟨24128049680258698291130107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128682931628046390886027237 24128049680258698291130107)
    ·
      refine ⟨36192074520388047436695161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24128049680258698291130107 36192074520388047436695161)
      ·
        refine ⟨27144055890291035577521371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36192074520388047436695161 27144055890291035577521371)
        ·
          refine ⟨40716083835436553366282057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27144055890291035577521371 40716083835436553366282057)
          ·
            refine ⟨30537062876577415024711543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40716083835436553366282057 30537062876577415024711543)
            ·
              refine ⟨45805594314866122537067315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30537062876577415024711543 45805594314866122537067315)
              ·
                refine ⟨68708391472299183805600973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45805594314866122537067315 68708391472299183805600973)
                ·
                  refine ⟨25765646802112193927100365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68708391472299183805600973 25765646802112193927100365)
                  ·
                    refine ⟨9662117550792072722662637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25765646802112193927100365 9662117550792072722662637)
                    ·
                      refine ⟨3623294081547027270998489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9662117550792072722662637 3623294081547027270998489)
                      ·
                        rfl

theorem cell23_7056340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_7056340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056340 prefixEnd_7056340 := by exact prefixLift 7056340
  have htrace : WordTrace (prefixWord ++ tailWord_7056340) baseStart_7056340 baseEnd_7056340 := by
    simpa [prefixWord, tailWord_7056340, baseEnd_7056340] using wordTrace_append hprefix tailTrace_7056340
  have hstable : (prefixWord ++ tailWord_7056340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056340).length < 2 ^ (prefixWord ++ tailWord_7056340).sum := by decide
  have hdescent : baseEnd_7056340 < baseStart_7056340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056374 : List Nat := [5, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_7056374 : Nat := 118140960795 + 7056374 * 2 ^ 59
def prefixEnd_7056374 : Nat := 4983230072969 + 3 ^ 40 * 7056374 * 2
def baseEnd_7056374 : Nat := 3623311539889280137973333

theorem tailTrace_7056374 : CollatzResearch.WordTrace tailWord_7056374 prefixEnd_7056374 3623311539889280137973333 := by
  unfold tailWord_7056374
  simp only [CollatzResearch.WordTrace]
  refine ⟨16085443958623100348674511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171578068891979737052528117 16085443958623100348674511)
  ·
    refine ⟨24128165937934650523011767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16085443958623100348674511 24128165937934650523011767)
    ·
      refine ⟨36192248906901975784517651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24128165937934650523011767 36192248906901975784517651)
      ·
        refine ⟨54288373360352963676776477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36192248906901975784517651 54288373360352963676776477)
        ·
          refine ⟨20358140010132361378791179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54288373360352963676776477 20358140010132361378791179)
          ·
            refine ⟨30537210015198542068186769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20358140010132361378791179 30537210015198542068186769)
            ·
              refine ⟨22902907511398906551140077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30537210015198542068186769 22902907511398906551140077)
              ·
                refine ⟨8588590316774589956677529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22902907511398906551140077 8588590316774589956677529)
                ·
                  refine ⟨6441442737580942467508147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8588590316774589956677529 6441442737580942467508147)
                  ·
                    refine ⟨9662164106371413701262221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6441442737580942467508147 9662164106371413701262221)
                    ·
                      refine ⟨3623311539889280137973333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9662164106371413701262221 3623311539889280137973333)
                      ·
                        rfl

theorem cell23_7056374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_7056374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056374 prefixEnd_7056374 := by exact prefixLift 7056374
  have htrace : WordTrace (prefixWord ++ tailWord_7056374) baseStart_7056374 baseEnd_7056374 := by
    simpa [prefixWord, tailWord_7056374, baseEnd_7056374] using wordTrace_append hprefix tailTrace_7056374
  have hstable : (prefixWord ++ tailWord_7056374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056374).length < 2 ^ (prefixWord ++ tailWord_7056374).sum := by decide
  have hdescent : baseEnd_7056374 < baseStart_7056374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056420 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 7]
def baseStart_7056420 : Nat := 118140960795 + 7056420 * 2 ^ 59
def prefixEnd_7056420 : Nat := 4983230072969 + 3 ^ 40 * 7056420 * 2
def baseEnd_7056420 : Nat := 402592795555487439777569

theorem tailTrace_7056420 : CollatzResearch.WordTrace tailWord_7056420 prefixEnd_7056420 402592795555487439777569 := by
  unfold tailWord_7056420
  simp only [CollatzResearch.WordTrace]
  refine ⟨128684390547901477717483357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171579187397201970289977809 128684390547901477717483357)
  ·
    refine ⟨48256646455463054144056259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128684390547901477717483357 48256646455463054144056259)
    ·
      refine ⟨72384969683194581216084389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48256646455463054144056259 72384969683194581216084389)
      ·
        refine ⟨13572181815598983978015823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72384969683194581216084389 13572181815598983978015823)
        ·
          refine ⟨20358272723398475967023735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13572181815598983978015823 20358272723398475967023735)
          ·
            refine ⟨30537409085097713950535603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20358272723398475967023735 30537409085097713950535603)
            ·
              refine ⟨45806113627646570925803405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30537409085097713950535603 45806113627646570925803405)
              ·
                refine ⟨17177292610367464097176277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45806113627646570925803405 17177292610367464097176277)
                ·
                  refine ⟨402592795555487439777569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17177292610367464097176277 402592795555487439777569)
                  ·
                    rfl

theorem cell23_7056420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_7056420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056420 prefixEnd_7056420 := by exact prefixLift 7056420
  have htrace : WordTrace (prefixWord ++ tailWord_7056420) baseStart_7056420 baseEnd_7056420 := by
    simpa [prefixWord, tailWord_7056420, baseEnd_7056420] using wordTrace_append hprefix tailTrace_7056420
  have hstable : (prefixWord ++ tailWord_7056420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056420).length < 2 ^ (prefixWord ++ tailWord_7056420).sum := by decide
  have hdescent : baseEnd_7056420 < baseStart_7056420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056433 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 3, 7]
def baseStart_7056433 : Nat := 118140960795 + 7056433 * 2 ^ 59
def prefixEnd_7056433 : Nat := 4983230072969 + 3 ^ 40 * 7056433 * 2
def baseEnd_7056433 : Nat := 1207780611749298469045187

theorem tailTrace_7056433 : CollatzResearch.WordTrace tailWord_7056433 prefixEnd_7056433 1207780611749298469045187 := by
  unfold tailWord_7056433
  simp only [CollatzResearch.WordTrace]
  refine ⟨257369255244755858655189953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171579503496503905770126635 257369255244755858655189953)
  ·
    refine ⟨193026941433566893991392465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257369255244755858655189953 193026941433566893991392465)
    ·
      refine ⟨144770206075175170493544349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193026941433566893991392465 144770206075175170493544349)
      ·
        refine ⟨54288827278190688935079131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144770206075175170493544349 54288827278190688935079131)
        ·
          refine ⟨81433240917286033402618697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54288827278190688935079131 81433240917286033402618697)
          ·
            refine ⟨61074930687964525051964023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81433240917286033402618697 61074930687964525051964023)
            ·
              refine ⟨91612396031946787577946035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61074930687964525051964023 91612396031946787577946035)
              ·
                refine ⟨137418594047920181366919053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91612396031946787577946035 137418594047920181366919053)
                ·
                  refine ⟨51531972767970068012594645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137418594047920181366919053 51531972767970068012594645)
                  ·
                    refine ⟨1207780611749298469045187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51531972767970068012594645 1207780611749298469045187)
                    ·
                      rfl

theorem cell23_7056433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_7056433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056433 prefixEnd_7056433 := by exact prefixLift 7056433
  have htrace : WordTrace (prefixWord ++ tailWord_7056433) baseStart_7056433 baseEnd_7056433 := by
    simpa [prefixWord, tailWord_7056433, baseEnd_7056433] using wordTrace_append hprefix tailTrace_7056433
  have hstable : (prefixWord ++ tailWord_7056433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056433).length < 2 ^ (prefixWord ++ tailWord_7056433).sum := by decide
  have hdescent : baseEnd_7056433 < baseStart_7056433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056473 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 1, 5, 5]
def baseStart_7056473 : Nat := 118140960795 + 7056473 * 2 ^ 59
def prefixEnd_7056473 : Nat := 4983230072969 + 3 ^ 40 * 7056473 * 2
def baseEnd_7056473 : Nat := 3623362374474075250635377

theorem tailTrace_7056473 : CollatzResearch.WordTrace tailWord_7056473 prefixEnd_7056473 3623362374474075250635377 := by
  unfold tailWord_7056473
  simp only [CollatzResearch.WordTrace]
  refine ⟨257370714164610945486646073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171580476109740630324430715 257370714164610945486646073)
  ·
    refine ⟨193028035623458209114984555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257370714164610945486646073 193028035623458209114984555)
    ·
      refine ⟨289542053435187313672476833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193028035623458209114984555 289542053435187313672476833)
      ·
        refine ⟨217156540076390485254357625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289542053435187313672476833 217156540076390485254357625)
        ·
          refine ⟨162867405057292863940768219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217156540076390485254357625 162867405057292863940768219)
          ·
            refine ⟨244301107585939295911152329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162867405057292863940768219 244301107585939295911152329)
            ·
              refine ⟨183225830689454471933364247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244301107585939295911152329 183225830689454471933364247)
              ·
                refine ⟨274838746034181707900046371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183225830689454471933364247 274838746034181707900046371)
                ·
                  refine ⟨412258119051272561850069557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274838746034181707900046371 412258119051272561850069557)
                  ·
                    refine ⟨38649198661056802673444021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 412258119051272561850069557 38649198661056802673444021)
                    ·
                      refine ⟨3623362374474075250635377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38649198661056802673444021 3623362374474075250635377)
                      ·
                        rfl

theorem cell23_7056473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_7056473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056473 prefixEnd_7056473 := by exact prefixLift 7056473
  have htrace : WordTrace (prefixWord ++ tailWord_7056473) baseStart_7056473 baseEnd_7056473 := by
    simpa [prefixWord, tailWord_7056473, baseEnd_7056473] using wordTrace_append hprefix tailTrace_7056473
  have hstable : (prefixWord ++ tailWord_7056473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056473).length < 2 ^ (prefixWord ++ tailWord_7056473).sum := by decide
  have hdescent : baseEnd_7056473 < baseStart_7056473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056547 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 4, 3, 2]
def baseStart_7056547 : Nat := 118140960795 + 7056547 * 2 ^ 59
def prefixEnd_7056547 : Nat := 4983230072969 + 3 ^ 40 * 7056547 * 2
def baseEnd_7056547 : Nat := 3623400372042507961110037

theorem tailTrace_7056547 : CollatzResearch.WordTrace tailWord_7056547 prefixEnd_7056547 3623400372042507961110037 := by
  unfold tailWord_7056547
  simp only [CollatzResearch.WordTrace]
  refine ⟨257373413166342856124839895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171582275444228570749893263 257373413166342856124839895)
  ·
    refine ⟨386060119749514284187259843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257373413166342856124839895 386060119749514284187259843)
    ·
      refine ⟨579090179624271426280889765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386060119749514284187259843 579090179624271426280889765)
      ·
        refine ⟨108579408679550892427666831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 579090179624271426280889765 108579408679550892427666831)
        ·
          refine ⟨162869113019326338641500247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108579408679550892427666831 162869113019326338641500247)
          ·
            refine ⟨244303669528989507962250371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162869113019326338641500247 244303669528989507962250371)
            ·
              refine ⟨366455504293484261943375557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244303669528989507962250371 366455504293484261943375557)
              ·
                refine ⟨68710407055028299114382917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366455504293484261943375557 68710407055028299114382917)
                ·
                  refine ⟨12883201322817806083946797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68710407055028299114382917 12883201322817806083946797)
                  ·
                    refine ⟨4831200496056677281480049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12883201322817806083946797 4831200496056677281480049)
                    ·
                      refine ⟨3623400372042507961110037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4831200496056677281480049 3623400372042507961110037)
                      ·
                        rfl

theorem cell23_7056547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_7056547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056547 prefixEnd_7056547 := by exact prefixLift 7056547
  have htrace : WordTrace (prefixWord ++ tailWord_7056547) baseStart_7056547 baseEnd_7056547 := by
    simpa [prefixWord, tailWord_7056547, baseEnd_7056547] using wordTrace_append hprefix tailTrace_7056547
  have hstable : (prefixWord ++ tailWord_7056547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056547).length < 2 ^ (prefixWord ++ tailWord_7056547).sum := by decide
  have hdescent : baseEnd_7056547 < baseStart_7056547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056574 : List Nat := [4, 2, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_7056574 : Nat := 118140960795 + 7056574 * 2 ^ 59
def prefixEnd_7056574 : Nat := 4983230072969 + 3 ^ 40 * 7056574 * 2
def baseEnd_7056574 : Nat := 1207804745340059785157471

theorem tailTrace_7056574 : CollatzResearch.WordTrace tailWord_7056574 prefixEnd_7056574 1207804745340059785157471 := by
  unfold tailWord_7056574
  simp only [CollatzResearch.WordTrace]
  refine ⟨32171799742155629967009097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171582931958163359824048517 32171799742155629967009097)
  ·
    refine ⟨24128849806616722475256823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32171799742155629967009097 24128849806616722475256823)
    ·
      refine ⟨36193274709925083712885235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24128849806616722475256823 36193274709925083712885235)
      ·
        refine ⟨54289912064887625569327853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36193274709925083712885235 54289912064887625569327853)
        ·
          refine ⟨20358717024332859588497945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54289912064887625569327853 20358717024332859588497945)
          ·
            refine ⟨15269037768249644691373459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20358717024332859588497945 15269037768249644691373459)
            ·
              refine ⟨22903556652374467037060189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15269037768249644691373459 22903556652374467037060189)
              ·
                refine ⟨8588833744640425138897571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22903556652374467037060189 8588833744640425138897571)
                ·
                  refine ⟨12883250616960637708346357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8588833744640425138897571 12883250616960637708346357)
                  ·
                    refine ⟨1207804745340059785157471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12883250616960637708346357 1207804745340059785157471)
                    ·
                      rfl

theorem cell23_7056574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_7056574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056574 prefixEnd_7056574 := by exact prefixLift 7056574
  have htrace : WordTrace (prefixWord ++ tailWord_7056574) baseStart_7056574 baseEnd_7056574 := by
    simpa [prefixWord, tailWord_7056574, baseEnd_7056574] using wordTrace_append hprefix tailTrace_7056574
  have hstable : (prefixWord ++ tailWord_7056574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056574).length < 2 ^ (prefixWord ++ tailWord_7056574).sum := by decide
  have hdescent : baseEnd_7056574 < baseStart_7056574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056578 : List Nat := [3, 5, 1, 1, 2, 2, 1, 2, 6]
def baseStart_7056578 : Nat := 118140960795 + 7056578 * 2 ^ 59
def prefixEnd_7056578 : Nat := 4983230072969 + 3 ^ 40 * 7056578 * 2
def baseEnd_7056578 : Nat := 402601809993644148869155

theorem tailTrace_7056578 : CollatzResearch.WordTrace tailWord_7056578 prefixEnd_7056578 402601809993644148869155 := by
  unfold tailWord_7056578
  simp only [CollatzResearch.WordTrace]
  refine ⟨64343635957307637104804597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171583029219487032279478925 64343635957307637104804597)
  ·
    refine ⟨6032215870997590978575431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64343635957307637104804597 6032215870997590978575431)
    ·
      refine ⟨9048323806496386467863147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6032215870997590978575431 9048323806496386467863147)
      ·
        refine ⟨13572485709744579701794721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9048323806496386467863147 13572485709744579701794721)
        ·
          refine ⟨10179364282308434776346041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13572485709744579701794721 10179364282308434776346041)
          ·
            refine ⟨7634523211731326082259531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10179364282308434776346041 7634523211731326082259531)
            ·
              refine ⟨11451784817596989123389297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7634523211731326082259531 11451784817596989123389297)
              ·
                refine ⟨8588838613197741842541973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11451784817596989123389297 8588838613197741842541973)
                ·
                  refine ⟨402601809993644148869155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8588838613197741842541973 402601809993644148869155)
                  ·
                    rfl

theorem cell23_7056578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_7056578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056578 prefixEnd_7056578 := by exact prefixLift 7056578
  have htrace : WordTrace (prefixWord ++ tailWord_7056578) baseStart_7056578 baseEnd_7056578 := by
    simpa [prefixWord, tailWord_7056578, baseEnd_7056578] using wordTrace_append hprefix tailTrace_7056578
  have hstable : (prefixWord ++ tailWord_7056578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056578).length < 2 ^ (prefixWord ++ tailWord_7056578).sum := by decide
  have hdescent : baseEnd_7056578 < baseStart_7056578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056587 : List Nat := [1, 1, 1, 1, 3, 2, 2, 6, 2, 4]
def baseStart_7056587 : Nat := 118140960795 + 7056587 * 2 ^ 59
def prefixEnd_7056587 : Nat := 4983230072969 + 3 ^ 40 * 7056587 * 2
def baseEnd_7056587 : Nat := 1207806970422895934869951

theorem tailTrace_7056587 : CollatzResearch.WordTrace tailWord_7056587 prefixEnd_7056587 1207806970422895934869951 := by
  unfold tailWord_7056587
  simp only [CollatzResearch.WordTrace]
  refine ⟨257374872086197942956296015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171583248057465295304197343 257374872086197942956296015)
  ·
    refine ⟨386062308129296914434444023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257374872086197942956296015 386062308129296914434444023)
    ·
      refine ⟨579093462193945371651666035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386062308129296914434444023 579093462193945371651666035)
      ·
        refine ⟨868640193290918057477499053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579093462193945371651666035 868640193290918057477499053)
        ·
          refine ⟨325740072484094271554062145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 868640193290918057477499053 325740072484094271554062145)
          ·
            refine ⟨244305054363070703665546609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325740072484094271554062145 244305054363070703665546609)
            ·
              refine ⟨183228790772303027749159957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244305054363070703665546609 183228790772303027749159957)
              ·
                refine ⟨8588849567451704425741873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 183228790772303027749159957 8588849567451704425741873)
                ·
                  refine ⟨6441637175588778319306405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8588849567451704425741873 6441637175588778319306405)
                  ·
                    refine ⟨1207806970422895934869951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6441637175588778319306405 1207806970422895934869951)
                    ·
                      rfl

theorem cell23_7056587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 4].length) (baseStart_7056587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056587 prefixEnd_7056587 := by exact prefixLift 7056587
  have htrace : WordTrace (prefixWord ++ tailWord_7056587) baseStart_7056587 baseEnd_7056587 := by
    simpa [prefixWord, tailWord_7056587, baseEnd_7056587] using wordTrace_append hprefix tailTrace_7056587
  have hstable : (prefixWord ++ tailWord_7056587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056587).length < 2 ^ (prefixWord ++ tailWord_7056587).sum := by decide
  have hdescent : baseEnd_7056587 < baseStart_7056587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056597 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_7056597 : Nat := 118140960795 + 7056597 * 2 ^ 59
def prefixEnd_7056597 : Nat := 4983230072969 + 3 ^ 40 * 7056597 * 2
def baseEnd_7056597 : Nat := 3623426046075232765484807

theorem tailTrace_7056597 : CollatzResearch.WordTrace tailWord_7056597 prefixEnd_7056597 3623426046075232765484807 := by
  unfold tailWord_7056597
  simp only [CollatzResearch.WordTrace]
  refine ⟨257375236816161714664160045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171583491210774476442773363 257375236816161714664160045)
  ·
    refine ⟨96515713806060642999060017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257375236816161714664160045 96515713806060642999060017)
    ·
      refine ⟨72386785354545482249295013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96515713806060642999060017 72386785354545482249295013)
      ·
        refine ⟨13572522253977277921742815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72386785354545482249295013 13572522253977277921742815)
        ·
          refine ⟨20358783380965916882614223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13572522253977277921742815 20358783380965916882614223)
          ·
            refine ⟨30538175071448875323921335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20358783380965916882614223 30538175071448875323921335)
            ·
              refine ⟨45807262607173312985882003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30538175071448875323921335 45807262607173312985882003)
              ·
                refine ⟨68710893910759969478823005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45807262607173312985882003 68710893910759969478823005)
                ·
                  refine ⟨25766585216534988554558627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68710893910759969478823005 25766585216534988554558627)
                  ·
                    refine ⟨38649877824802482831837941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25766585216534988554558627 38649877824802482831837941)
                    ·
                      refine ⟨3623426046075232765484807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38649877824802482831837941 3623426046075232765484807)
                      ·
                        rfl

theorem cell23_7056597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_7056597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056597 prefixEnd_7056597 := by exact prefixLift 7056597
  have htrace : WordTrace (prefixWord ++ tailWord_7056597) baseStart_7056597 baseEnd_7056597 := by
    simpa [prefixWord, tailWord_7056597, baseEnd_7056597] using wordTrace_append hprefix tailTrace_7056597
  have hstable : (prefixWord ++ tailWord_7056597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056597).length < 2 ^ (prefixWord ++ tailWord_7056597).sum := by decide
  have hdescent : baseEnd_7056597 < baseStart_7056597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056607 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 4]
def baseStart_7056607 : Nat := 118140960795 + 7056607 * 2 ^ 59
def prefixEnd_7056607 : Nat := 4983230072969 + 3 ^ 40 * 7056607 * 2
def baseEnd_7056607 : Nat := 3623431180881777726359761

theorem tailTrace_7056607 : CollatzResearch.WordTrace tailWord_7056607 prefixEnd_7056607 3623431180881777726359761 := by
  unfold tailWord_7056607
  simp only [CollatzResearch.WordTrace]
  refine ⟨257375601546125486372024075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171583734364083657581349383 257375601546125486372024075)
  ·
    refine ⟨386063402319188229558036113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257375601546125486372024075 386063402319188229558036113)
    ·
      refine ⟨289547551739391172168527085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386063402319188229558036113 289547551739391172168527085)
      ·
        refine ⟨108580331902271689563197657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289547551739391172168527085 108580331902271689563197657)
        ·
          refine ⟨81435248926703767172398243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108580331902271689563197657 81435248926703767172398243)
          ·
            refine ⟨122152873390055650758597365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81435248926703767172398243 122152873390055650758597365)
            ·
              refine ⟨11451831880317717258618503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122152873390055650758597365 11451831880317717258618503)
              ·
                refine ⟨17177747820476575887927755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11451831880317717258618503 17177747820476575887927755)
                ·
                  refine ⟨25766621730714863831891633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17177747820476575887927755 25766621730714863831891633)
                  ·
                    refine ⟨19324966298036147873918725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25766621730714863831891633 19324966298036147873918725)
                    ·
                      refine ⟨3623431180881777726359761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19324966298036147873918725 3623431180881777726359761)
                      ·
                        rfl

theorem cell23_7056607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_7056607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056607 prefixEnd_7056607 := by exact prefixLift 7056607
  have htrace : WordTrace (prefixWord ++ tailWord_7056607) baseStart_7056607 baseEnd_7056607 := by
    simpa [prefixWord, tailWord_7056607, baseEnd_7056607] using wordTrace_append hprefix tailTrace_7056607
  have hstable : (prefixWord ++ tailWord_7056607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056607).length < 2 ^ (prefixWord ++ tailWord_7056607).sum := by decide
  have hdescent : baseEnd_7056607 < baseStart_7056607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056640 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 5]
def baseStart_7056640 : Nat := 118140960795 + 7056640 * 2 ^ 59
def prefixEnd_7056640 : Nat := 4983230072969 + 3 ^ 40 * 7056640 * 2
def baseEnd_7056640 : Nat := 3623448125743376097247109

theorem tailTrace_7056640 : CollatzResearch.WordTrace tailWord_7056640 prefixEnd_7056640 3623448125743376097247109 := by
  unfold tailWord_7056640
  simp only [CollatzResearch.WordTrace]
  refine ⟨128688402577502966503987687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171584536770003955338650249 128688402577502966503987687)
  ·
    refine ⟨193032603866254449755981531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128688402577502966503987687 193032603866254449755981531)
    ·
      refine ⟨289548905799381674633972297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193032603866254449755981531 289548905799381674633972297)
      ·
        refine ⟨217161679349536255975479223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289548905799381674633972297 217161679349536255975479223)
        ·
          refine ⟨325742519024304383963218835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217161679349536255975479223 325742519024304383963218835)
          ·
            refine ⟨488613778536456575944828253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325742519024304383963218835 488613778536456575944828253)
            ·
              refine ⟨183230166951171215979310595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 488613778536456575944828253 183230166951171215979310595)
              ·
                refine ⟨274845250426756823968965893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183230166951171215979310595 274845250426756823968965893)
                ·
                  refine ⟨51533484455016904494181105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 274845250426756823968965893 51533484455016904494181105)
                  ·
                    refine ⟨38650113341262678370635829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51533484455016904494181105 38650113341262678370635829)
                    ·
                      refine ⟨3623448125743376097247109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38650113341262678370635829 3623448125743376097247109)
                      ·
                        rfl

theorem cell23_7056640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_7056640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056640 prefixEnd_7056640 := by exact prefixLift 7056640
  have htrace : WordTrace (prefixWord ++ tailWord_7056640) baseStart_7056640 baseEnd_7056640 := by
    simpa [prefixWord, tailWord_7056640, baseEnd_7056640] using wordTrace_append hprefix tailTrace_7056640
  have hstable : (prefixWord ++ tailWord_7056640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056640).length < 2 ^ (prefixWord ++ tailWord_7056640).sum := by decide
  have hdescent : baseEnd_7056640 < baseStart_7056640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056671 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 3, 3, 2]
def baseStart_7056671 : Nat := 118140960795 + 7056671 * 2 ^ 59
def prefixEnd_7056671 : Nat := 4983230072969 + 3 ^ 40 * 7056671 * 2
def baseEnd_7056671 : Nat := 3623464043643665475959467

theorem tailTrace_7056671 : CollatzResearch.WordTrace tailWord_7056671 prefixEnd_7056671 3623464043643665475959467 := by
  unfold tailWord_7056671
  simp only [CollatzResearch.WordTrace]
  refine ⟨257377935817893625302353867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171585290545262416868235911 257377935817893625302353867)
  ·
    refine ⟨386066903726840437953530801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257377935817893625302353867 386066903726840437953530801)
    ·
      refine ⟨289550177795130328465148101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386066903726840437953530801 289550177795130328465148101)
      ·
        refine ⟨54290658336586936587215269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289550177795130328465148101 54290658336586936587215269)
        ·
          refine ⟨10179498438110050610102863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54290658336586936587215269 10179498438110050610102863)
          ·
            refine ⟨15269247657165075915154295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10179498438110050610102863 15269247657165075915154295)
            ·
              refine ⟨22903871485747613872731443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15269247657165075915154295 22903871485747613872731443)
              ·
                refine ⟨34355807228621420809097165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22903871485747613872731443 34355807228621420809097165)
                ·
                  refine ⟨12883427710733032803411437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34355807228621420809097165 12883427710733032803411437)
                  ·
                    refine ⟨4831285391524887301279289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12883427710733032803411437 4831285391524887301279289)
                    ·
                      refine ⟨3623464043643665475959467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4831285391524887301279289 3623464043643665475959467)
                      ·
                        rfl

theorem cell23_7056671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_7056671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056671 prefixEnd_7056671 := by exact prefixLift 7056671
  have htrace : WordTrace (prefixWord ++ tailWord_7056671) baseStart_7056671 baseEnd_7056671 := by
    simpa [prefixWord, tailWord_7056671, baseEnd_7056671] using wordTrace_append hprefix tailTrace_7056671
  have hstable : (prefixWord ++ tailWord_7056671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056671).length < 2 ^ (prefixWord ++ tailWord_7056671).sum := by decide
  have hdescent : baseEnd_7056671 < baseStart_7056671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056794 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3]
def baseStart_7056794 : Nat := 118140960795 + 7056794 * 2 ^ 59
def prefixEnd_7056794 : Nat := 4983230072969 + 3 ^ 40 * 7056794 * 2
def baseEnd_7056794 : Nat := 3623527201764168494721401

theorem tailTrace_7056794 : CollatzResearch.WordTrace tailWord_7056794 prefixEnd_7056794 3623527201764168494721401 := by
  unfold tailWord_7056794
  simp only [CollatzResearch.WordTrace]
  refine ⟨64345605499112004327270359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171588281330965344872720957 64345605499112004327270359)
  ·
    refine ⟨96518408248668006490905539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64345605499112004327270359 96518408248668006490905539)
    ·
      refine ⟨144777612373002009736358309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96518408248668006490905539 144777612373002009736358309)
      ·
        refine ⟨27145802319937876825567183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144777612373002009736358309 27145802319937876825567183)
        ·
          refine ⟨40718703479906815238350775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27145802319937876825567183 40718703479906815238350775)
          ·
            refine ⟨61078055219860222857526163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40718703479906815238350775 61078055219860222857526163)
            ·
              refine ⟨91617082829790334286289245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61078055219860222857526163 91617082829790334286289245)
              ·
                refine ⟨34356406061171375357358467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91617082829790334286289245 34356406061171375357358467)
                ·
                  refine ⟨51534609091757063036037701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34356406061171375357358467 51534609091757063036037701)
                  ·
                    refine ⟨9662739204704449319257069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51534609091757063036037701 9662739204704449319257069)
                    ·
                      refine ⟨3623527201764168494721401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9662739204704449319257069 3623527201764168494721401)
                      ·
                        rfl

theorem cell23_7056794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_7056794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056794 prefixEnd_7056794 := by exact prefixLift 7056794
  have htrace : WordTrace (prefixWord ++ tailWord_7056794) baseStart_7056794 baseEnd_7056794 := by
    simpa [prefixWord, tailWord_7056794, baseEnd_7056794] using wordTrace_append hprefix tailTrace_7056794
  have hstable : (prefixWord ++ tailWord_7056794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056794).length < 2 ^ (prefixWord ++ tailWord_7056794).sum := by decide
  have hdescent : baseEnd_7056794 < baseStart_7056794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056808 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_7056808 : Nat := 118140960795 + 7056808 * 2 ^ 59
def prefixEnd_7056808 : Nat := 4983230072969 + 3 ^ 40 * 7056808 * 2
def baseEnd_7056808 : Nat := 3623534390493331439946337

theorem tailTrace_7056808 : CollatzResearch.WordTrace tailWord_7056808 prefixEnd_7056808 3623534390493331439946337 := by
  unfold tailWord_7056808
  simp only [CollatzResearch.WordTrace]
  refine ⟨128691466309198648850045539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171588621745598198466727385 128691466309198648850045539)
  ·
    refine ⟨193037199463797973275068309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128691466309198648850045539 193037199463797973275068309)
    ·
      refine ⟨9048618724865529997268827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 193037199463797973275068309 9048618724865529997268827)
      ·
        refine ⟨13572928087298294995903241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9048618724865529997268827 13572928087298294995903241)
        ·
          refine ⟨10179696065473721246927431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13572928087298294995903241 10179696065473721246927431)
          ·
            refine ⟨15269544098210581870391147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10179696065473721246927431 15269544098210581870391147)
            ·
              refine ⟨22904316147315872805586721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15269544098210581870391147 22904316147315872805586721)
              ·
                refine ⟨17178237110486904604190041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22904316147315872805586721 17178237110486904604190041)
                ·
                  refine ⟨12883677832865178453142531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17178237110486904604190041 12883677832865178453142531)
                  ·
                    refine ⟨19325516749297767679713797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12883677832865178453142531 19325516749297767679713797)
                    ·
                      refine ⟨3623534390493331439946337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19325516749297767679713797 3623534390493331439946337)
                      ·
                        rfl

theorem cell23_7056808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_7056808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056808 prefixEnd_7056808 := by exact prefixLift 7056808
  have htrace : WordTrace (prefixWord ++ tailWord_7056808) baseStart_7056808 baseEnd_7056808 := by
    simpa [prefixWord, tailWord_7056808, baseEnd_7056808] using wordTrace_append hprefix tailTrace_7056808
  have hstable : (prefixWord ++ tailWord_7056808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056808).length < 2 ^ (prefixWord ++ tailWord_7056808).sum := by decide
  have hdescent : baseEnd_7056808 < baseStart_7056808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056887 : List Nat := [1, 1, 3, 1, 1, 1, 1, 14]
def baseStart_7056887 : Nat := 118140960795 + 7056887 * 2 ^ 59
def prefixEnd_7056887 : Nat := 4983230072969 + 3 ^ 40 * 7056887 * 2
def baseEnd_7056887 : Nat := 134206479832038393735499

theorem tailTrace_7056887 : CollatzResearch.WordTrace tailWord_7056887 prefixEnd_7056887 134206479832038393735499 := by
  unfold tailWord_7056887
  simp only [CollatzResearch.WordTrace]
  refine ⟨257385813985111094192216915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171590542656740729461477943 257385813985111094192216915)
  ·
    refine ⟨386078720977666641288325373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257385813985111094192216915 386078720977666641288325373)
    ·
      refine ⟨144779520366624990483122015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386078720977666641288325373 144779520366624990483122015)
      ·
        refine ⟨217169280549937485724683023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144779520366624990483122015 217169280549937485724683023)
        ·
          refine ⟨325753920824906228587024535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217169280549937485724683023 325753920824906228587024535)
          ·
            refine ⟨488630881237359342880536803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325753920824906228587024535 488630881237359342880536803)
            ·
              refine ⟨732946321856039014320805205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488630881237359342880536803 732946321856039014320805205)
              ·
                refine ⟨134206479832038393735499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 732946321856039014320805205 134206479832038393735499)
                ·
                  rfl

theorem cell23_7056887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 14].length) (baseStart_7056887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056887 prefixEnd_7056887 := by exact prefixLift 7056887
  have htrace : WordTrace (prefixWord ++ tailWord_7056887) baseStart_7056887 baseEnd_7056887 := by
    simpa [prefixWord, tailWord_7056887, baseEnd_7056887] using wordTrace_append hprefix tailTrace_7056887
  have hstable : (prefixWord ++ tailWord_7056887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056887).length < 2 ^ (prefixWord ++ tailWord_7056887).sum := by decide
  have hdescent : baseEnd_7056887 < baseStart_7056887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
