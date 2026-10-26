import V185TrunkScan20Chunk123

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_753406 : List Nat := [4, 2, 2, 1, 4, 7]
def baseStart_753406 : Nat := 118140960795 + 753406 * 2 ^ 59
def prefixEnd_753406 : Nat := 4983230072969 + 3 ^ 40 * 753406 * 2
def baseEnd_753406 : Nat := 12736112131074387794573

theorem tailTrace_753406 : CollatzResearch.WordTrace tailWord_753406 prefixEnd_753406 12736112131074387794573 := by
  unfold tailWord_753406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3434871788568276043231009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18319316205697472230565381 3434871788568276043231009)
  ·
    refine ⟨2576153841426207032423257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3434871788568276043231009 2576153841426207032423257)
    ·
      refine ⟨1932115381069655274317443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2576153841426207032423257 1932115381069655274317443)
      ·
        refine ⟨2898173071604482911476165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1932115381069655274317443 2898173071604482911476165)
        ·
          refine ⟨543407450925840545901781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2898173071604482911476165 543407450925840545901781)
          ·
            refine ⟨12736112131074387794573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 543407450925840545901781 12736112131074387794573)
            ·
              rfl

theorem cell20_753406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 7].length) (baseStart_753406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753406 prefixEnd_753406 := by exact prefixLift 753406
  have htrace : WordTrace (prefixWord ++ tailWord_753406) baseStart_753406 baseEnd_753406 := by
    simpa [prefixWord, tailWord_753406, baseEnd_753406] using wordTrace_append hprefix tailTrace_753406
  have hstable : (prefixWord ++ tailWord_753406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753406).length < 2 ^ (prefixWord ++ tailWord_753406).sum := by decide
  have hdescent : baseEnd_753406 < baseStart_753406 := by decide
  rcases family_descends (prefixWord ++ tailWord_753406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753441 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 6]
def baseStart_753441 : Nat := 118140960795 + 753441 * 2 ^ 59
def prefixEnd_753441 : Nat := 4983230072969 + 3 ^ 40 * 753441 * 2
def baseEnd_753441 : Nat := 343891002492703904286661

theorem tailTrace_753441 : CollatzResearch.WordTrace tailWord_753441 prefixEnd_753441 343891002492703904286661 := by
  unfold tailWord_753441
  simp only [CollatzResearch.WordTrace]
  refine ⟨27480250863419409323372177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18320167242279606215581451 27480250863419409323372177)
  ·
    refine ⟨20610188147564556992529133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27480250863419409323372177 20610188147564556992529133)
    ·
      refine ⟨7728820555336708872198425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20610188147564556992529133 7728820555336708872198425)
      ·
        refine ⟨5796615416502531654148819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7728820555336708872198425 5796615416502531654148819)
        ·
          refine ⟨8694923124753797481223229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5796615416502531654148819 8694923124753797481223229)
          ·
            refine ⟨3260596171782674055458711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8694923124753797481223229 3260596171782674055458711)
            ·
              refine ⟨4890894257674011083188067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3260596171782674055458711 4890894257674011083188067)
              ·
                refine ⟨7336341386511016624782101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4890894257674011083188067 7336341386511016624782101)
                ·
                  refine ⟨343891002492703904286661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7336341386511016624782101 343891002492703904286661)
                  ·
                    rfl

theorem cell20_753441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_753441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753441 prefixEnd_753441 := by exact prefixLift 753441
  have htrace : WordTrace (prefixWord ++ tailWord_753441) baseStart_753441 baseEnd_753441 := by
    simpa [prefixWord, tailWord_753441, baseEnd_753441] using wordTrace_append hprefix tailTrace_753441
  have hstable : (prefixWord ++ tailWord_753441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753441).length < 2 ^ (prefixWord ++ tailWord_753441).sum := by decide
  have hdescent : baseEnd_753441 < baseStart_753441 := by decide
  rcases family_descends (prefixWord ++ tailWord_753441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753444 : List Nat := [2, 3, 1, 3, 2, 2, 3, 4]
def baseStart_753444 : Nat := 118140960795 + 753444 * 2 ^ 59
def prefixEnd_753444 : Nat := 4983230072969 + 3 ^ 40 * 753444 * 2
def baseEnd_753444 : Nat := 114630790591483075728883

theorem tailTrace_753444 : CollatzResearch.WordTrace tailWord_753444 prefixEnd_753444 114630790591483075728883 := by
  unfold tailWord_753444
  simp only [CollatzResearch.WordTrace]
  refine ⟨13740180141204270417865693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18320240188272360557154257 13740180141204270417865693)
  ·
    refine ⟨5152567552951601406699635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13740180141204270417865693 5152567552951601406699635)
    ·
      refine ⟨7728851329427402110049453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5152567552951601406699635 7728851329427402110049453)
      ·
        refine ⟨2898319248535275791268545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7728851329427402110049453 2898319248535275791268545)
        ·
          refine ⟨2173739436401456843451409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2898319248535275791268545 2173739436401456843451409)
          ·
            refine ⟨1630304577301092632588557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2173739436401456843451409 1630304577301092632588557)
            ·
              refine ⟨611364216487909737220709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1630304577301092632588557 611364216487909737220709)
              ·
                refine ⟨114630790591483075728883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 611364216487909737220709 114630790591483075728883)
                ·
                  rfl

theorem cell20_753444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_753444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753444 prefixEnd_753444 := by exact prefixLift 753444
  have htrace : WordTrace (prefixWord ++ tailWord_753444) baseStart_753444 baseEnd_753444 := by
    simpa [prefixWord, tailWord_753444, baseEnd_753444] using wordTrace_append hprefix tailTrace_753444
  have hstable : (prefixWord ++ tailWord_753444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753444).length < 2 ^ (prefixWord ++ tailWord_753444).sum := by decide
  have hdescent : baseEnd_753444 < baseStart_753444 := by decide
  rcases family_descends (prefixWord ++ tailWord_753444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753455 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 7]
def baseStart_753455 : Nat := 118140960795 + 753455 * 2 ^ 59
def prefixEnd_753455 : Nat := 4983230072969 + 3 ^ 40 * 753455 * 2
def baseEnd_753455 : Nat := 343897392474182077819937

theorem tailTrace_753455 : CollatzResearch.WordTrace tailWord_753455 prefixEnd_753455 343897392474182077819937 := by
  unfold tailWord_753455
  simp only [CollatzResearch.WordTrace]
  refine ⟨27480761485368689714381819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18320507656912459809587879 27480761485368689714381819)
  ·
    refine ⟨41221142228053034571572729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27480761485368689714381819 41221142228053034571572729)
    ·
      refine ⟨30915856671039775928679547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41221142228053034571572729 30915856671039775928679547)
      ·
        refine ⟨46373785006559663893019321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30915856671039775928679547 46373785006559663893019321)
        ·
          refine ⟨34780338754919747919764491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46373785006559663893019321 34780338754919747919764491)
          ·
            refine ⟨52170508132379621879646737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34780338754919747919764491 52170508132379621879646737)
            ·
              refine ⟨39127881099284716409735053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52170508132379621879646737 39127881099284716409735053)
              ·
                refine ⟨14672955412231768653650645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39127881099284716409735053 14672955412231768653650645)
                ·
                  refine ⟨343897392474182077819937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14672955412231768653650645 343897392474182077819937)
                  ·
                    rfl

theorem cell20_753455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_753455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753455 prefixEnd_753455 := by exact prefixLift 753455
  have htrace : WordTrace (prefixWord ++ tailWord_753455) baseStart_753455 baseEnd_753455 := by
    simpa [prefixWord, tailWord_753455, baseEnd_753455] using wordTrace_append hprefix tailTrace_753455
  have hstable : (prefixWord ++ tailWord_753455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753455).length < 2 ^ (prefixWord ++ tailWord_753455).sum := by decide
  have hdescent : baseEnd_753455 < baseStart_753455 := by decide
  rcases family_descends (prefixWord ++ tailWord_753455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753479 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 4]
def baseStart_753479 : Nat := 118140960795 + 753479 * 2 ^ 59
def prefixEnd_753479 : Nat := 4983230072969 + 3 ^ 40 * 753479 * 2
def baseEnd_753479 : Nat := 343908346728144661019839

theorem tailTrace_753479 : CollatzResearch.WordTrace tailWord_753479 prefixEnd_753479 343908346728144661019839 := by
  unfold tailWord_753479
  simp only [CollatzResearch.WordTrace]
  refine ⟨27481636837281741813255491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18321091224854494542170327 27481636837281741813255491)
  ·
    refine ⟨41222455255922612719883237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27481636837281741813255491 41222455255922612719883237)
    ·
      refine ⟨7729210360485489884978107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41222455255922612719883237 7729210360485489884978107)
      ·
        refine ⟨11593815540728234827467161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7729210360485489884978107 11593815540728234827467161)
        ·
          refine ⟨8695361655546176120600371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11593815540728234827467161 8695361655546176120600371)
          ·
            refine ⟨13043042483319264180900557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8695361655546176120600371 13043042483319264180900557)
            ·
              refine ⟨4891140931244724067837709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13043042483319264180900557 4891140931244724067837709)
              ·
                refine ⟨1834177849216771525439141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4891140931244724067837709 1834177849216771525439141)
                ·
                  refine ⟨343908346728144661019839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1834177849216771525439141 343908346728144661019839)
                  ·
                    rfl

theorem cell20_753479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_753479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753479 prefixEnd_753479 := by exact prefixLift 753479
  have htrace : WordTrace (prefixWord ++ tailWord_753479) baseStart_753479 baseEnd_753479 := by
    simpa [prefixWord, tailWord_753479, baseEnd_753479] using wordTrace_append hprefix tailTrace_753479
  have hstable : (prefixWord ++ tailWord_753479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753479).length < 2 ^ (prefixWord ++ tailWord_753479).sum := by decide
  have hdescent : baseEnd_753479 < baseStart_753479 := by decide
  rcases family_descends (prefixWord ++ tailWord_753479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753485 : List Nat := [1, 6, 1, 2, 1, 2, 3, 1, 3]
def baseStart_753485 : Nat := 118140960795 + 753485 * 2 ^ 59
def prefixEnd_753485 : Nat := 4983230072969 + 3 ^ 40 * 753485 * 2
def baseEnd_753485 : Nat := 343911085291635306819815

theorem tailTrace_753485 : CollatzResearch.WordTrace tailWord_753485 prefixEnd_753485 343911085291635306819815 := by
  unfold tailWord_753485
  simp only [CollatzResearch.WordTrace]
  refine ⟨27481855675260004837973909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18321237116840003225315939 27481855675260004837973909)
  ·
    refine ⟨1288211984777812726780027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27481855675260004837973909 1288211984777812726780027)
    ·
      refine ⟨1932317977166719090170041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1288211984777812726780027 1932317977166719090170041)
      ·
        refine ⟨1449238482875039317627531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1932317977166719090170041 1449238482875039317627531)
        ·
          refine ⟨2173857724312558976441297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1449238482875039317627531 2173857724312558976441297)
          ·
            refine ⟨1630393293234419232330973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2173857724312558976441297 1630393293234419232330973)
            ·
              refine ⟨611397484962907212124115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1630393293234419232330973 611397484962907212124115)
              ·
                refine ⟨917096227444360818186173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 611397484962907212124115 917096227444360818186173)
                ·
                  refine ⟨343911085291635306819815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917096227444360818186173 343911085291635306819815)
                  ·
                    rfl

theorem cell20_753485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_753485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753485 prefixEnd_753485 := by exact prefixLift 753485
  have htrace : WordTrace (prefixWord ++ tailWord_753485) baseStart_753485 baseEnd_753485 := by
    simpa [prefixWord, tailWord_753485, baseEnd_753485] using wordTrace_append hprefix tailTrace_753485
  have hstable : (prefixWord ++ tailWord_753485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753485).length < 2 ^ (prefixWord ++ tailWord_753485).sum := by decide
  have hdescent : baseEnd_753485 < baseStart_753485 := by decide
  rcases family_descends (prefixWord ++ tailWord_753485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753503 : List Nat := [1, 1, 2, 3, 1, 4, 4, 4]
def baseStart_753503 : Nat := 118140960795 + 753503 * 2 ^ 59
def prefixEnd_753503 : Nat := 4983230072969 + 3 ^ 40 * 753503 * 2
def baseEnd_753503 : Nat := 114639766994035748073247

theorem tailTrace_753503 : CollatzResearch.WordTrace tailWord_753503 prefixEnd_753503 114639766994035748073247 := by
  unfold tailWord_753503
  simp only [CollatzResearch.WordTrace]
  refine ⟨27482512189194793912129163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18321674792796529274752775 27482512189194793912129163)
  ·
    refine ⟨41223768283792190868193745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27482512189194793912129163 41223768283792190868193745)
    ·
      refine ⟨30917826212844143151145309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41223768283792190868193745 30917826212844143151145309)
      ·
        refine ⟨11594184829816553681679491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30917826212844143151145309 11594184829816553681679491)
        ·
          refine ⟨17391277244724830522519237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11594184829816553681679491 17391277244724830522519237)
          ·
            refine ⟨3260864483385905722972357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17391277244724830522519237 3260864483385905722972357)
            ·
              refine ⟨611412090634857323057317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3260864483385905722972357 611412090634857323057317)
              ·
                refine ⟨114639766994035748073247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 611412090634857323057317 114639766994035748073247)
                ·
                  rfl

theorem cell20_753503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 4].length) (baseStart_753503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753503 prefixEnd_753503 := by exact prefixLift 753503
  have htrace : WordTrace (prefixWord ++ tailWord_753503) baseStart_753503 baseEnd_753503 := by
    simpa [prefixWord, tailWord_753503, baseEnd_753503] using wordTrace_append hprefix tailTrace_753503
  have hstable : (prefixWord ++ tailWord_753503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753503).length < 2 ^ (prefixWord ++ tailWord_753503).sum := by decide
  have hdescent : baseEnd_753503 < baseStart_753503 := by decide
  rcases family_descends (prefixWord ++ tailWord_753503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753517 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 6]
def baseStart_753517 : Nat := 118140960795 + 753517 * 2 ^ 59
def prefixEnd_753517 : Nat := 4983230072969 + 3 ^ 40 * 753517 * 2
def baseEnd_753517 : Nat := 343925690963585417753017

theorem tailTrace_753517 : CollatzResearch.WordTrace tailWord_753517 prefixEnd_753517 343925690963585417753017 := by
  unfold tailWord_753517
  simp only [CollatzResearch.WordTrace]
  refine ⟨27483022811144074303138805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18322015207429382868759203 27483022811144074303138805)
  ·
    refine ⟨2576533388544756965919263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27483022811144074303138805 2576533388544756965919263)
    ·
      refine ⟨3864800082817135448878895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2576533388544756965919263 3864800082817135448878895)
      ·
        refine ⟨5797200124225703173318343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3864800082817135448878895 5797200124225703173318343)
        ·
          refine ⟨8695800186338554759977515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5797200124225703173318343 8695800186338554759977515)
          ·
            refine ⟨13043700279507832139966273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8695800186338554759977515 13043700279507832139966273)
            ·
              refine ⟨9782775209630874104974705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13043700279507832139966273 9782775209630874104974705)
              ·
                refine ⟨7337081407223155578731029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9782775209630874104974705 7337081407223155578731029)
                ·
                  refine ⟨343925690963585417753017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7337081407223155578731029 343925690963585417753017)
                  ·
                    rfl

theorem cell20_753517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_753517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753517 prefixEnd_753517 := by exact prefixLift 753517
  have htrace : WordTrace (prefixWord ++ tailWord_753517) baseStart_753517 baseEnd_753517 := by
    simpa [prefixWord, tailWord_753517, baseEnd_753517] using wordTrace_append hprefix tailTrace_753517
  have hstable : (prefixWord ++ tailWord_753517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753517).length < 2 ^ (prefixWord ++ tailWord_753517).sum := by decide
  have hdescent : baseEnd_753517 < baseStart_753517 := by decide
  rcases family_descends (prefixWord ++ tailWord_753517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753589 : List Nat := [1, 3, 3, 2, 1, 3, 1, 4, 2]
def baseStart_753589 : Nat := 118140960795 + 753589 * 2 ^ 59
def prefixEnd_753589 : Nat := 4983230072969 + 3 ^ 40 * 753589 * 2
def baseEnd_753589 : Nat := 343958553725473167352723

theorem tailTrace_753589 : CollatzResearch.WordTrace tailWord_753589 prefixEnd_753589 343958553725473167352723 := by
  unfold tailWord_753589
  simp only [CollatzResearch.WordTrace]
  refine ⟨27485648866883230599759821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18323765911255487066506547 27485648866883230599759821)
  ·
    refine ⟨10307118325081211474909933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27485648866883230599759821 10307118325081211474909933)
    ·
      refine ⟨3865169371905454303091225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10307118325081211474909933 3865169371905454303091225)
      ·
        refine ⟨2898877028929090727318419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3865169371905454303091225 2898877028929090727318419)
        ·
          refine ⟨4348315543393636090977629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2898877028929090727318419 4348315543393636090977629)
          ·
            refine ⟨1630618328772613534116611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4348315543393636090977629 1630618328772613534116611)
            ·
              refine ⟨2445927493158920301174917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1630618328772613534116611 2445927493158920301174917)
              ·
                refine ⟨458611404967297556470297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2445927493158920301174917 458611404967297556470297)
                ·
                  refine ⟨343958553725473167352723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458611404967297556470297 343958553725473167352723)
                  ·
                    rfl

theorem cell20_753589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_753589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753589 prefixEnd_753589 := by exact prefixLift 753589
  have htrace : WordTrace (prefixWord ++ tailWord_753589) baseStart_753589 baseEnd_753589 := by
    simpa [prefixWord, tailWord_753589, baseEnd_753589] using wordTrace_append hprefix tailTrace_753589
  have hstable : (prefixWord ++ tailWord_753589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753589).length < 2 ^ (prefixWord ++ tailWord_753589).sum := by decide
  have hdescent : baseEnd_753589 < baseStart_753589 := by decide
  rcases family_descends (prefixWord ++ tailWord_753589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753593 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 4]
def baseStart_753593 : Nat := 118140960795 + 753593 * 2 ^ 59
def prefixEnd_753593 : Nat := 4983230072969 + 3 ^ 40 * 753593 * 2
def baseEnd_753593 : Nat := 343960379434466931219373

theorem tailTrace_753593 : CollatzResearch.WordTrace tailWord_753593 prefixEnd_753593 343960379434466931219373 := by
  unfold tailWord_753593
  simp only [CollatzResearch.WordTrace]
  refine ⟨27485794758868739282905433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18323863172579159521936955 27485794758868739282905433)
  ·
    refine ⟨20614346069151554462179075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27485794758868739282905433 20614346069151554462179075)
    ·
      refine ⟨30921519103727331693268613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20614346069151554462179075 30921519103727331693268613)
      ·
        refine ⟨5797784831948874692487865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30921519103727331693268613 5797784831948874692487865)
        ·
          refine ⟨4348338623961656019365899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5797784831948874692487865 4348338623961656019365899)
          ·
            refine ⟨6522507935942484029048849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4348338623961656019365899 6522507935942484029048849)
            ·
              refine ⟨4891880951956863021786637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6522507935942484029048849 4891880951956863021786637)
              ·
                refine ⟨1834455356983823633169989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4891880951956863021786637 1834455356983823633169989)
                ·
                  refine ⟨343960379434466931219373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1834455356983823633169989 343960379434466931219373)
                  ·
                    rfl

theorem cell20_753593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_753593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753593 prefixEnd_753593 := by exact prefixLift 753593
  have htrace : WordTrace (prefixWord ++ tailWord_753593) baseStart_753593 baseEnd_753593 := by
    simpa [prefixWord, tailWord_753593, baseEnd_753593] using wordTrace_append hprefix tailTrace_753593
  have hstable : (prefixWord ++ tailWord_753593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753593).length < 2 ^ (prefixWord ++ tailWord_753593).sum := by decide
  have hdescent : baseEnd_753593 < baseStart_753593 := by decide
  rcases family_descends (prefixWord ++ tailWord_753593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753607 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 7]
def baseStart_753607 : Nat := 118140960795 + 753607 * 2 ^ 59
def prefixEnd_753607 : Nat := 4983230072969 + 3 ^ 40 * 753607 * 2
def baseEnd_753607 : Nat := 343966769415945104752649

theorem tailTrace_753607 : CollatzResearch.WordTrace tailWord_753607 prefixEnd_753607 343966769415945104752649 := by
  unfold tailWord_753607
  simp only [CollatzResearch.WordTrace]
  refine ⟨27486305380818019673915075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18324203587212013115943383 27486305380818019673915075)
  ·
    refine ⟨41229458071227029510872613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27486305380818019673915075 41229458071227029510872613)
    ·
      refine ⟨7730523388355068033288615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41229458071227029510872613 7730523388355068033288615)
      ·
        refine ⟨11595785082532602049932923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7730523388355068033288615 11595785082532602049932923)
        ·
          refine ⟨17393677623798903074899385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11595785082532602049932923 17393677623798903074899385)
          ·
            refine ⟨13045258217849177306174539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17393677623798903074899385 13045258217849177306174539)
            ·
              refine ⟨19567887326773765959261809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13045258217849177306174539 19567887326773765959261809)
              ·
                refine ⟨14675915495080324469446357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19567887326773765959261809 14675915495080324469446357)
                ·
                  refine ⟨343966769415945104752649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14675915495080324469446357 343966769415945104752649)
                  ·
                    rfl

theorem cell20_753607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_753607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753607 prefixEnd_753607 := by exact prefixLift 753607
  have htrace : WordTrace (prefixWord ++ tailWord_753607) baseStart_753607 baseEnd_753607 := by
    simpa [prefixWord, tailWord_753607, baseEnd_753607] using wordTrace_append hprefix tailTrace_753607
  have hstable : (prefixWord ++ tailWord_753607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753607).length < 2 ^ (prefixWord ++ tailWord_753607).sum := by decide
  have hdescent : baseEnd_753607 < baseStart_753607 := by decide
  rcases family_descends (prefixWord ++ tailWord_753607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753634 : List Nat := [3, 3, 3, 1, 2, 1, 7]
def baseStart_753634 : Nat := 118140960795 + 753634 * 2 ^ 59
def prefixEnd_753634 : Nat := 4983230072969 + 3 ^ 40 * 753634 * 2
def baseEnd_753634 : Nat := 38219899216850334539171

theorem tailTrace_753634 : CollatzResearch.WordTrace tailWord_753634 prefixEnd_753634 38219899216850334539171 := by
  unfold tailWord_753634
  simp only [CollatzResearch.WordTrace]
  refine ⟨6871822537930050821286989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18324860101146802190098637 6871822537930050821286989)
  ·
    refine ⟨2576933451723769057982621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6871822537930050821286989 2576933451723769057982621)
    ·
      refine ⟨966350044396413396743483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2576933451723769057982621 966350044396413396743483)
      ·
        refine ⟨1449525066594620095115225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 966350044396413396743483 1449525066594620095115225)
        ·
          refine ⟨1087143799945965071336419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1449525066594620095115225 1087143799945965071336419)
          ·
            refine ⟨1630715699918947607004629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087143799945965071336419 1630715699918947607004629)
            ·
              refine ⟨38219899216850334539171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1630715699918947607004629 38219899216850334539171)
              ·
                rfl

theorem cell20_753634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 7].length) (baseStart_753634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753634 prefixEnd_753634 := by exact prefixLift 753634
  have htrace : WordTrace (prefixWord ++ tailWord_753634) baseStart_753634 baseEnd_753634 := by
    simpa [prefixWord, tailWord_753634, baseEnd_753634] using wordTrace_append hprefix tailTrace_753634
  have hstable : (prefixWord ++ tailWord_753634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753634).length < 2 ^ (prefixWord ++ tailWord_753634).sum := by decide
  have hdescent : baseEnd_753634 < baseStart_753634 := by decide
  rcases family_descends (prefixWord ++ tailWord_753634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753648 : List Nat := [2, 1, 1, 1, 3, 2, 4, 4, 2]
def baseStart_753648 : Nat := 118140960795 + 753648 * 2 ^ 59
def prefixEnd_753648 : Nat := 4983230072969 + 3 ^ 40 * 753648 * 2
def baseEnd_753648 : Nat := 343985482933131184385815

theorem tailTrace_753648 : CollatzResearch.WordTrace tailWord_753648 prefixEnd_753648 343985482933131184385815 := by
  unfold tailWord_753648
  simp only [CollatzResearch.WordTrace]
  refine ⟨13743900386834741838078799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18325200515779655784105065 13743900386834741838078799)
  ·
    refine ⟨20615850580252112757118199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13743900386834741838078799 20615850580252112757118199)
    ·
      refine ⟨30923775870378169135677299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20615850580252112757118199 30923775870378169135677299)
      ·
        refine ⟨46385663805567253703515949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30923775870378169135677299 46385663805567253703515949)
        ·
          refine ⟨17394623927087720138818481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46385663805567253703515949 17394623927087720138818481)
          ·
            refine ⟨13045967945315790104113861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17394623927087720138818481 13045967945315790104113861)
            ·
              refine ⟨2446118989746710644521349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13045967945315790104113861 2446118989746710644521349)
              ·
                refine ⟨458647310577508245847753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2446118989746710644521349 458647310577508245847753)
                ·
                  refine ⟨343985482933131184385815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458647310577508245847753 343985482933131184385815)
                  ·
                    rfl

theorem cell20_753648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 2].length) (baseStart_753648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753648 prefixEnd_753648 := by exact prefixLift 753648
  have htrace : WordTrace (prefixWord ++ tailWord_753648) baseStart_753648 baseEnd_753648 := by
    simpa [prefixWord, tailWord_753648, baseEnd_753648] using wordTrace_append hprefix tailTrace_753648
  have hstable : (prefixWord ++ tailWord_753648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753648).length < 2 ^ (prefixWord ++ tailWord_753648).sum := by decide
  have hdescent : baseEnd_753648 < baseStart_753648 := by decide
  rcases family_descends (prefixWord ++ tailWord_753648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753668 : List Nat := [2, 3, 2, 4, 2, 1, 2, 4]
def baseStart_753668 : Nat := 118140960795 + 753668 * 2 ^ 59
def prefixEnd_753668 : Nat := 4983230072969 + 3 ^ 40 * 753668 * 2
def baseEnd_753668 : Nat := 114664870492700001239689

theorem tailTrace_753668 : CollatzResearch.WordTrace tailWord_753668 prefixEnd_753668 114664870492700001239689 := by
  unfold tailWord_753668
  simp only [CollatzResearch.WordTrace]
  refine ⟨13744265116798513545942829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18325686822398018061257105 13744265116798513545942829)
  ·
    refine ⟨5154099418799442579728561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13744265116798513545942829 5154099418799442579728561)
    ·
      refine ⟨3865574564099581934796421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5154099418799442579728561 3865574564099581934796421)
      ·
        refine ⟨724795230768671612774329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3865574564099581934796421 724795230768671612774329)
        ·
          refine ⟨543596423076503709580747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724795230768671612774329 543596423076503709580747)
          ·
            refine ⟨815394634614755564371121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543596423076503709580747 815394634614755564371121)
            ·
              refine ⟨611545975961066673278341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815394634614755564371121 611545975961066673278341)
              ·
                refine ⟨114664870492700001239689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 611545975961066673278341 114664870492700001239689)
                ·
                  rfl

theorem cell20_753668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_753668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753668 prefixEnd_753668 := by exact prefixLift 753668
  have htrace : WordTrace (prefixWord ++ tailWord_753668) baseStart_753668 baseEnd_753668 := by
    simpa [prefixWord, tailWord_753668, baseEnd_753668] using wordTrace_append hprefix tailTrace_753668
  have hstable : (prefixWord ++ tailWord_753668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753668).length < 2 ^ (prefixWord ++ tailWord_753668).sum := by decide
  have hdescent : baseEnd_753668 < baseStart_753668 := by decide
  rcases family_descends (prefixWord ++ tailWord_753668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753669 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 4]
def baseStart_753669 : Nat := 118140960795 + 753669 * 2 ^ 59
def prefixEnd_753669 : Nat := 4983230072969 + 3 ^ 40 * 753669 * 2
def baseEnd_753669 : Nat := 343995067905348444685729

theorem tailTrace_753669 : CollatzResearch.WordTrace tailWord_753669 prefixEnd_753669 343995067905348444685729 := by
  unfold tailWord_753669
  simp only [CollatzResearch.WordTrace]
  refine ⟨27488566706593404262672061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18325711137728936175114707 27488566706593404262672061)
  ·
    refine ⟨10308212514972526598502023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27488566706593404262672061 10308212514972526598502023)
    ·
      refine ⟨15462318772458789897753035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10308212514972526598502023 15462318772458789897753035)
      ·
        refine ⟨23193478158688184846629553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15462318772458789897753035 23193478158688184846629553)
        ·
          refine ⟨17395108619016138634972165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23193478158688184846629553 17395108619016138634972165)
          ·
            refine ⟨3261582866065525994057281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17395108619016138634972165 3261582866065525994057281)
            ·
              refine ⟨2446187149549144495542961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3261582866065525994057281 2446187149549144495542961)
              ·
                refine ⟨1834640362161858371657221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2446187149549144495542961 1834640362161858371657221)
                ·
                  refine ⟨343995067905348444685729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1834640362161858371657221 343995067905348444685729)
                  ·
                    rfl

theorem cell20_753669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_753669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753669 prefixEnd_753669 := by exact prefixLift 753669
  have htrace : WordTrace (prefixWord ++ tailWord_753669) baseStart_753669 baseEnd_753669 := by
    simpa [prefixWord, tailWord_753669, baseEnd_753669] using wordTrace_append hprefix tailTrace_753669
  have hstable : (prefixWord ++ tailWord_753669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753669).length < 2 ^ (prefixWord ++ tailWord_753669).sum := by decide
  have hdescent : baseEnd_753669 < baseStart_753669 := by decide
  rcases family_descends (prefixWord ++ tailWord_753669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753676 : List Nat := [2, 2, 1, 2, 3, 1, 3, 6]
def baseStart_753676 : Nat := 118140960795 + 753676 * 2 ^ 59
def prefixEnd_753676 : Nat := 4983230072969 + 3 ^ 40 * 753676 * 2
def baseEnd_753676 : Nat := 114666087632029177150789

theorem tailTrace_753676 : CollatzResearch.WordTrace tailWord_753676 prefixEnd_753676 114666087632029177150789 := by
  unfold tailWord_753676
  simp only [CollatzResearch.WordTrace]
  refine ⟨13744411008784022229088441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18325881345045362972117921 13744411008784022229088441)
  ·
    refine ⟨10308308256588016671816331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13744411008784022229088441 10308308256588016671816331)
    ·
      refine ⟨15462462384882025007724497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10308308256588016671816331 15462462384882025007724497)
      ·
        refine ⟨11596846788661518755793373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15462462384882025007724497 11596846788661518755793373)
        ·
          refine ⟨4348817545748069533422515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11596846788661518755793373 4348817545748069533422515)
          ·
            refine ⟨6523226318622104300133773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4348817545748069533422515 6523226318622104300133773)
            ·
              refine ⟨2446209869483289112550165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6523226318622104300133773 2446209869483289112550165)
              ·
                refine ⟨114666087632029177150789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2446209869483289112550165 114666087632029177150789)
                ·
                  rfl

theorem cell20_753676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_753676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753676 prefixEnd_753676 := by exact prefixLift 753676
  have htrace : WordTrace (prefixWord ++ tailWord_753676) baseStart_753676 baseEnd_753676 := by
    simpa [prefixWord, tailWord_753676, baseEnd_753676] using wordTrace_append hprefix tailTrace_753676
  have hstable : (prefixWord ++ tailWord_753676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753676).length < 2 ^ (prefixWord ++ tailWord_753676).sum := by decide
  have hdescent : baseEnd_753676 < baseStart_753676 := by decide
  rcases family_descends (prefixWord ++ tailWord_753676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753683 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 5]
def baseStart_753683 : Nat := 118140960795 + 753683 * 2 ^ 59
def prefixEnd_753683 : Nat := 4983230072969 + 3 ^ 40 * 753683 * 2
def baseEnd_753683 : Nat := 344001457886826618219005

theorem tailTrace_753683 : CollatzResearch.WordTrace tailWord_753683 prefixEnd_753683 344001457886826618219005 := by
  unfold tailWord_753683
  simp only [CollatzResearch.WordTrace]
  refine ⟨27489077328542684653681703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18326051552361789769121135 27489077328542684653681703)
  ·
    refine ⟨41233615992814026980522555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27489077328542684653681703 41233615992814026980522555)
    ·
      refine ⟨61850423989221040470783833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41233615992814026980522555 61850423989221040470783833)
      ·
        refine ⟨46387817991915780353087875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61850423989221040470783833 46387817991915780353087875)
        ·
          refine ⟨69581726987873670529631813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46387817991915780353087875 69581726987873670529631813)
          ·
            refine ⟨13046573810226313224305965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69581726987873670529631813 13046573810226313224305965)
            ·
              refine ⟨4892465178834867459114737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13046573810226313224305965 4892465178834867459114737)
              ·
                refine ⟨3669348884126150594336053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4892465178834867459114737 3669348884126150594336053)
                ·
                  refine ⟨344001457886826618219005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3669348884126150594336053 344001457886826618219005)
                  ·
                    rfl

theorem cell20_753683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_753683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753683 prefixEnd_753683 := by exact prefixLift 753683
  have htrace : WordTrace (prefixWord ++ tailWord_753683) baseStart_753683 baseEnd_753683 := by
    simpa [prefixWord, tailWord_753683, baseEnd_753683] using wordTrace_append hprefix tailTrace_753683
  have hstable : (prefixWord ++ tailWord_753683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753683).length < 2 ^ (prefixWord ++ tailWord_753683).sum := by decide
  have hdescent : baseEnd_753683 < baseStart_753683 := by decide
  rcases family_descends (prefixWord ++ tailWord_753683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753693 : List Nat := [1, 4, 2, 2, 2, 3, 6]
def baseStart_753693 : Nat := 118140960795 + 753693 * 2 ^ 59
def prefixEnd_753693 : Nat := 4983230072969 + 3 ^ 40 * 753693 * 2
def baseEnd_753693 : Nat := 38222891351034558653959

theorem tailTrace_753693 : CollatzResearch.WordTrace tailWord_753693 prefixEnd_753693 38222891351034558653959 := by
  unfold tailWord_753693
  simp only [CollatzResearch.WordTrace]
  refine ⟨27489442058506456361545733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18326294705670970907697155 27489442058506456361545733)
  ·
    refine ⟨5154270385969960567789825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27489442058506456361545733 5154270385969960567789825)
    ·
      refine ⟨3865702789477470425842369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5154270385969960567789825 3865702789477470425842369)
      ·
        refine ⟨2899277092108102819381777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3865702789477470425842369 2899277092108102819381777)
        ·
          refine ⟨2174457819081077114536333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2899277092108102819381777 2174457819081077114536333)
          ·
            refine ⟨815421682155403917951125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2174457819081077114536333 815421682155403917951125)
            ·
              refine ⟨38222891351034558653959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 815421682155403917951125 38222891351034558653959)
              ·
                rfl

theorem cell20_753693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 6].length) (baseStart_753693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753693 prefixEnd_753693 := by exact prefixLift 753693
  have htrace : WordTrace (prefixWord ++ tailWord_753693) baseStart_753693 baseEnd_753693 := by
    simpa [prefixWord, tailWord_753693, baseEnd_753693] using wordTrace_append hprefix tailTrace_753693
  have hstable : (prefixWord ++ tailWord_753693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753693).length < 2 ^ (prefixWord ++ tailWord_753693).sum := by decide
  have hdescent : baseEnd_753693 < baseStart_753693 := by decide
  rcases family_descends (prefixWord ++ tailWord_753693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753714 : List Nat := [3, 2, 1, 1, 2, 3, 1, 7]
def baseStart_753714 : Nat := 118140960795 + 753714 * 2 ^ 59
def prefixEnd_753714 : Nat := 4983230072969 + 3 ^ 40 * 753714 * 2
def baseEnd_753714 : Nat := 114671869043842762728515

theorem tailTrace_753714 : CollatzResearch.WordTrace tailWord_753714 prefixEnd_753714 114671869043842762728515 := by
  unfold tailWord_753714
  simp only [CollatzResearch.WordTrace]
  refine ⟨6872551997857594237015049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18326805327620251298706797 6872551997857594237015049)
  ·
    refine ⟨5154413998393195677761287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6872551997857594237015049 5154413998393195677761287)
    ·
      refine ⟨7731620997589793516641931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5154413998393195677761287 7731620997589793516641931)
      ·
        refine ⟨11597431496384690274962897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7731620997589793516641931 11597431496384690274962897)
        ·
          refine ⟨8698073622288517706222173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11597431496384690274962897 8698073622288517706222173)
          ·
            refine ⟨3261777608358194139833315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8698073622288517706222173 3261777608358194139833315)
            ·
              refine ⟨4892666412537291209749973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3261777608358194139833315 4892666412537291209749973)
              ·
                refine ⟨114671869043842762728515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4892666412537291209749973 114671869043842762728515)
                ·
                  rfl

theorem cell20_753714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_753714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753714 prefixEnd_753714 := by exact prefixLift 753714
  have htrace : WordTrace (prefixWord ++ tailWord_753714) baseStart_753714 baseEnd_753714 := by
    simpa [prefixWord, tailWord_753714, baseEnd_753714] using wordTrace_append hprefix tailTrace_753714
  have hstable : (prefixWord ++ tailWord_753714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753714).length < 2 ^ (prefixWord ++ tailWord_753714).sum := by decide
  have hdescent : baseEnd_753714 < baseStart_753714 := by decide
  rcases family_descends (prefixWord ++ tailWord_753714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753717 : List Nat := [1, 3, 3, 1, 1, 1, 6, 1, 3]
def baseStart_753717 : Nat := 118140960795 + 753717 * 2 ^ 59
def prefixEnd_753717 : Nat := 4983230072969 + 3 ^ 40 * 753717 * 2
def baseEnd_753717 : Nat := 344016976413273611085533

theorem tailTrace_753717 : CollatzResearch.WordTrace tailWord_753717 prefixEnd_753717 344016976413273611085533 := by
  unfold tailWord_753717
  simp only [CollatzResearch.WordTrace]
  refine ⟨27490317410419508460419405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18326878273613005640279603 27490317410419508460419405)
  ·
    refine ⟨10308869028907315672657277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27490317410419508460419405 10308869028907315672657277)
    ·
      refine ⟨3865825885840243377246479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10308869028907315672657277 3865825885840243377246479)
      ·
        refine ⟨5798738828760365065869719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3865825885840243377246479 5798738828760365065869719)
        ·
          refine ⟨8698108243140547598804579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5798738828760365065869719 8698108243140547598804579)
          ·
            refine ⟨13047162364710821398206869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8698108243140547598804579 13047162364710821398206869)
            ·
              refine ⟨611585735845819753040947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13047162364710821398206869 611585735845819753040947)
              ·
                refine ⟨917378603768729629561421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 611585735845819753040947 917378603768729629561421)
                ·
                  refine ⟨344016976413273611085533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917378603768729629561421 344016976413273611085533)
                  ·
                    rfl

theorem cell20_753717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_753717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753717 prefixEnd_753717 := by exact prefixLift 753717
  have htrace : WordTrace (prefixWord ++ tailWord_753717) baseStart_753717 baseEnd_753717 := by
    simpa [prefixWord, tailWord_753717, baseEnd_753717] using wordTrace_append hprefix tailTrace_753717
  have hstable : (prefixWord ++ tailWord_753717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753717).length < 2 ^ (prefixWord ++ tailWord_753717).sum := by decide
  have hdescent : baseEnd_753717 < baseStart_753717 := by decide
  rcases family_descends (prefixWord ++ tailWord_753717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753741 : List Nat := [1, 6, 1, 1, 1, 1, 2, 5, 2]
def baseStart_753741 : Nat := 118140960795 + 753741 * 2 ^ 59
def prefixEnd_753741 : Nat := 4983230072969 + 3 ^ 40 * 753741 * 2
def baseEnd_753741 : Nat := 344027930667236194285435

theorem tailTrace_753741 : CollatzResearch.WordTrace tailWord_753741 prefixEnd_753741 344027930667236194285435 := by
  unfold tailWord_753741
  simp only [CollatzResearch.WordTrace]
  refine ⟨27491192762332560559293077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18327461841555040372862051 27491192762332560559293077)
  ·
    refine ⟨1288649660734338776216863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27491192762332560559293077 1288649660734338776216863)
    ·
      refine ⟨1932974491101508164325295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1288649660734338776216863 1932974491101508164325295)
      ·
        refine ⟨2899461736652262246487943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1932974491101508164325295 2899461736652262246487943)
        ·
          refine ⟨4349192604978393369731915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2899461736652262246487943 4349192604978393369731915)
          ·
            refine ⟨6523788907467590054597873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4349192604978393369731915 6523788907467590054597873)
            ·
              refine ⟨4892841680600692540948405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6523788907467590054597873 4892841680600692540948405)
              ·
                refine ⟨458703907556314925713913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4892841680600692540948405 458703907556314925713913)
                ·
                  refine ⟨344027930667236194285435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458703907556314925713913 344027930667236194285435)
                  ·
                    rfl

theorem cell20_753741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_753741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753741 prefixEnd_753741 := by exact prefixLift 753741
  have htrace : WordTrace (prefixWord ++ tailWord_753741) baseStart_753741 baseEnd_753741 := by
    simpa [prefixWord, tailWord_753741, baseEnd_753741] using wordTrace_append hprefix tailTrace_753741
  have hstable : (prefixWord ++ tailWord_753741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753741).length < 2 ^ (prefixWord ++ tailWord_753741).sum := by decide
  have hdescent : baseEnd_753741 < baseStart_753741 := by decide
  rcases family_descends (prefixWord ++ tailWord_753741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753776 : List Nat := [2, 1, 1, 1, 5, 2, 2, 3, 3]
def baseStart_753776 : Nat := 118140960795 + 753776 * 2 ^ 59
def prefixEnd_753776 : Nat := 4983230072969 + 3 ^ 40 * 753776 * 2
def baseEnd_753776 : Nat := 344043905620931628118625

theorem tailTrace_753776 : CollatzResearch.WordTrace tailWord_753776 prefixEnd_753776 344043905620931628118625 := by
  unfold tailWord_753776
  simp only [CollatzResearch.WordTrace]
  refine ⟨13746234658602880768408591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18328312878137174357878121 13746234658602880768408591)
  ·
    refine ⟨20619351987904321152612887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13746234658602880768408591 20619351987904321152612887)
    ·
      refine ⟨30929027981856481728919331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20619351987904321152612887 30929027981856481728919331)
      ·
        refine ⟨46393541972784722593378997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30929027981856481728919331 46393541972784722593378997)
        ·
          refine ⟨4349394559948567743129281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46393541972784722593378997 4349394559948567743129281)
          ·
            refine ⟨3262045919961425807346961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4349394559948567743129281 3262045919961425807346961)
            ·
              refine ⟨2446534439971069355510221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3262045919961425807346961 2446534439971069355510221)
              ·
                refine ⟨917450414989151008316333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2446534439971069355510221 917450414989151008316333)
                ·
                  refine ⟨344043905620931628118625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917450414989151008316333 344043905620931628118625)
                  ·
                    rfl

theorem cell20_753776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_753776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753776 prefixEnd_753776 := by exact prefixLift 753776
  have htrace : WordTrace (prefixWord ++ tailWord_753776) baseStart_753776 baseEnd_753776 := by
    simpa [prefixWord, tailWord_753776, baseEnd_753776] using wordTrace_append hprefix tailTrace_753776
  have hstable : (prefixWord ++ tailWord_753776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753776).length < 2 ^ (prefixWord ++ tailWord_753776).sum := by decide
  have hdescent : baseEnd_753776 < baseStart_753776 := by decide
  rcases family_descends (prefixWord ++ tailWord_753776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753783 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 4]
def baseStart_753783 : Nat := 118140960795 + 753783 * 2 ^ 59
def prefixEnd_753783 : Nat := 4983230072969 + 3 ^ 40 * 753783 * 2
def baseEnd_753783 : Nat := 344047100611670714885263

theorem tailTrace_753783 : CollatzResearch.WordTrace tailWord_753783 prefixEnd_753783 344047100611670714885263 := by
  unfold tailWord_753783
  simp only [CollatzResearch.WordTrace]
  refine ⟨27492724628180401732322003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18328483085453601154881335 27492724628180401732322003)
  ·
    refine ⟨41239086942270602598483005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27492724628180401732322003 41239086942270602598483005)
    ·
      refine ⟨15464657603351475974431127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41239086942270602598483005 15464657603351475974431127)
      ·
        refine ⟨23196986405027213961646691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15464657603351475974431127 23196986405027213961646691)
        ·
          refine ⟨34795479607540820942470037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23196986405027213961646691 34795479607540820942470037)
          ·
            refine ⟨1631038106603475981678283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34795479607540820942470037 1631038106603475981678283)
            ·
              refine ⟨2446557159905213972517425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631038106603475981678283 2446557159905213972517425)
              ·
                refine ⟨1834917869928910479388069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2446557159905213972517425 1834917869928910479388069)
                ·
                  refine ⟨344047100611670714885263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1834917869928910479388069 344047100611670714885263)
                  ·
                    rfl

theorem cell20_753783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_753783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753783 prefixEnd_753783 := by exact prefixLift 753783
  have htrace : WordTrace (prefixWord ++ tailWord_753783) baseStart_753783 baseEnd_753783 := by
    simpa [prefixWord, tailWord_753783, baseEnd_753783] using wordTrace_append hprefix tailTrace_753783
  have hstable : (prefixWord ++ tailWord_753783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753783).length < 2 ^ (prefixWord ++ tailWord_753783).sum := by decide
  have hdescent : baseEnd_753783 < baseStart_753783 := by decide
  rcases family_descends (prefixWord ++ tailWord_753783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753821 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 4]
def baseStart_753821 : Nat := 118140960795 + 753821 * 2 ^ 59
def prefixEnd_753821 : Nat := 4983230072969 + 3 ^ 40 * 753821 * 2
def baseEnd_753821 : Nat := 344064444847111471618441

theorem tailTrace_753821 : CollatzResearch.WordTrace tailWord_753821 prefixEnd_753821 344064444847111471618441 := by
  unfold tailWord_753821
  simp only [CollatzResearch.WordTrace]
  refine ⟨27494110602042734222205317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18329407068028489481470211 27494110602042734222205317)
  ·
    refine ⟨5155145737883012666663497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27494110602042734222205317 5155145737883012666663497)
    ·
      refine ⟨3866359303412259499997623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5155145737883012666663497 3866359303412259499997623)
      ·
        refine ⟨5799538955118389249996435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3866359303412259499997623 5799538955118389249996435)
        ·
          refine ⟨8699308432677583874994653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5799538955118389249996435 8699308432677583874994653)
          ·
            refine ⟨3262240662254093953122995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8699308432677583874994653 3262240662254093953122995)
            ·
              refine ⟨4893360993381140929684493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3262240662254093953122995 4893360993381140929684493)
              ·
                refine ⟨1835010372517927848631685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4893360993381140929684493 1835010372517927848631685)
                ·
                  refine ⟨344064444847111471618441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1835010372517927848631685 344064444847111471618441)
                  ·
                    rfl

theorem cell20_753821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_753821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753821 prefixEnd_753821 := by exact prefixLift 753821
  have htrace : WordTrace (prefixWord ++ tailWord_753821) baseStart_753821 baseEnd_753821 := by
    simpa [prefixWord, tailWord_753821, baseEnd_753821] using wordTrace_append hprefix tailTrace_753821
  have hstable : (prefixWord ++ tailWord_753821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753821).length < 2 ^ (prefixWord ++ tailWord_753821).sum := by decide
  have hdescent : baseEnd_753821 < baseStart_753821 := by decide
  rcases family_descends (prefixWord ++ tailWord_753821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753841 : List Nat := [1, 2, 2, 5, 3, 1, 2, 4]
def baseStart_753841 : Nat := 118140960795 + 753841 * 2 ^ 59
def prefixEnd_753841 : Nat := 4983230072969 + 3 ^ 40 * 753841 * 2
def baseEnd_753841 : Nat := 114691191130693430317231

theorem tailTrace_753841 : CollatzResearch.WordTrace tailWord_753841 prefixEnd_753841 114691191130693430317231 := by
  unfold tailWord_753841
  simp only [CollatzResearch.WordTrace]
  refine ⟨27494840061970277637933377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18329893374646851758622251 27494840061970277637933377)
  ·
    refine ⟨20621130046477708228450033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27494840061970277637933377 20621130046477708228450033)
    ·
      refine ⟨15465847534858281171337525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20621130046477708228450033 15465847534858281171337525)
      ·
        refine ⟨1449923206392963859812893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15465847534858281171337525 1449923206392963859812893)
        ·
          refine ⟨543721202397361447429835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1449923206392963859812893 543721202397361447429835)
          ·
            refine ⟨815581803596042171144753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543721202397361447429835 815581803596042171144753)
            ·
              refine ⟨611686352697031628358565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815581803596042171144753 611686352697031628358565)
              ·
                refine ⟨114691191130693430317231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 611686352697031628358565 114691191130693430317231)
                ·
                  rfl

theorem cell20_753841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 4].length) (baseStart_753841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753841 prefixEnd_753841 := by exact prefixLift 753841
  have htrace : WordTrace (prefixWord ++ tailWord_753841) baseStart_753841 baseEnd_753841 := by
    simpa [prefixWord, tailWord_753841, baseEnd_753841] using wordTrace_append hprefix tailTrace_753841
  have hstable : (prefixWord ++ tailWord_753841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753841).length < 2 ^ (prefixWord ++ tailWord_753841).sum := by decide
  have hdescent : baseEnd_753841 < baseStart_753841 := by decide
  rcases family_descends (prefixWord ++ tailWord_753841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753873 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 5]
def baseStart_753873 : Nat := 118140960795 + 753873 * 2 ^ 59
def prefixEnd_753873 : Nat := 4983230072969 + 3 ^ 40 * 753873 * 2
def baseEnd_753873 : Nat := 344088179064030401884895

theorem tailTrace_753873 : CollatzResearch.WordTrace tailWord_753873 prefixEnd_753873 344088179064030401884895 := by
  unfold tailWord_753873
  simp only [CollatzResearch.WordTrace]
  refine ⟨27496007197854347103098273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18330671465236231402065515 27496007197854347103098273)
  ·
    refine ⟨20622005398390760327323705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27496007197854347103098273 20622005398390760327323705)
    ·
      refine ⟨15466504048793070245492779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20622005398390760327323705 15466504048793070245492779)
      ·
        refine ⟨23199756073189605368239169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15466504048793070245492779 23199756073189605368239169)
        ·
          refine ⟨17399817054892204026179377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23199756073189605368239169 17399817054892204026179377)
          ·
            refine ⟨13049862791169153019634533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17399817054892204026179377 13049862791169153019634533)
            ·
              refine ⟨2446849273344216191181475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13049862791169153019634533 2446849273344216191181475)
              ·
                refine ⟨3670273910016324286772213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2446849273344216191181475 3670273910016324286772213)
                ·
                  refine ⟨344088179064030401884895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3670273910016324286772213 344088179064030401884895)
                  ·
                    rfl

theorem cell20_753873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_753873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753873 prefixEnd_753873 := by exact prefixLift 753873
  have htrace : WordTrace (prefixWord ++ tailWord_753873) baseStart_753873 baseEnd_753873 := by
    simpa [prefixWord, tailWord_753873, baseEnd_753873] using wordTrace_append hprefix tailTrace_753873
  have hstable : (prefixWord ++ tailWord_753873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753873).length < 2 ^ (prefixWord ++ tailWord_753873).sum := by decide
  have hdescent : baseEnd_753873 < baseStart_753873 := by decide
  rcases family_descends (prefixWord ++ tailWord_753873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753927 : List Nat := [1, 1, 4, 5, 1, 2, 2, 2, 2]
def baseStart_753927 : Nat := 118140960795 + 753927 * 2 ^ 59
def prefixEnd_753927 : Nat := 4983230072969 + 3 ^ 40 * 753927 * 2
def baseEnd_753927 : Nat := 344112826135446214084675

theorem tailTrace_753927 : CollatzResearch.WordTrace tailWord_753927 prefixEnd_753927 344112826135446214084675 := by
  unfold tailWord_753927
  simp only [CollatzResearch.WordTrace]
  refine ⟨27497976739658714325564035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18331984493105809550376023 27497976739658714325564035)
  ·
    refine ⟨41246965109488071488346053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27497976739658714325564035 41246965109488071488346053)
    ·
      refine ⟨7733805958029013404064885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41246965109488071488346053 7733805958029013404064885)
      ·
        refine ⟨725044308565220006631083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7733805958029013404064885 725044308565220006631083)
        ·
          refine ⟨1087566462847830009946625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725044308565220006631083 1087566462847830009946625)
          ·
            refine ⟨815674847135872507459969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1087566462847830009946625 815674847135872507459969)
            ·
              refine ⟨611756135351904380594977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815674847135872507459969 611756135351904380594977)
              ·
                refine ⟨458817101513928285446233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 611756135351904380594977 458817101513928285446233)
                ·
                  refine ⟨344112826135446214084675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458817101513928285446233 344112826135446214084675)
                  ·
                    rfl

theorem cell20_753927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 2].length) (baseStart_753927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753927 prefixEnd_753927 := by exact prefixLift 753927
  have htrace : WordTrace (prefixWord ++ tailWord_753927) baseStart_753927 baseEnd_753927 := by
    simpa [prefixWord, tailWord_753927, baseEnd_753927] using wordTrace_append hprefix tailTrace_753927
  have hstable : (prefixWord ++ tailWord_753927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753927).length < 2 ^ (prefixWord ++ tailWord_753927).sum := by decide
  have hdescent : baseEnd_753927 < baseStart_753927 := by decide
  rcases family_descends (prefixWord ++ tailWord_753927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753928 : List Nat := [2, 1, 3, 2, 3, 1, 1, 4, 3]
def baseStart_753928 : Nat := 118140960795 + 753928 * 2 ^ 59
def prefixEnd_753928 : Nat := 4983230072969 + 3 ^ 40 * 753928 * 2
def baseEnd_753928 : Nat := 344113282562694655051337

theorem tailTrace_753928 : CollatzResearch.WordTrace tailWord_753928 prefixEnd_753928 344113282562694655051337 := by
  unfold tailWord_753928
  simp only [CollatzResearch.WordTrace]
  refine ⟨13749006606327545748175219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18332008808436727664233625 13749006606327545748175219)
  ·
    refine ⟨20623509909491318622262829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13749006606327545748175219 20623509909491318622262829)
    ·
      refine ⟨7733816216059244483348561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20623509909491318622262829 7733816216059244483348561)
      ·
        refine ⟨5800362162044433362511421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7733816216059244483348561 5800362162044433362511421)
        ·
          refine ⟨2175135810766662510941783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5800362162044433362511421 2175135810766662510941783)
          ·
            refine ⟨3262703716149993766412675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175135810766662510941783 3262703716149993766412675)
            ·
              refine ⟨4894055574224990649619013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3262703716149993766412675 4894055574224990649619013)
              ·
                refine ⟨917635420167185746803565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4894055574224990649619013 917635420167185746803565)
                ·
                  refine ⟨344113282562694655051337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917635420167185746803565 344113282562694655051337)
                  ·
                    rfl

theorem cell20_753928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_753928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753928 prefixEnd_753928 := by exact prefixLift 753928
  have htrace : WordTrace (prefixWord ++ tailWord_753928) baseStart_753928 baseEnd_753928 := by
    simpa [prefixWord, tailWord_753928, baseEnd_753928] using wordTrace_append hprefix tailTrace_753928
  have hstable : (prefixWord ++ tailWord_753928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753928).length < 2 ^ (prefixWord ++ tailWord_753928).sum := by decide
  have hdescent : baseEnd_753928 < baseStart_753928 := by decide
  rcases family_descends (prefixWord ++ tailWord_753928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753969 : List Nat := [1, 2, 2, 3, 4, 1, 2, 3, 2]
def baseStart_753969 : Nat := 118140960795 + 753969 * 2 ^ 59
def prefixEnd_753969 : Nat := 4983230072969 + 3 ^ 40 * 753969 * 2
def baseEnd_753969 : Nat := 344131996079880734684503

theorem tailTrace_753969 : CollatzResearch.WordTrace tailWord_753969 prefixEnd_753969 344131996079880734684503 := by
  unfold tailWord_753969
  simp only [CollatzResearch.WordTrace]
  refine ⟨27499508605506555498592961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18333005737004370332395307 27499508605506555498592961)
  ·
    refine ⟨20624631454129916623944721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27499508605506555498592961 20624631454129916623944721)
    ·
      refine ⟨15468473590597437467958541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20624631454129916623944721 15468473590597437467958541)
      ·
        refine ⟨5800677596474039050484453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15468473590597437467958541 5800677596474039050484453)
        ·
          refine ⟨1087627049338882321965835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5800677596474039050484453 1087627049338882321965835)
          ·
            refine ⟨1631440574008323482948753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087627049338882321965835 1631440574008323482948753)
            ·
              refine ⟨1223580430506242612211565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1631440574008323482948753 1223580430506242612211565)
              ·
                refine ⟨458842661439840979579337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1223580430506242612211565 458842661439840979579337)
                ·
                  refine ⟨344131996079880734684503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458842661439840979579337 344131996079880734684503)
                  ·
                    rfl

theorem cell20_753969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 2].length) (baseStart_753969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_753969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_753969 prefixEnd_753969 := by exact prefixLift 753969
  have htrace : WordTrace (prefixWord ++ tailWord_753969) baseStart_753969 baseEnd_753969 := by
    simpa [prefixWord, tailWord_753969, baseEnd_753969] using wordTrace_append hprefix tailTrace_753969
  have hstable : (prefixWord ++ tailWord_753969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753969).length < 2 ^ (prefixWord ++ tailWord_753969).sum := by decide
  have hdescent : baseEnd_753969 < baseStart_753969 := by decide
  rcases family_descends (prefixWord ++ tailWord_753969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754045 : List Nat := [1, 4, 1, 1, 2, 4, 3, 2, 2]
def baseStart_754045 : Nat := 118140960795 + 754045 * 2 ^ 59
def prefixEnd_754045 : Nat := 4983230072969 + 3 ^ 40 * 754045 * 2
def baseEnd_754045 : Nat := 344166684550762248150859

theorem tailTrace_754045 : CollatzResearch.WordTrace tailWord_754045 prefixEnd_754045 344166684550762248150859 := by
  unfold tailWord_754045
  simp only [CollatzResearch.WordTrace]
  refine ⟨27502280553231220478359589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18334853702154146985573059 27502280553231220478359589)
  ·
    refine ⟨5156677603730853839692423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27502280553231220478359589 5156677603730853839692423)
    ·
      refine ⟨7735016405596280759538635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5156677603730853839692423 7735016405596280759538635)
      ·
        refine ⟨11602524608394421139307953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7735016405596280759538635 11602524608394421139307953)
        ·
          refine ⟨8701893456295815854480965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11602524608394421139307953 8701893456295815854480965)
          ·
            refine ⟨1631605023055465472715181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8701893456295815854480965 1631605023055465472715181)
            ·
              refine ⟨611851883645799552268193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1631605023055465472715181 611851883645799552268193)
              ·
                refine ⟨458888912734349664201145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 611851883645799552268193 458888912734349664201145)
                ·
                  refine ⟨344166684550762248150859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458888912734349664201145 344166684550762248150859)
                  ·
                    rfl

theorem cell20_754045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_754045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754045 prefixEnd_754045 := by exact prefixLift 754045
  have htrace : WordTrace (prefixWord ++ tailWord_754045) baseStart_754045 baseEnd_754045 := by
    simpa [prefixWord, tailWord_754045, baseEnd_754045] using wordTrace_append hprefix tailTrace_754045
  have hstable : (prefixWord ++ tailWord_754045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754045).length < 2 ^ (prefixWord ++ tailWord_754045).sum := by decide
  have hdescent : baseEnd_754045 < baseStart_754045 := by decide
  rcases family_descends (prefixWord ++ tailWord_754045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754056 : List Nat := [2, 1, 3, 3, 1, 1, 4, 5]
def baseStart_754056 : Nat := 118140960795 + 754056 * 2 ^ 59
def prefixEnd_754056 : Nat := 4983230072969 + 3 ^ 40 * 754056 * 2
def baseEnd_754056 : Nat := 114723901750165032928049

theorem tailTrace_754056 : CollatzResearch.WordTrace tailWord_754056 prefixEnd_754056 114723901750165032928049 := by
  unfold tailWord_754056
  simp only [CollatzResearch.WordTrace]
  refine ⟨13751340878095684678505011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18335121170794246238006681 13751340878095684678505011)
  ·
    refine ⟨20627011317143527017757517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13751340878095684678505011 20627011317143527017757517)
    ·
      refine ⟨7735129243928822631659069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20627011317143527017757517 7735129243928822631659069)
      ·
        refine ⟨2900673466473308486872151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7735129243928822631659069 2900673466473308486872151)
        ·
          refine ⟨4351010199709962730308227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2900673466473308486872151 4351010199709962730308227)
          ·
            refine ⟨6526515299564944095462341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4351010199709962730308227 6526515299564944095462341)
            ·
              refine ⟨1223721618668427017899189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6526515299564944095462341 1223721618668427017899189)
              ·
                refine ⟨114723901750165032928049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1223721618668427017899189 114723901750165032928049)
                ·
                  rfl

theorem cell20_754056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_754056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754056 prefixEnd_754056 := by exact prefixLift 754056
  have htrace : WordTrace (prefixWord ++ tailWord_754056) baseStart_754056 baseEnd_754056 := by
    simpa [prefixWord, tailWord_754056, baseEnd_754056] using wordTrace_append hprefix tailTrace_754056
  have hstable : (prefixWord ++ tailWord_754056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754056).length < 2 ^ (prefixWord ++ tailWord_754056).sum := by decide
  have hdescent : baseEnd_754056 < baseStart_754056 := by decide
  rcases family_descends (prefixWord ++ tailWord_754056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754059 : List Nat := [1, 1, 1, 1, 4, 6, 2, 1, 3]
def baseStart_754059 : Nat := 118140960795 + 754059 * 2 ^ 59
def prefixEnd_754059 : Nat := 4983230072969 + 3 ^ 40 * 754059 * 2
def baseEnd_754059 : Nat := 344173074532240421684135

theorem tailTrace_754059 : CollatzResearch.WordTrace tailWord_754059 prefixEnd_754059 344173074532240421684135 := by
  unfold tailWord_754059
  simp only [CollatzResearch.WordTrace]
  refine ⟨27502791175180500869369231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18335194116787000579579487 27502791175180500869369231)
  ·
    refine ⟨41254186762770751304053847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27502791175180500869369231 41254186762770751304053847)
    ·
      refine ⟨61881280144156126956080771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41254186762770751304053847 61881280144156126956080771)
      ·
        refine ⟨92821920216234190434121157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61881280144156126956080771 92821920216234190434121157)
        ·
          refine ⟨17404110040543910706397717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92821920216234190434121157 17404110040543910706397717)
          ·
            refine ⟨815817658150495814362393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17404110040543910706397717 815817658150495814362393)
            ·
              refine ⟨611863243612871860771795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815817658150495814362393 611863243612871860771795)
              ·
                refine ⟨917794865419307791157693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 611863243612871860771795 917794865419307791157693)
                ·
                  refine ⟨344173074532240421684135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917794865419307791157693 344173074532240421684135)
                  ·
                    rfl

theorem cell20_754059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 3].length) (baseStart_754059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754059 prefixEnd_754059 := by exact prefixLift 754059
  have htrace : WordTrace (prefixWord ++ tailWord_754059) baseStart_754059 baseEnd_754059 := by
    simpa [prefixWord, tailWord_754059, baseEnd_754059] using wordTrace_append hprefix tailTrace_754059
  have hstable : (prefixWord ++ tailWord_754059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754059).length < 2 ^ (prefixWord ++ tailWord_754059).sum := by decide
  have hdescent : baseEnd_754059 < baseStart_754059 := by decide
  rcases family_descends (prefixWord ++ tailWord_754059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754090 : List Nat := [3, 1, 6, 1, 1, 8]
def baseStart_754090 : Nat := 118140960795 + 754090 * 2 ^ 59
def prefixEnd_754090 : Nat := 4983230072969 + 3 ^ 40 * 754090 * 2
def baseEnd_754090 : Nat := 12747674954701558950025

theorem tailTrace_754090 : CollatzResearch.WordTrace tailWord_754090 prefixEnd_754090 12747674954701558950025 := by
  unfold tailWord_754090
  simp only [CollatzResearch.WordTrace]
  refine ⟨6875980459517048290936931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18335947892045462109165149 6875980459517048290936931)
  ·
    refine ⟨10313970689275572436405397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6875980459517048290936931 10313970689275572436405397)
    ·
      refine ⟨483467376059792457956503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10313970689275572436405397 483467376059792457956503)
      ·
        refine ⟨725201064089688686934755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483467376059792457956503 725201064089688686934755)
        ·
          refine ⟨1087801596134533030402133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725201064089688686934755 1087801596134533030402133)
          ·
            refine ⟨12747674954701558950025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1087801596134533030402133 12747674954701558950025)
            ·
              rfl

theorem cell20_754090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 8].length) (baseStart_754090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754090 prefixEnd_754090 := by exact prefixLift 754090
  have htrace : WordTrace (prefixWord ++ tailWord_754090) baseStart_754090 baseEnd_754090 := by
    simpa [prefixWord, tailWord_754090, baseEnd_754090] using wordTrace_append hprefix tailTrace_754090
  have hstable : (prefixWord ++ tailWord_754090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754090).length < 2 ^ (prefixWord ++ tailWord_754090).sum := by decide
  have hdescent : baseEnd_754090 < baseStart_754090 := by decide
  rcases family_descends (prefixWord ++ tailWord_754090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754163 : List Nat := [1, 1, 1, 2, 2, 2, 3, 6, 2]
def baseStart_754163 : Nat := 118140960795 + 754163 * 2 ^ 59
def prefixEnd_754163 : Nat := 4983230072969 + 3 ^ 40 * 754163 * 2
def baseEnd_754163 : Nat := 344220542966078282217043

theorem tailTrace_754163 : CollatzResearch.WordTrace tailWord_754163 prefixEnd_754163 344220542966078282217043 := by
  unfold tailWord_754163
  simp only [CollatzResearch.WordTrace]
  refine ⟨27506584366803726631155143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18337722911202484420770095 27506584366803726631155143)
  ·
    refine ⟨41259876550205589946732715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27506584366803726631155143 41259876550205589946732715)
    ·
      refine ⟨61889814825308384920099073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41259876550205589946732715 61889814825308384920099073)
      ·
        refine ⟨46417361118981288690074305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61889814825308384920099073 46417361118981288690074305)
        ·
          refine ⟨34813020839235966517555729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46417361118981288690074305 34813020839235966517555729)
          ·
            refine ⟨26109765629426974888166797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34813020839235966517555729 26109765629426974888166797)
            ·
              refine ⟨9791162111035115583062549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26109765629426974888166797 9791162111035115583062549)
              ·
                refine ⟨458960723954771042956057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9791162111035115583062549 458960723954771042956057)
                ·
                  refine ⟨344220542966078282217043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458960723954771042956057 344220542966078282217043)
                  ·
                    rfl

theorem cell20_754163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 2].length) (baseStart_754163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754163 prefixEnd_754163 := by exact prefixLift 754163
  have htrace : WordTrace (prefixWord ++ tailWord_754163) baseStart_754163 baseEnd_754163 := by
    simpa [prefixWord, tailWord_754163, baseEnd_754163] using wordTrace_append hprefix tailTrace_754163
  have hstable : (prefixWord ++ tailWord_754163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754163).length < 2 ^ (prefixWord ++ tailWord_754163).sum := by decide
  have hdescent : baseEnd_754163 < baseStart_754163 := by decide
  rcases family_descends (prefixWord ++ tailWord_754163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754187 : List Nat := [1, 1, 1, 1, 7, 3, 2, 4]
def baseStart_754187 : Nat := 118140960795 + 754187 * 2 ^ 59
def prefixEnd_754187 : Nat := 4983230072969 + 3 ^ 40 * 754187 * 2
def baseEnd_754187 : Nat := 114743832406680288472315

theorem tailTrace_754187 : CollatzResearch.WordTrace tailWord_754187 prefixEnd_754187 114743832406680288472315 := by
  unfold tailWord_754187
  simp only [CollatzResearch.WordTrace]
  refine ⟨27507459718716778730028815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18338306479144519153352543 27507459718716778730028815)
  ·
    refine ⟨41261189578075168095043223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27507459718716778730028815 41261189578075168095043223)
    ·
      refine ⟨61891784367112752142564835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41261189578075168095043223 61891784367112752142564835)
      ·
        refine ⟨92837676550669128213847253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61891784367112752142564835 92837676550669128213847253)
        ·
          refine ⟨2175883044156307692512045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 92837676550669128213847253 2175883044156307692512045)
          ·
            refine ⟨815956141558615384692017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2175883044156307692512045 815956141558615384692017)
            ·
              refine ⟨611967106168961538519013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815956141558615384692017 611967106168961538519013)
              ·
                refine ⟨114743832406680288472315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 611967106168961538519013 114743832406680288472315)
                ·
                  rfl

theorem cell20_754187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 4].length) (baseStart_754187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754187 prefixEnd_754187 := by exact prefixLift 754187
  have htrace : WordTrace (prefixWord ++ tailWord_754187) baseStart_754187 baseEnd_754187 := by
    simpa [prefixWord, tailWord_754187, baseEnd_754187] using wordTrace_append hprefix tailTrace_754187
  have hstable : (prefixWord ++ tailWord_754187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754187).length < 2 ^ (prefixWord ++ tailWord_754187).sum := by decide
  have hdescent : baseEnd_754187 < baseStart_754187 := by decide
  rcases family_descends (prefixWord ++ tailWord_754187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754218 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 4]
def baseStart_754218 : Nat := 118140960795 + 754218 * 2 ^ 59
def prefixEnd_754218 : Nat := 4983230072969 + 3 ^ 40 * 754218 * 2
def baseEnd_754218 : Nat := 344245646464742535383485

theorem tailTrace_754218 : CollatzResearch.WordTrace tailWord_754218 prefixEnd_754218 344245646464742535383485 := by
  unfold tailWord_754218
  simp only [CollatzResearch.WordTrace]
  refine ⟨6877147595401117756101827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18339060254402980682938205 6877147595401117756101827)
  ·
    refine ⟨10315721393101676634152741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6877147595401117756101827 10315721393101676634152741)
    ·
      refine ⟨1934197761206564368903639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10315721393101676634152741 1934197761206564368903639)
      ·
        refine ⟨2901296641809846553355459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1934197761206564368903639 2901296641809846553355459)
        ·
          refine ⟨4351944962714769830033189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2901296641809846553355459 4351944962714769830033189)
          ·
            refine ⟨815989680509019343131223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4351944962714769830033189 815989680509019343131223)
            ·
              refine ⟨1223984520763529014696835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815989680509019343131223 1223984520763529014696835)
              ·
                refine ⟨1835976781145293522045253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1223984520763529014696835 1835976781145293522045253)
                ·
                  refine ⟨344245646464742535383485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1835976781145293522045253 344245646464742535383485)
                  ·
                    rfl

theorem cell20_754218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_754218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754218 prefixEnd_754218 := by exact prefixLift 754218
  have htrace : WordTrace (prefixWord ++ tailWord_754218) baseStart_754218 baseEnd_754218 := by
    simpa [prefixWord, tailWord_754218, baseEnd_754218] using wordTrace_append hprefix tailTrace_754218
  have hstable : (prefixWord ++ tailWord_754218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754218).length < 2 ^ (prefixWord ++ tailWord_754218).sum := by decide
  have hdescent : baseEnd_754218 < baseStart_754218 := by decide
  rcases family_descends (prefixWord ++ tailWord_754218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754221 : List Nat := [1, 5, 4, 1, 1, 1, 2, 5]
def baseStart_754221 : Nat := 118140960795 + 754221 * 2 ^ 59
def prefixEnd_754221 : Nat := 4983230072969 + 3 ^ 40 * 754221 * 2
def baseEnd_754221 : Nat := 114749005248829286094491

theorem tailTrace_754221 : CollatzResearch.WordTrace tailWord_754221 prefixEnd_754221 114749005248829286094491 := by
  unfold tailWord_754221
  simp only [CollatzResearch.WordTrace]
  refine ⟨27508699800593602536766517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18339133200395735024511011 27508699800593602536766517)
  ·
    refine ⟨2578940606305650237821861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27508699800593602536766517 2578940606305650237821861)
    ·
      refine ⟨483551363682309419591599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2578940606305650237821861 483551363682309419591599)
      ·
        refine ⟨725327045523464129387399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483551363682309419591599 725327045523464129387399)
        ·
          refine ⟨1087990568285196194081099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725327045523464129387399 1087990568285196194081099)
          ·
            refine ⟨1631985852427794291121649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087990568285196194081099 1631985852427794291121649)
            ·
              refine ⟨1223989389320845718341237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1631985852427794291121649 1223989389320845718341237)
              ·
                refine ⟨114749005248829286094491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1223989389320845718341237 114749005248829286094491)
                ·
                  rfl

theorem cell20_754221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 5].length) (baseStart_754221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754221 prefixEnd_754221 := by exact prefixLift 754221
  have htrace : WordTrace (prefixWord ++ tailWord_754221) baseStart_754221 baseEnd_754221 := by
    simpa [prefixWord, tailWord_754221, baseEnd_754221] using wordTrace_append hprefix tailTrace_754221
  have hstable : (prefixWord ++ tailWord_754221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754221).length < 2 ^ (prefixWord ++ tailWord_754221).sum := by decide
  have hdescent : baseEnd_754221 < baseStart_754221 := by decide
  rcases family_descends (prefixWord ++ tailWord_754221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754228 : List Nat := [2, 5, 1, 3, 1, 1, 1, 3, 3]
def baseStart_754228 : Nat := 118140960795 + 754228 * 2 ^ 59
def prefixEnd_754228 : Nat := 4983230072969 + 3 ^ 40 * 754228 * 2
def baseEnd_754228 : Nat := 344250210737226945050111

theorem tailTrace_754228 : CollatzResearch.WordTrace tailWord_754228 prefixEnd_754228 344250210737226945050111 := by
  unfold tailWord_754228
  simp only [CollatzResearch.WordTrace]
  refine ⟨13754477555784121366135669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18339303407712161821514225 13754477555784121366135669)
  ·
    refine ⟨1289482270854761378075219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13754477555784121366135669 1289482270854761378075219)
    ·
      refine ⟨1934223406282142067112829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1289482270854761378075219 1934223406282142067112829)
      ·
        refine ⟨725333777355803275167311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1934223406282142067112829 725333777355803275167311)
        ·
          refine ⟨1088000666033704912750967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725333777355803275167311 1088000666033704912750967)
          ·
            refine ⟨1632000999050557369126451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088000666033704912750967 1632000999050557369126451)
            ·
              refine ⟨2448001498575836053689677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1632000999050557369126451 2448001498575836053689677)
              ·
                refine ⟨918000561965938520133629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2448001498575836053689677 918000561965938520133629)
                ·
                  refine ⟨344250210737226945050111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 918000561965938520133629 344250210737226945050111)
                  ·
                    rfl

theorem cell20_754228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_754228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754228 prefixEnd_754228 := by exact prefixLift 754228
  have htrace : WordTrace (prefixWord ++ tailWord_754228) baseStart_754228 baseEnd_754228 := by
    simpa [prefixWord, tailWord_754228, baseEnd_754228] using wordTrace_append hprefix tailTrace_754228
  have hstable : (prefixWord ++ tailWord_754228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754228).length < 2 ^ (prefixWord ++ tailWord_754228).sum := by decide
  have hdescent : baseEnd_754228 < baseStart_754228 := by decide
  rcases family_descends (prefixWord ++ tailWord_754228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754273 : List Nat := [1, 2, 3, 1, 1, 6, 2, 2, 2]
def baseStart_754273 : Nat := 118140960795 + 754273 * 2 ^ 59
def prefixEnd_754273 : Nat := 4983230072969 + 3 ^ 40 * 754273 * 2
def baseEnd_754273 : Nat := 344270749963406788549927

theorem tailTrace_754273 : CollatzResearch.WordTrace tailWord_754273 prefixEnd_754273 344270749963406788549927 := by
  unfold tailWord_754273
  simp only [CollatzResearch.WordTrace]
  refine ⟨27510596396405215417659473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18340397597603476945106315 27510596396405215417659473)
  ·
    refine ⟨20632947297303911563244605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27510596396405215417659473 20632947297303911563244605)
    ·
      refine ⟨7737355236488966836216727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20632947297303911563244605 7737355236488966836216727)
      ·
        refine ⟨11606032854733450254325091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7737355236488966836216727 11606032854733450254325091)
        ·
          refine ⟨17409049282100175381487637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11606032854733450254325091 17409049282100175381487637)
          ·
            refine ⟨816049185098445721007233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17409049282100175381487637 816049185098445721007233)
            ·
              refine ⟨612036888823834290755425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816049185098445721007233 612036888823834290755425)
              ·
                refine ⟨459027666617875718066569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612036888823834290755425 459027666617875718066569)
                ·
                  refine ⟨344270749963406788549927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459027666617875718066569 344270749963406788549927)
                  ·
                    rfl

theorem cell20_754273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 2].length) (baseStart_754273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754273 prefixEnd_754273 := by exact prefixLift 754273
  have htrace : WordTrace (prefixWord ++ tailWord_754273) baseStart_754273 baseEnd_754273 := by
    simpa [prefixWord, tailWord_754273, baseEnd_754273] using wordTrace_append hprefix tailTrace_754273
  have hstable : (prefixWord ++ tailWord_754273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754273).length < 2 ^ (prefixWord ++ tailWord_754273).sum := by decide
  have hdescent : baseEnd_754273 < baseStart_754273 := by decide
  rcases family_descends (prefixWord ++ tailWord_754273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754280 : List Nat := [2, 1, 4, 3, 3, 1, 1, 5]
def baseStart_754280 : Nat := 118140960795 + 754280 * 2 ^ 59
def prefixEnd_754280 : Nat := 4983230072969 + 3 ^ 40 * 754280 * 2
def baseEnd_754280 : Nat := 114757981651381958438855

theorem tailTrace_754280 : CollatzResearch.WordTrace tailWord_754280 prefixEnd_754280 114757981651381958438855 := by
  unfold tailWord_754280
  simp only [CollatzResearch.WordTrace]
  refine ⟨13755425853689927806582147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18340567804919903742109529 13755425853689927806582147)
  ·
    refine ⟨20633138780534891709873221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13755425853689927806582147 20633138780534891709873221)
    ·
      refine ⟨3868713521350292195601229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20633138780534891709873221 3868713521350292195601229)
      ·
        refine ⟨1450767570506359573350461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3868713521350292195601229 1450767570506359573350461)
        ·
          refine ⟨544037838939884840006423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1450767570506359573350461 544037838939884840006423)
          ·
            refine ⟨816056758409827260009635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544037838939884840006423 816056758409827260009635)
            ·
              refine ⟨1224085137614740890014453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816056758409827260009635 1224085137614740890014453)
              ·
                refine ⟨114757981651381958438855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1224085137614740890014453 114757981651381958438855)
                ·
                  rfl

theorem cell20_754280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_754280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754280 prefixEnd_754280 := by exact prefixLift 754280
  have htrace : WordTrace (prefixWord ++ tailWord_754280) baseStart_754280 baseEnd_754280 := by
    simpa [prefixWord, tailWord_754280, baseEnd_754280] using wordTrace_append hprefix tailTrace_754280
  have hstable : (prefixWord ++ tailWord_754280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754280).length < 2 ^ (prefixWord ++ tailWord_754280).sum := by decide
  have hdescent : baseEnd_754280 < baseStart_754280 := by decide
  rcases family_descends (prefixWord ++ tailWord_754280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754294 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_754294 : Nat := 118140960795 + 754294 * 2 ^ 59
def prefixEnd_754294 : Nat := 4983230072969 + 3 ^ 40 * 754294 * 2
def baseEnd_754294 : Nat := 344280334935624048849841

theorem tailTrace_754294 : CollatzResearch.WordTrace tailWord_754294 prefixEnd_754294 344280334935624048849841 := by
  unfold tailWord_754294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1719460145583071000260871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18340908219552757336115957 1719460145583071000260871)
  ·
    refine ⟨2579190218374606500391307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1719460145583071000260871 2579190218374606500391307)
    ·
      refine ⟨3868785327561909750586961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2579190218374606500391307 3868785327561909750586961)
      ·
        refine ⟨2901588995671432312940221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3868785327561909750586961 2901588995671432312940221)
        ·
          refine ⟨1088095873376787117352583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2901588995671432312940221 1088095873376787117352583)
          ·
            refine ⟨1632143810065180676028875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088095873376787117352583 1632143810065180676028875)
            ·
              refine ⟨2448215715097771014043313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1632143810065180676028875 2448215715097771014043313)
              ·
                refine ⟨1836161786323328260532485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2448215715097771014043313 1836161786323328260532485)
                ·
                  refine ⟨344280334935624048849841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1836161786323328260532485 344280334935624048849841)
                  ·
                    rfl

theorem cell20_754294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_754294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754294 prefixEnd_754294 := by exact prefixLift 754294
  have htrace : WordTrace (prefixWord ++ tailWord_754294) baseStart_754294 baseEnd_754294 := by
    simpa [prefixWord, tailWord_754294, baseEnd_754294] using wordTrace_append hprefix tailTrace_754294
  have hstable : (prefixWord ++ tailWord_754294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754294).length < 2 ^ (prefixWord ++ tailWord_754294).sum := by decide
  have hdescent : baseEnd_754294 < baseStart_754294 := by decide
  rcases family_descends (prefixWord ++ tailWord_754294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754301 : List Nat := [1, 4, 1, 1, 5, 1, 3, 4]
def baseStart_754301 : Nat := 118140960795 + 754301 * 2 ^ 59
def prefixEnd_754301 : Nat := 4983230072969 + 3 ^ 40 * 754301 * 2
def baseEnd_754301 : Nat := 114761176642121045205493

theorem tailTrace_754301 : CollatzResearch.WordTrace tailWord_754301 prefixEnd_754301 114761176642121045205493 := by
  unfold tailWord_754301
  simp only [CollatzResearch.WordTrace]
  refine ⟨27511617640303776199678757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18341078426869184133119171 27511617640303776199678757)
  ·
    refine ⟨5158428307556958037439767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27511617640303776199678757 5158428307556958037439767)
    ·
      refine ⟨7737642461335437056159651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5158428307556958037439767 7737642461335437056159651)
      ·
        refine ⟨11606463692003155584239477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7737642461335437056159651 11606463692003155584239477)
        ·
          refine ⟨1088105971125295836022451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11606463692003155584239477 1088105971125295836022451)
          ·
            refine ⟨1632158956687943754033677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088105971125295836022451 1632158956687943754033677)
            ·
              refine ⟨612059608757978907762629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1632158956687943754033677 612059608757978907762629)
              ·
                refine ⟨114761176642121045205493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 612059608757978907762629 114761176642121045205493)
                ·
                  rfl

theorem cell20_754301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 4].length) (baseStart_754301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754301 prefixEnd_754301 := by exact prefixLift 754301
  have htrace : WordTrace (prefixWord ++ tailWord_754301) baseStart_754301 baseEnd_754301 := by
    simpa [prefixWord, tailWord_754301, baseEnd_754301] using wordTrace_append hprefix tailTrace_754301
  have hstable : (prefixWord ++ tailWord_754301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754301).length < 2 ^ (prefixWord ++ tailWord_754301).sum := by decide
  have hdescent : baseEnd_754301 < baseStart_754301 := by decide
  rcases family_descends (prefixWord ++ tailWord_754301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754322 : List Nat := [3, 2, 3, 1, 2, 2, 7]
def baseStart_754322 : Nat := 118140960795 + 754322 * 2 ^ 59
def prefixEnd_754322 : Nat := 4983230072969 + 3 ^ 40 * 754322 * 2
def baseEnd_754322 : Nat := 38254790544286710657377

theorem tailTrace_754322 : CollatzResearch.WordTrace tailWord_754322 prefixEnd_754322 38254790544286710657377 := by
  unfold tailWord_754322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6878095893306924196548305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18341589048818464524128813 6878095893306924196548305)
  ·
    refine ⟨5158571919980193147411229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6878095893306924196548305 5158571919980193147411229)
    ·
      refine ⟨1934464469992572430279211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5158571919980193147411229 1934464469992572430279211)
      ·
        refine ⟨2901696704988858645418817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1934464469992572430279211 2901696704988858645418817)
        ·
          refine ⟨2176272528741643984064113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2901696704988858645418817 2176272528741643984064113)
          ·
            refine ⟨1632204396556232988048085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2176272528741643984064113 1632204396556232988048085)
            ·
              refine ⟨38254790544286710657377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1632204396556232988048085 38254790544286710657377)
              ·
                rfl

theorem cell20_754322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 7].length) (baseStart_754322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754322 prefixEnd_754322 := by exact prefixLift 754322
  have htrace : WordTrace (prefixWord ++ tailWord_754322) baseStart_754322 baseEnd_754322 := by
    simpa [prefixWord, tailWord_754322, baseEnd_754322] using wordTrace_append hprefix tailTrace_754322
  have hstable : (prefixWord ++ tailWord_754322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754322).length < 2 ^ (prefixWord ++ tailWord_754322).sum := by decide
  have hdescent : baseEnd_754322 < baseStart_754322 := by decide
  rcases family_descends (prefixWord ++ tailWord_754322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754332 : List Nat := [2, 2, 3, 2, 2, 1, 2, 4, 2]
def baseStart_754332 : Nat := 118140960795 + 754332 * 2 ^ 59
def prefixEnd_754332 : Nat := 4983230072969 + 3 ^ 40 * 754332 * 2
def baseEnd_754332 : Nat := 344297679171064805583019

theorem tailTrace_754332 : CollatzResearch.WordTrace tailWord_754332 prefixEnd_754332 344297679171064805583019 := by
  unfold tailWord_754332
  simp only [CollatzResearch.WordTrace]
  refine ⟨13756374151595734247028625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18341832202127645662704833 13756374151595734247028625)
  ·
    refine ⟨10317280613696800685271469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13756374151595734247028625 10317280613696800685271469)
    ·
      refine ⟨3868980230136300256976801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10317280613696800685271469 3868980230136300256976801)
      ·
        refine ⟨2901735172602225192732601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3868980230136300256976801 2901735172602225192732601)
        ·
          refine ⟨2176301379451668894549451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2901735172602225192732601 2176301379451668894549451)
          ·
            refine ⟨3264452069177503341824177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176301379451668894549451 3264452069177503341824177)
            ·
              refine ⟨2448339051883127506368133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3264452069177503341824177 2448339051883127506368133)
              ·
                refine ⟨459063572228086407444025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2448339051883127506368133 459063572228086407444025)
                ·
                  refine ⟨344297679171064805583019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459063572228086407444025 344297679171064805583019)
                  ·
                    rfl

theorem cell20_754332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_754332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754332 prefixEnd_754332 := by exact prefixLift 754332
  have htrace : WordTrace (prefixWord ++ tailWord_754332) baseStart_754332 baseEnd_754332 := by
    simpa [prefixWord, tailWord_754332, baseEnd_754332] using wordTrace_append hprefix tailTrace_754332
  have hstable : (prefixWord ++ tailWord_754332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754332).length < 2 ^ (prefixWord ++ tailWord_754332).sum := by decide
  have hdescent : baseEnd_754332 < baseStart_754332 := by decide
  rcases family_descends (prefixWord ++ tailWord_754332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754391 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 4]
def baseStart_754391 : Nat := 118140960795 + 754391 * 2 ^ 59
def prefixEnd_754391 : Nat := 4983230072969 + 3 ^ 40 * 754391 * 2
def baseEnd_754391 : Nat := 344324608378722822616111

theorem tailTrace_754391 : CollatzResearch.WordTrace tailWord_754391 prefixEnd_754391 344324608378722822616111 := by
  unfold tailWord_754391
  simp only [CollatzResearch.WordTrace]
  refine ⟨27514900209977721570455027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18343266806651814380303351 27514900209977721570455027)
  ·
    refine ⟨41272350314966582355682541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27514900209977721570455027 41272350314966582355682541)
    ·
      refine ⟨15477131368112468383380953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41272350314966582355682541 15477131368112468383380953)
      ·
        refine ⟨11607848526084351287535715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15477131368112468383380953 11607848526084351287535715)
        ·
          refine ⟨17411772789126526931303573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11607848526084351287535715 17411772789126526931303573)
          ·
            refine ⟨816176849490305949904855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17411772789126526931303573 816176849490305949904855)
            ·
              refine ⟨1224265274235458924857283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816176849490305949904855 1224265274235458924857283)
              ·
                refine ⟨1836397911353188387285925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1224265274235458924857283 1836397911353188387285925)
                ·
                  refine ⟨344324608378722822616111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1836397911353188387285925 344324608378722822616111)
                  ·
                    rfl

theorem cell20_754391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 4].length) (baseStart_754391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754391 prefixEnd_754391 := by exact prefixLift 754391
  have htrace : WordTrace (prefixWord ++ tailWord_754391) baseStart_754391 baseEnd_754391 := by
    simpa [prefixWord, tailWord_754391, baseEnd_754391] using wordTrace_append hprefix tailTrace_754391
  have hstable : (prefixWord ++ tailWord_754391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754391).length < 2 ^ (prefixWord ++ tailWord_754391).sum := by decide
  have hdescent : baseEnd_754391 < baseStart_754391 := by decide
  rcases family_descends (prefixWord ++ tailWord_754391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754395 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 10]
def baseStart_754395 : Nat := 118140960795 + 754395 * 2 ^ 59
def prefixEnd_754395 : Nat := 4983230072969 + 3 ^ 40 * 754395 * 2
def baseEnd_754395 : Nat := 344326434087716586482761

theorem tailTrace_754395 : CollatzResearch.WordTrace tailWord_754395 prefixEnd_754395 344326434087716586482761 := by
  unfold tailWord_754395
  simp only [CollatzResearch.WordTrace]
  refine ⟨27515046101963230253600639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18343364067975486835733759 27515046101963230253600639)
  ·
    refine ⟨41272569152944845380400959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27515046101963230253600639 41272569152944845380400959)
    ·
      refine ⟨61908853729417268070601439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41272569152944845380400959 61908853729417268070601439)
      ·
        refine ⟨92863280594125902105902159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61908853729417268070601439 92863280594125902105902159)
        ·
          refine ⟨139294920891188853158853239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92863280594125902105902159 139294920891188853158853239)
          ·
            refine ⟨208942381336783279738279859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139294920891188853158853239 208942381336783279738279859)
            ·
              refine ⟨313413572005174919607419789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208942381336783279738279859 313413572005174919607419789)
              ·
                refine ⟨117530089501940594852782421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313413572005174919607419789 117530089501940594852782421)
                ·
                  refine ⟨344326434087716586482761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 117530089501940594852782421 344326434087716586482761)
                  ·
                    rfl

theorem cell20_754395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_754395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754395 prefixEnd_754395 := by exact prefixLift 754395
  have htrace : WordTrace (prefixWord ++ tailWord_754395) baseStart_754395 baseEnd_754395 := by
    simpa [prefixWord, tailWord_754395, baseEnd_754395] using wordTrace_append hprefix tailTrace_754395
  have hstable : (prefixWord ++ tailWord_754395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754395).length < 2 ^ (prefixWord ++ tailWord_754395).sum := by decide
  have hdescent : baseEnd_754395 < baseStart_754395 := by decide
  rcases family_descends (prefixWord ++ tailWord_754395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754401 : List Nat := [1, 2, 3, 1, 4, 3, 2, 1, 3]
def baseStart_754401 : Nat := 118140960795 + 754401 * 2 ^ 59
def prefixEnd_754401 : Nat := 4983230072969 + 3 ^ 40 * 754401 * 2
def baseEnd_754401 : Nat := 344329172651207232282737

theorem tailTrace_754401 : CollatzResearch.WordTrace tailWord_754401 prefixEnd_754401 344329172651207232282737 := by
  unfold tailWord_754401
  simp only [CollatzResearch.WordTrace]
  refine ⟨27515264939941493278319057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18343509959960995518879371 27515264939941493278319057)
  ·
    refine ⟨20636448704956119958739293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27515264939941493278319057 20636448704956119958739293)
    ·
      refine ⟨7738668264358544984527235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20636448704956119958739293 7738668264358544984527235)
      ·
        refine ⟨11608002396537817476790853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7738668264358544984527235 11608002396537817476790853)
        ·
          refine ⟨2176500449350840776898285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11608002396537817476790853 2176500449350840776898285)
          ·
            refine ⟨816187668506565291336857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2176500449350840776898285 816187668506565291336857)
            ·
              refine ⟨612140751379923968502643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816187668506565291336857 612140751379923968502643)
              ·
                refine ⟨918211127069885952753965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612140751379923968502643 918211127069885952753965)
                ·
                  refine ⟨344329172651207232282737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 918211127069885952753965 344329172651207232282737)
                  ·
                    rfl

theorem cell20_754401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_754401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754401 prefixEnd_754401 := by exact prefixLift 754401
  have htrace : WordTrace (prefixWord ++ tailWord_754401) baseStart_754401 baseEnd_754401 := by
    simpa [prefixWord, tailWord_754401, baseEnd_754401] using wordTrace_append hprefix tailTrace_754401
  have hstable : (prefixWord ++ tailWord_754401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754401).length < 2 ^ (prefixWord ++ tailWord_754401).sum := by decide
  have hdescent : baseEnd_754401 < baseStart_754401 := by decide
  rcases family_descends (prefixWord ++ tailWord_754401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754426 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_754426 : Nat := 118140960795 + 754426 * 2 ^ 59
def prefixEnd_754426 : Nat := 4983230072969 + 3 ^ 40 * 754426 * 2
def baseEnd_754426 : Nat := 344340583332418256449301

theorem tailTrace_754426 : CollatzResearch.WordTrace tailWord_754426 prefixEnd_754426 344340583332418256449301 := by
  unfold tailWord_754426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6879044191212730636994783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18344117843233948365319421 6879044191212730636994783)
  ·
    refine ⟨10318566286819095955492175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6879044191212730636994783 10318566286819095955492175)
    ·
      refine ⟨15477849430228643933238263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10318566286819095955492175 15477849430228643933238263)
      ·
        refine ⟨23216774145342965899857395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15477849430228643933238263 23216774145342965899857395)
        ·
          refine ⟨34825161218014448849786093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23216774145342965899857395 34825161218014448849786093)
          ·
            refine ⟨13059435456755418318669785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34825161218014448849786093 13059435456755418318669785)
            ·
              refine ⟨9794576592566563739002339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13059435456755418318669785 9794576592566563739002339)
              ·
                refine ⟨14691864888849845608503509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9794576592566563739002339 14691864888849845608503509)
                ·
                  refine ⟨344340583332418256449301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14691864888849845608503509 344340583332418256449301)
                  ·
                    rfl

theorem cell20_754426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_754426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754426 prefixEnd_754426 := by exact prefixLift 754426
  have htrace : WordTrace (prefixWord ++ tailWord_754426) baseStart_754426 baseEnd_754426 := by
    simpa [prefixWord, tailWord_754426, baseEnd_754426] using wordTrace_append hprefix tailTrace_754426
  have hstable : (prefixWord ++ tailWord_754426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754426).length < 2 ^ (prefixWord ++ tailWord_754426).sum := by decide
  have hdescent : baseEnd_754426 < baseStart_754426 := by decide
  rcases family_descends (prefixWord ++ tailWord_754426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754429 : List Nat := [1, 4, 1, 1, 1, 1, 4, 5, 2]
def baseStart_754429 : Nat := 118140960795 + 754429 * 2 ^ 59
def prefixEnd_754429 : Nat := 4983230072969 + 3 ^ 40 * 754429 * 2
def baseEnd_754429 : Nat := 344341952614163579349289

theorem tailTrace_754429 : CollatzResearch.WordTrace tailWord_754429 prefixEnd_754429 344341952614163579349289 := by
  unfold tailWord_754429
  simp only [CollatzResearch.WordTrace]
  refine ⟨27516286183840054060338341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18344190789226702706892227 27516286183840054060338341)
  ·
    refine ⟨5159303659470010136313439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27516286183840054060338341 5159303659470010136313439)
    ·
      refine ⟨7738955489205015204470159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5159303659470010136313439 7738955489205015204470159)
      ·
        refine ⟨11608433233807522806705239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7738955489205015204470159 11608433233807522806705239)
        ·
          refine ⟨17412649850711284210057859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11608433233807522806705239 17412649850711284210057859)
          ·
            refine ⟨26118974776066926315086789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17412649850711284210057859 26118974776066926315086789)
            ·
              refine ⟨4897307770512548684078773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26118974776066926315086789 4897307770512548684078773)
              ·
                refine ⟨459122603485551439132385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4897307770512548684078773 459122603485551439132385)
                ·
                  refine ⟨344341952614163579349289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459122603485551439132385 344341952614163579349289)
                  ·
                    rfl

theorem cell20_754429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_754429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754429 prefixEnd_754429 := by exact prefixLift 754429
  have htrace : WordTrace (prefixWord ++ tailWord_754429) baseStart_754429 baseEnd_754429 := by
    simpa [prefixWord, tailWord_754429, baseEnd_754429] using wordTrace_append hprefix tailTrace_754429
  have hstable : (prefixWord ++ tailWord_754429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754429).length < 2 ^ (prefixWord ++ tailWord_754429).sum := by decide
  have hdescent : baseEnd_754429 < baseStart_754429 := by decide
  rcases family_descends (prefixWord ++ tailWord_754429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754494 : List Nat := [4, 2, 1, 2, 4, 1, 1, 2, 3]
def baseStart_754494 : Nat := 118140960795 + 754494 * 2 ^ 59
def prefixEnd_754494 : Nat := 4983230072969 + 3 ^ 40 * 754494 * 2
def baseEnd_754494 : Nat := 344371620385312242182357

theorem tailTrace_754494 : CollatzResearch.WordTrace tailWord_754494 prefixEnd_754494 344371620385312242182357 := by
  unfold tailWord_754494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3439832116075571270181817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18345771285736380107636357 3439832116075571270181817)
  ·
    refine ⟨2579874087056678452636363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3439832116075571270181817 2579874087056678452636363)
    ·
      refine ⟨3869811130585017678954545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2579874087056678452636363 3869811130585017678954545)
      ·
        refine ⟨2902358347938763259215909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3869811130585017678954545 2902358347938763259215909)
        ·
          refine ⟨544192190238518111102983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2902358347938763259215909 544192190238518111102983)
          ·
            refine ⟨816288285357777166654475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544192190238518111102983 816288285357777166654475)
            ·
              refine ⟨1224432428036665749981713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816288285357777166654475 1224432428036665749981713)
              ·
                refine ⟨918324321027499312486285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1224432428036665749981713 918324321027499312486285)
                ·
                  refine ⟨344371620385312242182357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 918324321027499312486285 344371620385312242182357)
                  ·
                    rfl

theorem cell20_754494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_754494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754494 prefixEnd_754494 := by exact prefixLift 754494
  have htrace : WordTrace (prefixWord ++ tailWord_754494) baseStart_754494 baseEnd_754494 := by
    simpa [prefixWord, tailWord_754494, baseEnd_754494] using wordTrace_append hprefix tailTrace_754494
  have hstable : (prefixWord ++ tailWord_754494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754494).length < 2 ^ (prefixWord ++ tailWord_754494).sum := by decide
  have hdescent : baseEnd_754494 < baseStart_754494 := by decide
  rcases family_descends (prefixWord ++ tailWord_754494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754495 : List Nat := [1, 1, 2, 2, 5, 2, 7]
def baseStart_754495 : Nat := 118140960795 + 754495 * 2 ^ 59
def prefixEnd_754495 : Nat := 4983230072969 + 3 ^ 40 * 754495 * 2
def baseEnd_754495 : Nat := 38263564090284520349891

theorem tailTrace_754495 : CollatzResearch.WordTrace tailWord_754495 prefixEnd_754495 38263564090284520349891 := by
  unfold tailWord_754495
  simp only [CollatzResearch.WordTrace]
  refine ⟨27518693401600947332240939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18345795601067298221493959 27518693401600947332240939)
  ·
    refine ⟨41278040102401420998361409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27518693401600947332240939 41278040102401420998361409)
    ·
      refine ⟨30958530076801065748771057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41278040102401420998361409 30958530076801065748771057)
      ·
        refine ⟨23218897557600799311578293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30958530076801065748771057 23218897557600799311578293)
        ·
          refine ⟨2176771646025074935460465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23218897557600799311578293 2176771646025074935460465)
          ·
            refine ⟨1632578734518806201595349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2176771646025074935460465 1632578734518806201595349)
            ·
              refine ⟨38263564090284520349891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1632578734518806201595349 38263564090284520349891)
              ·
                rfl

theorem cell20_754495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 7].length) (baseStart_754495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754495 prefixEnd_754495 := by exact prefixLift 754495
  have htrace : WordTrace (prefixWord ++ tailWord_754495) baseStart_754495 baseEnd_754495 := by
    simpa [prefixWord, tailWord_754495, baseEnd_754495] using wordTrace_append hprefix tailTrace_754495
  have hstable : (prefixWord ++ tailWord_754495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754495).length < 2 ^ (prefixWord ++ tailWord_754495).sum := by decide
  have hdescent : baseEnd_754495 < baseStart_754495 := by decide
  rcases family_descends (prefixWord ++ tailWord_754495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754505 : List Nat := [1, 2, 1, 1, 2, 5, 2, 4, 2]
def baseStart_754505 : Nat := 118140960795 + 754505 * 2 ^ 59
def prefixEnd_754505 : Nat := 4983230072969 + 3 ^ 40 * 754505 * 2
def baseEnd_754505 : Nat := 344376641085045092815645

theorem tailTrace_754505 : CollatzResearch.WordTrace tailWord_754505 prefixEnd_754505 344376641085045092815645 := by
  unfold tailWord_754505
  simp only [CollatzResearch.WordTrace]
  refine ⟨27519058131564719040104969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18346038754376479360069979 27519058131564719040104969)
  ·
    refine ⟨20639293598673539280078727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27519058131564719040104969 20639293598673539280078727)
    ·
      refine ⟨30958940398010308920118091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20639293598673539280078727 30958940398010308920118091)
      ·
        refine ⟨46438410597015463380177137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30958940398010308920118091 46438410597015463380177137)
        ·
          refine ⟨34828807947761597535132853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46438410597015463380177137 34828807947761597535132853)
          ·
            refine ⟨3265200745102649768918705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34828807947761597535132853 3265200745102649768918705)
            ·
              refine ⟨2448900558826987326689029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3265200745102649768918705 2448900558826987326689029)
              ·
                refine ⟨459168854780060123754193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2448900558826987326689029 459168854780060123754193)
                ·
                  refine ⟨344376641085045092815645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459168854780060123754193 344376641085045092815645)
                  ·
                    rfl

theorem cell20_754505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 2].length) (baseStart_754505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754505 prefixEnd_754505 := by exact prefixLift 754505
  have htrace : WordTrace (prefixWord ++ tailWord_754505) baseStart_754505 baseEnd_754505 := by
    simpa [prefixWord, tailWord_754505, baseEnd_754505] using wordTrace_append hprefix tailTrace_754505
  have hstable : (prefixWord ++ tailWord_754505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754505).length < 2 ^ (prefixWord ++ tailWord_754505).sum := by decide
  have hdescent : baseEnd_754505 < baseStart_754505 := by decide
  rcases family_descends (prefixWord ++ tailWord_754505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754540 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_754540 : Nat := 118140960795 + 754540 * 2 ^ 59
def prefixEnd_754540 : Nat := 4983230072969 + 3 ^ 40 * 754540 * 2
def baseEnd_754540 : Nat := 344392616038740526648835

theorem tailTrace_754540 : CollatzResearch.WordTrace tailWord_754540 prefixEnd_754540 344392616038740526648835 := by
  unfold tailWord_754540
  simp only [CollatzResearch.WordTrace]
  refine ⟨13760167343218960008814537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18346889790958613345086049 13760167343218960008814537)
  ·
    refine ⟨10320125507414220006610903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13760167343218960008814537 10320125507414220006610903)
    ·
      refine ⟨15480188261121330009916355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10320125507414220006610903 15480188261121330009916355)
      ·
        refine ⟨23220282391681995014874533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15480188261121330009916355 23220282391681995014874533)
        ·
          refine ⟨4353802948440374065288975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23220282391681995014874533 4353802948440374065288975)
          ·
            refine ⟨6530704422660561097933463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4353802948440374065288975 6530704422660561097933463)
            ·
              refine ⟨9796056633990841646900195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6530704422660561097933463 9796056633990841646900195)
              ·
                refine ⟨14694084950986262470350293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9796056633990841646900195 14694084950986262470350293)
                ·
                  refine ⟨344392616038740526648835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14694084950986262470350293 344392616038740526648835)
                  ·
                    rfl

theorem cell20_754540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_754540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754540 prefixEnd_754540 := by exact prefixLift 754540
  have htrace : WordTrace (prefixWord ++ tailWord_754540) baseStart_754540 baseEnd_754540 := by
    simpa [prefixWord, tailWord_754540, baseEnd_754540] using wordTrace_append hprefix tailTrace_754540
  have hstable : (prefixWord ++ tailWord_754540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754540).length < 2 ^ (prefixWord ++ tailWord_754540).sum := by decide
  have hdescent : baseEnd_754540 < baseStart_754540 := by decide
  rcases family_descends (prefixWord ++ tailWord_754540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754547 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 6]
def baseStart_754547 : Nat := 118140960795 + 754547 * 2 ^ 59
def prefixEnd_754547 : Nat := 4983230072969 + 3 ^ 40 * 754547 * 2
def baseEnd_754547 : Nat := 344395811029479613415473

theorem tailTrace_754547 : CollatzResearch.WordTrace tailWord_754547 prefixEnd_754547 344395811029479613415473 := by
  unfold tailWord_754547
  simp only [CollatzResearch.WordTrace]
  refine ⟨27520589997412560213133895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18347059998275040142089263 27520589997412560213133895)
  ·
    refine ⟨41280884996118840319700843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27520589997412560213133895 41280884996118840319700843)
    ·
      refine ⟨61921327494178260479551265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41280884996118840319700843 61921327494178260479551265)
      ·
        refine ⟨46440995620633695359663449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61921327494178260479551265 46440995620633695359663449)
        ·
          refine ⟨34830746715475271519747587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46440995620633695359663449 34830746715475271519747587)
          ·
            refine ⟨52246120073212907279621381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34830746715475271519747587 52246120073212907279621381)
            ·
              refine ⟨9796147513727420114929009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52246120073212907279621381 9796147513727420114929009)
              ·
                refine ⟨7347110635295565086196757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9796147513727420114929009 7347110635295565086196757)
                ·
                  refine ⟨344395811029479613415473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7347110635295565086196757 344395811029479613415473)
                  ·
                    rfl

theorem cell20_754547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_754547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754547 prefixEnd_754547 := by exact prefixLift 754547
  have htrace : WordTrace (prefixWord ++ tailWord_754547) baseStart_754547 baseEnd_754547 := by
    simpa [prefixWord, tailWord_754547, baseEnd_754547] using wordTrace_append hprefix tailTrace_754547
  have hstable : (prefixWord ++ tailWord_754547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754547).length < 2 ^ (prefixWord ++ tailWord_754547).sum := by decide
  have hdescent : baseEnd_754547 < baseStart_754547 := by decide
  rcases family_descends (prefixWord ++ tailWord_754547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754550 : List Nat := [5, 1, 1, 3, 1, 1, 8]
def baseStart_754550 : Nat := 118140960795 + 754550 * 2 ^ 59
def prefixEnd_754550 : Nat := 4983230072969 + 3 ^ 40 * 754550 * 2
def baseEnd_754550 : Nat := 38266353367913881812829

theorem tailTrace_754550 : CollatzResearch.WordTrace tailWord_754550 prefixEnd_754550 38266353367913881812829 := by
  unfold tailWord_754550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1720043713525105732843319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18347132944267794483662069 1720043713525105732843319)
  ·
    refine ⟨2580065570287658599264979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1720043713525105732843319 2580065570287658599264979)
    ·
      refine ⟨3870098355431487898897469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2580065570287658599264979 3870098355431487898897469)
      ·
        refine ⟨1451286883286807962086551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3870098355431487898897469 1451286883286807962086551)
        ·
          refine ⟨2176930324930211943129827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451286883286807962086551 2176930324930211943129827)
          ·
            refine ⟨3265395487395317914694741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176930324930211943129827 3265395487395317914694741)
            ·
              refine ⟨38266353367913881812829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3265395487395317914694741 38266353367913881812829)
              ·
                rfl

theorem cell20_754550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 8].length) (baseStart_754550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754550 prefixEnd_754550 := by exact prefixLift 754550
  have htrace : WordTrace (prefixWord ++ tailWord_754550) baseStart_754550 baseEnd_754550 := by
    simpa [prefixWord, tailWord_754550, baseEnd_754550] using wordTrace_append hprefix tailTrace_754550
  have hstable : (prefixWord ++ tailWord_754550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754550).length < 2 ^ (prefixWord ++ tailWord_754550).sum := by decide
  have hdescent : baseEnd_754550 < baseStart_754550 := by decide
  rcases family_descends (prefixWord ++ tailWord_754550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754585 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 6]
def baseStart_754585 : Nat := 118140960795 + 754585 * 2 ^ 59
def prefixEnd_754585 : Nat := 4983230072969 + 3 ^ 40 * 754585 * 2
def baseEnd_754585 : Nat := 344413155264920370148651

theorem tailTrace_754585 : CollatzResearch.WordTrace tailWord_754585 prefixEnd_754585 344413155264920370148651 := by
  unfold tailWord_754585
  simp only [CollatzResearch.WordTrace]
  refine ⟨27521975971274892703017209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18347983980849928468678139 27521975971274892703017209)
  ·
    refine ⟨20641481978456169527262907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27521975971274892703017209 20641481978456169527262907)
    ·
      refine ⟨30962222967684254290894361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20641481978456169527262907 30962222967684254290894361)
      ·
        refine ⟨23221667225763190718170771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30962222967684254290894361 23221667225763190718170771)
        ·
          refine ⟨34832500838644786077256157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23221667225763190718170771 34832500838644786077256157)
          ·
            refine ⟨13062187814491794778971059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34832500838644786077256157 13062187814491794778971059)
            ·
              refine ⟨19593281721737692168456589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13062187814491794778971059 19593281721737692168456589)
              ·
                refine ⟨7347480645651634563171221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19593281721737692168456589 7347480645651634563171221)
                ·
                  refine ⟨344413155264920370148651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7347480645651634563171221 344413155264920370148651)
                  ·
                    rfl

theorem cell20_754585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_754585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754585 prefixEnd_754585 := by exact prefixLift 754585
  have htrace : WordTrace (prefixWord ++ tailWord_754585) baseStart_754585 baseEnd_754585 := by
    simpa [prefixWord, tailWord_754585, baseEnd_754585] using wordTrace_append hprefix tailTrace_754585
  have hstable : (prefixWord ++ tailWord_754585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754585).length < 2 ^ (prefixWord ++ tailWord_754585).sum := by decide
  have hdescent : baseEnd_754585 < baseStart_754585 := by decide
  rcases family_descends (prefixWord ++ tailWord_754585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754605 : List Nat := [1, 5, 2, 3, 2, 7]
def baseStart_754605 : Nat := 118140960795 + 754605 * 2 ^ 59
def prefixEnd_754605 : Nat := 4983230072969 + 3 ^ 40 * 754605 * 2
def baseEnd_754605 : Nat := 12756380881847747758589

theorem tailTrace_754605 : CollatzResearch.WordTrace tailWord_754605 prefixEnd_754605 12756380881847747758589 := by
  unfold tailWord_754605
  simp only [CollatzResearch.WordTrace]
  refine ⟨27522705431202436118745269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18348470287468290745830179 27522705431202436118745269)
  ·
    refine ⟨2580253634175228386132369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27522705431202436118745269 2580253634175228386132369)
    ·
      refine ⟨1935190225631421289599277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2580253634175228386132369 1935190225631421289599277)
      ·
        refine ⟨725696334611782983599729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1935190225631421289599277 725696334611782983599729)
        ·
          refine ⟨544272250958837237699797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 725696334611782983599729 544272250958837237699797)
          ·
            refine ⟨12756380881847747758589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 544272250958837237699797 12756380881847747758589)
            ·
              rfl

theorem cell20_754605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 7].length) (baseStart_754605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754605 prefixEnd_754605 := by exact prefixLift 754605
  have htrace : WordTrace (prefixWord ++ tailWord_754605) baseStart_754605 baseEnd_754605 := by
    simpa [prefixWord, tailWord_754605, baseEnd_754605] using wordTrace_append hprefix tailTrace_754605
  have hstable : (prefixWord ++ tailWord_754605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754605).length < 2 ^ (prefixWord ++ tailWord_754605).sum := by decide
  have hdescent : baseEnd_754605 < baseStart_754605 := by decide
  rcases family_descends (prefixWord ++ tailWord_754605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754609 : List Nat := [1, 2, 2, 4, 3, 8]
def baseStart_754609 : Nat := 118140960795 + 754609 * 2 ^ 59
def prefixEnd_754609 : Nat := 4983230072969 + 3 ^ 40 * 754609 * 2
def baseEnd_754609 : Nat := 12756448500699368642539

theorem tailTrace_754609 : CollatzResearch.WordTrace tailWord_754609 prefixEnd_754609 12756448500699368642539 := by
  unfold tailWord_754609
  simp only [CollatzResearch.WordTrace]
  refine ⟨27522851323187944801890881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18348567548791963201260587 27522851323187944801890881)
  ·
    refine ⟨20642138492390958601418161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27522851323187944801890881 20642138492390958601418161)
    ·
      refine ⟨15481603869293218951063621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20642138492390958601418161 15481603869293218951063621)
      ·
        refine ⟨2902800725492478553324429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15481603869293218951063621 2902800725492478553324429)
        ·
          refine ⟨1088550272059679457496661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2902800725492478553324429 1088550272059679457496661)
          ·
            refine ⟨12756448500699368642539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1088550272059679457496661 12756448500699368642539)
            ·
              rfl

theorem cell20_754609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 8].length) (baseStart_754609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754609 prefixEnd_754609 := by exact prefixLift 754609
  have htrace : WordTrace (prefixWord ++ tailWord_754609) baseStart_754609 baseEnd_754609 := by
    simpa [prefixWord, tailWord_754609, baseEnd_754609] using wordTrace_append hprefix tailTrace_754609
  have hstable : (prefixWord ++ tailWord_754609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754609).length < 2 ^ (prefixWord ++ tailWord_754609).sum := by decide
  have hdescent : baseEnd_754609 < baseStart_754609 := by decide
  rcases family_descends (prefixWord ++ tailWord_754609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754671 : List Nat := [1, 1, 2, 1, 4, 3, 3, 2, 3]
def baseStart_754671 : Nat := 118140960795 + 754671 * 2 ^ 59
def prefixEnd_754671 : Nat := 4983230072969 + 3 ^ 40 * 754671 * 2
def baseEnd_754671 : Nat := 344452408008286293281633

theorem tailTrace_754671 : CollatzResearch.WordTrace tailWord_754671 prefixEnd_754671 344452408008286293281633 := by
  unfold tailWord_754671
  simp only [CollatzResearch.WordTrace]
  refine ⟨27525112648963329390647867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18350075099308886260431911 27525112648963329390647867)
  ·
    refine ⟨41287668973444994085971801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27525112648963329390647867 41287668973444994085971801)
    ·
      refine ⟨30965751730083745564478851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41287668973444994085971801 30965751730083745564478851)
      ·
        refine ⟨46448627595125618346718277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30965751730083745564478851 46448627595125618346718277)
        ·
          refine ⟨8709117674086053440009677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46448627595125618346718277 8709117674086053440009677)
          ·
            refine ⟨3265919127782270040003629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8709117674086053440009677 3265919127782270040003629)
            ·
              refine ⟨1224719672918351265001361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3265919127782270040003629 1224719672918351265001361)
              ·
                refine ⟨918539754688763448751021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1224719672918351265001361 918539754688763448751021)
                ·
                  refine ⟨344452408008286293281633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 918539754688763448751021 344452408008286293281633)
                  ·
                    rfl

theorem cell20_754671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 3].length) (baseStart_754671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754671 prefixEnd_754671 := by exact prefixLift 754671
  have htrace : WordTrace (prefixWord ++ tailWord_754671) baseStart_754671 baseEnd_754671 := by
    simpa [prefixWord, tailWord_754671, baseEnd_754671] using wordTrace_append hprefix tailTrace_754671
  have hstable : (prefixWord ++ tailWord_754671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754671).length < 2 ^ (prefixWord ++ tailWord_754671).sum := by decide
  have hdescent : baseEnd_754671 < baseStart_754671 := by decide
  rcases family_descends (prefixWord ++ tailWord_754671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754674 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 4]
def baseStart_754674 : Nat := 118140960795 + 754674 * 2 ^ 59
def prefixEnd_754674 : Nat := 4983230072969 + 3 ^ 40 * 754674 * 2
def baseEnd_754674 : Nat := 344453777290031616181621

theorem tailTrace_754674 : CollatzResearch.WordTrace tailWord_754674 prefixEnd_754674 344453777290031616181621 := by
  unfold tailWord_754674
  simp only [CollatzResearch.WordTrace]
  refine ⟨6881305516988115225751769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18350148045301640602004717 6881305516988115225751769)
  ·
    refine ⟨5160979137741086419313827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6881305516988115225751769 5160979137741086419313827)
    ·
      refine ⟨7741468706611629628970741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5160979137741086419313827 7741468706611629628970741)
      ·
        refine ⟨725762691244840277716007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7741468706611629628970741 725762691244840277716007)
        ·
          refine ⟨1088644036867260416574011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725762691244840277716007 1088644036867260416574011)
          ·
            refine ⟨1632966055300890624861017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088644036867260416574011 1632966055300890624861017)
            ·
              refine ⟨1224724541475667968645763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1632966055300890624861017 1224724541475667968645763)
              ·
                refine ⟨1837086812213501952968645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1224724541475667968645763 1837086812213501952968645)
                ·
                  refine ⟨344453777290031616181621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1837086812213501952968645 344453777290031616181621)
                  ·
                    rfl

theorem cell20_754674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_754674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754674 prefixEnd_754674 := by exact prefixLift 754674
  have htrace : WordTrace (prefixWord ++ tailWord_754674) baseStart_754674 baseEnd_754674 := by
    simpa [prefixWord, tailWord_754674, baseEnd_754674] using wordTrace_append hprefix tailTrace_754674
  have hstable : (prefixWord ++ tailWord_754674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754674).length < 2 ^ (prefixWord ++ tailWord_754674).sum := by decide
  have hdescent : baseEnd_754674 < baseStart_754674 := by decide
  rcases family_descends (prefixWord ++ tailWord_754674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754702 : List Nat := [4, 1, 1, 2, 2, 2, 4, 4]
def baseStart_754702 : Nat := 118140960795 + 754702 * 2 ^ 59
def prefixEnd_754702 : Nat := 4983230072969 + 3 ^ 40 * 754702 * 2
def baseEnd_754702 : Nat := 114822185750995987749391

theorem tailTrace_754702 : CollatzResearch.WordTrace tailWord_754702 prefixEnd_754702 114822185750995987749391 := by
  unfold tailWord_754702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3440780413981377710628295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18350828874567347790017573 3440780413981377710628295)
  ·
    refine ⟨5161170620972066565942443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3440780413981377710628295 5161170620972066565942443)
    ·
      refine ⟨7741755931458099848913665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5161170620972066565942443 7741755931458099848913665)
      ·
        refine ⟨5806316948593574886685249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7741755931458099848913665 5806316948593574886685249)
        ·
          refine ⟨4354737711445181165013937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5806316948593574886685249 4354737711445181165013937)
          ·
            refine ⟨3266053283583885873760453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4354737711445181165013937 3266053283583885873760453)
            ·
              refine ⟨612384990671978601330085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3266053283583885873760453 612384990671978601330085)
              ·
                refine ⟨114822185750995987749391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 612384990671978601330085 114822185750995987749391)
                ·
                  rfl

theorem cell20_754702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_754702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754702 prefixEnd_754702 := by exact prefixLift 754702
  have htrace : WordTrace (prefixWord ++ tailWord_754702) baseStart_754702 baseEnd_754702 := by
    simpa [prefixWord, tailWord_754702, baseEnd_754702] using wordTrace_append hprefix tailTrace_754702
  have hstable : (prefixWord ++ tailWord_754702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754702).length < 2 ^ (prefixWord ++ tailWord_754702).sum := by decide
  have hdescent : baseEnd_754702 < baseStart_754702 := by decide
  rcases family_descends (prefixWord ++ tailWord_754702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754712 : List Nat := [2, 1, 2, 3, 2, 4, 1, 3, 2]
def baseStart_754712 : Nat := 118140960795 + 754712 * 2 ^ 59
def prefixEnd_754712 : Nat := 4983230072969 + 3 ^ 40 * 754712 * 2
def baseEnd_754712 : Nat := 344471121525472372914799

theorem tailTrace_754712 : CollatzResearch.WordTrace tailWord_754712 prefixEnd_754712 344471121525472372914799 := by
  unfold tailWord_754712
  simp only [CollatzResearch.WordTrace]
  refine ⟨13763304020907396696445195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18351072027876528928593593 13763304020907396696445195)
  ·
    refine ⟨20644956031361095044667793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13763304020907396696445195 20644956031361095044667793)
    ·
      refine ⟨15483717023520821283500845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20644956031361095044667793 15483717023520821283500845)
      ·
        refine ⟨5806393883820307981312817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15483717023520821283500845 5806393883820307981312817)
        ·
          refine ⟨4354795412865230985984613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5806393883820307981312817 4354795412865230985984613)
          ·
            refine ⟨816524139912230809872115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4354795412865230985984613 816524139912230809872115)
            ·
              refine ⟨1224786209868346214808173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816524139912230809872115 1224786209868346214808173)
              ·
                refine ⟨459294828700629830553065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1224786209868346214808173 459294828700629830553065)
                ·
                  refine ⟨344471121525472372914799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459294828700629830553065 344471121525472372914799)
                  ·
                    rfl

theorem cell20_754712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 2].length) (baseStart_754712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754712 prefixEnd_754712 := by exact prefixLift 754712
  have htrace : WordTrace (prefixWord ++ tailWord_754712) baseStart_754712 baseEnd_754712 := by
    simpa [prefixWord, tailWord_754712, baseEnd_754712] using wordTrace_append hprefix tailTrace_754712
  have hstable : (prefixWord ++ tailWord_754712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754712).length < 2 ^ (prefixWord ++ tailWord_754712).sum := by decide
  have hdescent : baseEnd_754712 < baseStart_754712 := by decide
  rcases family_descends (prefixWord ++ tailWord_754712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754723 : List Nat := [1, 1, 1, 4, 3, 4, 6]
def baseStart_754723 : Nat := 118140960795 + 754723 * 2 ^ 59
def prefixEnd_754723 : Nat := 4983230072969 + 3 ^ 40 * 754723 * 2
def baseEnd_754723 : Nat := 38275126913911691505343

theorem tailTrace_754723 : CollatzResearch.WordTrace tailWord_754723 prefixEnd_754723 38275126913911691505343 := by
  unfold tailWord_754723
  simp only [CollatzResearch.WordTrace]
  refine ⟨27527009244774942271540823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18351339496516628181027215 27527009244774942271540823)
  ·
    refine ⟨41290513867162413407311235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27527009244774942271540823 41290513867162413407311235)
    ·
      refine ⟨61935770800743620110966853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41290513867162413407311235 61935770800743620110966853)
      ·
        refine ⟨11612957025139428770806285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61935770800743620110966853 11612957025139428770806285)
        ·
          refine ⟨4354858884427285789052357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11612957025139428770806285 4354858884427285789052357)
          ·
            refine ⟨816536040830116085447317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4354858884427285789052357 816536040830116085447317)
            ·
              refine ⟨38275126913911691505343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 816536040830116085447317 38275126913911691505343)
              ·
                rfl

theorem cell20_754723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 6].length) (baseStart_754723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754723 prefixEnd_754723 := by exact prefixLift 754723
  have htrace : WordTrace (prefixWord ++ tailWord_754723) baseStart_754723 baseEnd_754723 := by
    simpa [prefixWord, tailWord_754723, baseEnd_754723] using wordTrace_append hprefix tailTrace_754723
  have hstable : (prefixWord ++ tailWord_754723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754723).length < 2 ^ (prefixWord ++ tailWord_754723).sum := by decide
  have hdescent : baseEnd_754723 < baseStart_754723 := by decide
  rcases family_descends (prefixWord ++ tailWord_754723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754740 : List Nat := [2, 5, 1, 2, 1, 1, 1, 7]
def baseStart_754740 : Nat := 118140960795 + 754740 * 2 ^ 59
def prefixEnd_754740 : Nat := 4983230072969 + 3 ^ 40 * 754740 * 2
def baseEnd_754740 : Nat := 114827967162809573327117

theorem tailTrace_754740 : CollatzResearch.WordTrace tailWord_754740 prefixEnd_754740 114827967162809573327117 := by
  unfold tailWord_754740
  simp only [CollatzResearch.WordTrace]
  refine ⟨13763814642856677087454837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18351752857142236116606449 13763814642856677087454837)
  ·
    refine ⟨1290357622767813476948891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13763814642856677087454837 1290357622767813476948891)
    ·
      refine ⟨1935536434151720215423337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1290357622767813476948891 1935536434151720215423337)
      ·
        refine ⟨1451652325613790161567503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1935536434151720215423337 1451652325613790161567503)
        ·
          refine ⟨2177478488420685242351255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451652325613790161567503 2177478488420685242351255)
          ·
            refine ⟨3266217732631027863526883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177478488420685242351255 3266217732631027863526883)
            ·
              refine ⟨4899326598946541795290325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3266217732631027863526883 4899326598946541795290325)
              ·
                refine ⟨114827967162809573327117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4899326598946541795290325 114827967162809573327117)
                ·
                  rfl

theorem cell20_754740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_754740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754740 prefixEnd_754740 := by exact prefixLift 754740
  have htrace : WordTrace (prefixWord ++ tailWord_754740) baseStart_754740 baseEnd_754740 := by
    simpa [prefixWord, tailWord_754740, baseEnd_754740] using wordTrace_append hprefix tailTrace_754740
  have hstable : (prefixWord ++ tailWord_754740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754740).length < 2 ^ (prefixWord ++ tailWord_754740).sum := by decide
  have hdescent : baseEnd_754740 < baseStart_754740 := by decide
  rcases family_descends (prefixWord ++ tailWord_754740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754781 : List Nat := [1, 4, 4, 1, 2, 1, 2, 2, 3]
def baseStart_754781 : Nat := 118140960795 + 754781 * 2 ^ 59
def prefixEnd_754781 : Nat := 4983230072969 + 3 ^ 40 * 754781 * 2
def baseEnd_754781 : Nat := 344502615005614799614517

theorem tailTrace_754781 : CollatzResearch.WordTrace tailWord_754781 prefixEnd_754781 344502615005614799614517 := by
  unfold tailWord_754781
  simp only [CollatzResearch.WordTrace]
  refine ⟨27529124678564818177152197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18352749785709878784768131 27529124678564818177152197)
  ·
    refine ⟨5161710877230903408216037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27529124678564818177152197 5161710877230903408216037)
    ·
      refine ⟨967820789480794389040507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5161710877230903408216037 967820789480794389040507)
      ·
        refine ⟨1451731184221191583560761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 967820789480794389040507 1451731184221191583560761)
        ·
          refine ⟨1088798388165893687670571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1451731184221191583560761 1088798388165893687670571)
          ·
            refine ⟨1633197582248840531505857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088798388165893687670571 1633197582248840531505857)
            ·
              refine ⟨1224898186686630398629393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1633197582248840531505857 1224898186686630398629393)
              ·
                refine ⟨918673640014972798972045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1224898186686630398629393 918673640014972798972045)
                ·
                  refine ⟨344502615005614799614517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 918673640014972798972045 344502615005614799614517)
                  ·
                    rfl

theorem cell20_754781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_754781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754781 prefixEnd_754781 := by exact prefixLift 754781
  have htrace : WordTrace (prefixWord ++ tailWord_754781) baseStart_754781 baseEnd_754781 := by
    simpa [prefixWord, tailWord_754781, baseEnd_754781] using wordTrace_append hprefix tailTrace_754781
  have hstable : (prefixWord ++ tailWord_754781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754781).length < 2 ^ (prefixWord ++ tailWord_754781).sum := by decide
  have hdescent : baseEnd_754781 < baseStart_754781 := by decide
  rcases family_descends (prefixWord ++ tailWord_754781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754840 : List Nat := [2, 1, 2, 4, 2, 3, 1, 2, 3]
def baseStart_754840 : Nat := 118140960795 + 754840 * 2 ^ 59
def prefixEnd_754840 : Nat := 4983230072969 + 3 ^ 40 * 754840 * 2
def baseEnd_754840 : Nat := 344529544213272816647609

theorem tailTrace_754840 : CollatzResearch.WordTrace tailWord_754840 prefixEnd_754840 344529544213272816647609 := by
  unfold tailWord_754840
  simp only [CollatzResearch.WordTrace]
  refine ⟨13765638292675535626774987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18354184390234047502366649 13765638292675535626774987)
  ·
    refine ⟨20648457439013303440162481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13765638292675535626774987 20648457439013303440162481)
    ·
      refine ⟨15486343079259977580121861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20648457439013303440162481 15486343079259977580121861)
      ·
        refine ⟨2903689327361245796272849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15486343079259977580121861 2903689327361245796272849)
        ·
          refine ⟨2177766995520934347204637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2903689327361245796272849 2177766995520934347204637)
          ·
            refine ⟨816662623320350380201739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2177766995520934347204637 816662623320350380201739)
            ·
              refine ⟨1224993934980525570302609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816662623320350380201739 1224993934980525570302609)
              ·
                refine ⟨918745451235394177726957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1224993934980525570302609 918745451235394177726957)
                ·
                  refine ⟨344529544213272816647609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 918745451235394177726957 344529544213272816647609)
                  ·
                    rfl

theorem cell20_754840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_754840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754840 prefixEnd_754840 := by exact prefixLift 754840
  have htrace : WordTrace (prefixWord ++ tailWord_754840) baseStart_754840 baseEnd_754840 := by
    simpa [prefixWord, tailWord_754840, baseEnd_754840] using wordTrace_append hprefix tailTrace_754840
  have hstable : (prefixWord ++ tailWord_754840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754840).length < 2 ^ (prefixWord ++ tailWord_754840).sum := by decide
  have hdescent : baseEnd_754840 < baseStart_754840 := by decide
  rcases family_descends (prefixWord ++ tailWord_754840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754847 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 4]
def baseStart_754847 : Nat := 118140960795 + 754847 * 2 ^ 59
def prefixEnd_754847 : Nat := 4983230072969 + 3 ^ 40 * 754847 * 2
def baseEnd_754847 : Nat := 344532739204011903414247

theorem tailTrace_754847 : CollatzResearch.WordTrace tailWord_754847 prefixEnd_754847 344532739204011903414247 := by
  unfold tailWord_754847
  simp only [CollatzResearch.WordTrace]
  refine ⟨27531531896325711449054795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18354354597550474299369863 27531531896325711449054795)
  ·
    refine ⟨41297297844488567173582193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27531531896325711449054795 41297297844488567173582193)
    ·
      refine ⟨30972973383366425380186645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41297297844488567173582193 30972973383366425380186645)
      ·
        refine ⟨1451858127345301189696249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30972973383366425380186645 1451858127345301189696249)
        ·
          refine ⟨1088893595508975892272187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1451858127345301189696249 1088893595508975892272187)
          ·
            refine ⟨1633340393263463838408281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088893595508975892272187 1633340393263463838408281)
            ·
              refine ⟨1225005294947597878806211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1633340393263463838408281 1225005294947597878806211)
              ·
                refine ⟨1837507942421396818209317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225005294947597878806211 1837507942421396818209317)
                ·
                  refine ⟨344532739204011903414247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1837507942421396818209317 344532739204011903414247)
                  ·
                    rfl

theorem cell20_754847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 4].length) (baseStart_754847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754847 prefixEnd_754847 := by exact prefixLift 754847
  have htrace : WordTrace (prefixWord ++ tailWord_754847) baseStart_754847 baseEnd_754847 := by
    simpa [prefixWord, tailWord_754847, baseEnd_754847] using wordTrace_append hprefix tailTrace_754847
  have hstable : (prefixWord ++ tailWord_754847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754847).length < 2 ^ (prefixWord ++ tailWord_754847).sum := by decide
  have hdescent : baseEnd_754847 < baseStart_754847 := by decide
  rcases family_descends (prefixWord ++ tailWord_754847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754881 : List Nat := [1, 2, 6, 1, 1, 3, 1, 3, 2]
def baseStart_754881 : Nat := 118140960795 + 754881 * 2 ^ 59
def prefixEnd_754881 : Nat := 4983230072969 + 3 ^ 40 * 754881 * 2
def baseEnd_754881 : Nat := 344548257730458896280775

theorem tailTrace_754881 : CollatzResearch.WordTrace tailWord_754881 prefixEnd_754881 344548257730458896280775 := by
  unfold tailWord_754881
  simp only [CollatzResearch.WordTrace]
  refine ⟨27532771978202535255792497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18355181318801690170528331 27532771978202535255792497)
  ·
    refine ⟨20649578983651901441844373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27532771978202535255792497 20649578983651901441844373)
    ·
      refine ⟨967949014858682880086455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20649578983651901441844373 967949014858682880086455)
      ·
        refine ⟨1451923522288024320129683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 967949014858682880086455 1451923522288024320129683)
        ·
          refine ⟨2177885283432036480194525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451923522288024320129683 2177885283432036480194525)
          ·
            refine ⟨816706981287013680072947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2177885283432036480194525 816706981287013680072947)
            ·
              refine ⟨1225060471930520520109421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816706981287013680072947 1225060471930520520109421)
              ·
                refine ⟨459397676973945195041033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1225060471930520520109421 459397676973945195041033)
                ·
                  refine ⟨344548257730458896280775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459397676973945195041033 344548257730458896280775)
                  ·
                    rfl

theorem cell20_754881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 2].length) (baseStart_754881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754881 prefixEnd_754881 := by exact prefixLift 754881
  have htrace : WordTrace (prefixWord ++ tailWord_754881) baseStart_754881 baseEnd_754881 := by
    simpa [prefixWord, tailWord_754881, baseEnd_754881] using wordTrace_append hprefix tailTrace_754881
  have hstable : (prefixWord ++ tailWord_754881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754881).length < 2 ^ (prefixWord ++ tailWord_754881).sum := by decide
  have hdescent : baseEnd_754881 < baseStart_754881 := by decide
  rcases family_descends (prefixWord ++ tailWord_754881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754913 : List Nat := [1, 2, 3, 1, 3, 3, 2, 5]
def baseStart_754913 : Nat := 118140960795 + 754913 * 2 ^ 59
def prefixEnd_754913 : Nat := 4983230072969 + 3 ^ 40 * 754913 * 2
def baseEnd_754913 : Nat := 114854287800803002404659

theorem tailTrace_754913 : CollatzResearch.WordTrace tailWord_754913 prefixEnd_754913 114854287800803002404659 := by
  unfold tailWord_754913
  simp only [CollatzResearch.WordTrace]
  refine ⟨27533939114086604720957393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18355959409391069813971595 27533939114086604720957393)
  ·
    refine ⟨20650454335564953540718045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27533939114086604720957393 20650454335564953540718045)
    ·
      refine ⟨7743920375836857577769267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20650454335564953540718045 7743920375836857577769267)
      ·
        refine ⟨11615880563755286366653901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7743920375836857577769267 11615880563755286366653901)
        ·
          refine ⟨4355955211408232387495213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11615880563755286366653901 4355955211408232387495213)
          ·
            refine ⟨1633483204278087145310705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4355955211408232387495213 1633483204278087145310705)
            ·
              refine ⟨1225112403208565358983029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1633483204278087145310705 1225112403208565358983029)
              ·
                refine ⟨114854287800803002404659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1225112403208565358983029 114854287800803002404659)
                ·
                  rfl

theorem cell20_754913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 5].length) (baseStart_754913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754913 prefixEnd_754913 := by exact prefixLift 754913
  have htrace : WordTrace (prefixWord ++ tailWord_754913) baseStart_754913 baseEnd_754913 := by
    simpa [prefixWord, tailWord_754913, baseEnd_754913] using wordTrace_append hprefix tailTrace_754913
  have hstable : (prefixWord ++ tailWord_754913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754913).length < 2 ^ (prefixWord ++ tailWord_754913).sum := by decide
  have hdescent : baseEnd_754913 < baseStart_754913 := by decide
  rcases family_descends (prefixWord ++ tailWord_754913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754944 : List Nat := [2, 1, 1, 2, 1, 1, 3, 7, 2]
def baseStart_754944 : Nat := 118140960795 + 754944 * 2 ^ 59
def prefixEnd_754944 : Nat := 4983230072969 + 3 ^ 40 * 754944 * 2
def baseEnd_754944 : Nat := 344577012647110677180517

theorem tailTrace_754944 : CollatzResearch.WordTrace tailWord_754944 prefixEnd_754944 344577012647110677180517 := by
  unfold tailWord_754944
  simp only [CollatzResearch.WordTrace]
  refine ⟨13767534888487148507667943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18356713184649531343557257 13767534888487148507667943)
  ·
    refine ⟨20651302332730722761501915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13767534888487148507667943 20651302332730722761501915)
    ·
      refine ⟨30976953499096084142252873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20651302332730722761501915 30976953499096084142252873)
      ·
        refine ⟨23232715124322063106689655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30976953499096084142252873 23232715124322063106689655)
        ·
          refine ⟨34849072686483094660034483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23232715124322063106689655 34849072686483094660034483)
          ·
            refine ⟨52273609029724641990051725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34849072686483094660034483 52273609029724641990051725)
            ·
              refine ⟨19602603386146740746269397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52273609029724641990051725 19602603386146740746269397)
              ·
                refine ⟨459436016862814236240689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19602603386146740746269397 459436016862814236240689)
                ·
                  refine ⟨344577012647110677180517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459436016862814236240689 344577012647110677180517)
                  ·
                    rfl

theorem cell20_754944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 2].length) (baseStart_754944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754944 prefixEnd_754944 := by exact prefixLift 754944
  have htrace : WordTrace (prefixWord ++ tailWord_754944) baseStart_754944 baseEnd_754944 := by
    simpa [prefixWord, tailWord_754944, baseEnd_754944] using wordTrace_append hprefix tailTrace_754944
  have hstable : (prefixWord ++ tailWord_754944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754944).length < 2 ^ (prefixWord ++ tailWord_754944).sum := by decide
  have hdescent : baseEnd_754944 < baseStart_754944 := by decide
  rcases family_descends (prefixWord ++ tailWord_754944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754965 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 4]
def baseStart_754965 : Nat := 118140960795 + 754965 * 2 ^ 59
def prefixEnd_754965 : Nat := 4983230072969 + 3 ^ 40 * 754965 * 2
def baseEnd_754965 : Nat := 344586597619327937480431

theorem tailTrace_754965 : CollatzResearch.WordTrace tailWord_754965 prefixEnd_754965 344586597619327937480431 := by
  unfold tailWord_754965
  simp only [CollatzResearch.WordTrace]
  refine ⟨27535835709898217601850349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18357223806598811734566899 27535835709898217601850349)
  ·
    refine ⟨10325938391211831600693881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27535835709898217601850349 10325938391211831600693881)
    ·
      refine ⟨7744453793408873700520411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10325938391211831600693881 7744453793408873700520411)
      ·
        refine ⟨11616680690113310550780617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7744453793408873700520411 11616680690113310550780617)
        ·
          refine ⟨8712510517584982913085463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11616680690113310550780617 8712510517584982913085463)
          ·
            refine ⟨13068765776377474369628195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8712510517584982913085463 13068765776377474369628195)
            ·
              refine ⟨19603148664566211554442293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13068765776377474369628195 19603148664566211554442293)
              ·
                refine ⟨1837795187303082333228965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19603148664566211554442293 1837795187303082333228965)
                ·
                  refine ⟨344586597619327937480431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1837795187303082333228965 344586597619327937480431)
                  ·
                    rfl

theorem cell20_754965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_754965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_754965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_754965 prefixEnd_754965 := by exact prefixLift 754965
  have htrace : WordTrace (prefixWord ++ tailWord_754965) baseStart_754965 baseEnd_754965 := by
    simpa [prefixWord, tailWord_754965, baseEnd_754965] using wordTrace_append hprefix tailTrace_754965
  have hstable : (prefixWord ++ tailWord_754965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754965).length < 2 ^ (prefixWord ++ tailWord_754965).sum := by decide
  have hdescent : baseEnd_754965 < baseStart_754965 := by decide
  rcases family_descends (prefixWord ++ tailWord_754965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755020 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 4]
def baseStart_755020 : Nat := 118140960795 + 755020 * 2 ^ 59
def prefixEnd_755020 : Nat := 4983230072969 + 3 ^ 40 * 755020 * 2
def baseEnd_755020 : Nat := 344611701117992190646873

theorem tailTrace_755020 : CollatzResearch.WordTrace tailWord_755020 prefixEnd_755020 344611701117992190646873 := by
  unfold tailWord_755020
  simp only [CollatzResearch.WordTrace]
  refine ⟨13768920862349480997551257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18358561149799307996735009 13768920862349480997551257)
  ·
    refine ⟨10326690646762110748163443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13768920862349480997551257 10326690646762110748163443)
    ·
      refine ⟨15490035970143166122245165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10326690646762110748163443 15490035970143166122245165)
      ·
        refine ⟨5808763488803687295841937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15490035970143166122245165 5808763488803687295841937)
        ·
          refine ⟨4356572616602765471881453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5808763488803687295841937 4356572616602765471881453)
          ·
            refine ⟨1633714731226037051955545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4356572616602765471881453 1633714731226037051955545)
            ·
              refine ⟨1225286048419527788966659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1633714731226037051955545 1225286048419527788966659)
              ·
                refine ⟨1837929072629291683449989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225286048419527788966659 1837929072629291683449989)
                ·
                  refine ⟨344611701117992190646873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1837929072629291683449989 344611701117992190646873)
                  ·
                    rfl

theorem cell20_755020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_755020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755020 prefixEnd_755020 := by exact prefixLift 755020
  have htrace : WordTrace (prefixWord ++ tailWord_755020) baseStart_755020 baseEnd_755020 := by
    simpa [prefixWord, tailWord_755020, baseEnd_755020] using wordTrace_append hprefix tailTrace_755020
  have hstable : (prefixWord ++ tailWord_755020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755020).length < 2 ^ (prefixWord ++ tailWord_755020).sum := by decide
  have hdescent : baseEnd_755020 < baseStart_755020 := by decide
  rcases family_descends (prefixWord ++ tailWord_755020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755034 : List Nat := [3, 1, 1, 2, 1, 2, 2, 5, 3]
def baseStart_755034 : Nat := 118140960795 + 755034 * 2 ^ 59
def prefixEnd_755034 : Nat := 4983230072969 + 3 ^ 40 * 755034 * 2
def baseEnd_755034 : Nat := 344618091099470364180149

theorem tailTrace_755034 : CollatzResearch.WordTrace tailWord_755034 prefixEnd_755034 344618091099470364180149 := by
  unfold tailWord_755034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6884588086662060596528039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18358901564432161590741437 6884588086662060596528039)
  ·
    refine ⟨10326882129993090894792059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6884588086662060596528039 10326882129993090894792059)
    ·
      refine ⟨15490323194989636342188089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10326882129993090894792059 15490323194989636342188089)
      ·
        refine ⟨11617742396242227256641067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15490323194989636342188089 11617742396242227256641067)
        ·
          refine ⟨17426613594363340884961601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11617742396242227256641067 17426613594363340884961601)
          ·
            refine ⟨13069960195772505663721201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17426613594363340884961601 13069960195772505663721201)
            ·
              refine ⟨9802470146829379247790901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13069960195772505663721201 9802470146829379247790901)
              ·
                refine ⟨918981576265254304480397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9802470146829379247790901 918981576265254304480397)
                ·
                  refine ⟨344618091099470364180149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 918981576265254304480397 344618091099470364180149)
                  ·
                    rfl

theorem cell20_755034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_755034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755034 prefixEnd_755034 := by exact prefixLift 755034
  have htrace : WordTrace (prefixWord ++ tailWord_755034) baseStart_755034 baseEnd_755034 := by
    simpa [prefixWord, tailWord_755034, baseEnd_755034] using wordTrace_append hprefix tailTrace_755034
  have hstable : (prefixWord ++ tailWord_755034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755034).length < 2 ^ (prefixWord ++ tailWord_755034).sum := by decide
  have hdescent : baseEnd_755034 < baseStart_755034 := by decide
  rcases family_descends (prefixWord ++ tailWord_755034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755044 : List Nat := [2, 3, 1, 1, 3, 4, 2, 4]
def baseStart_755044 : Nat := 118140960795 + 755044 * 2 ^ 59
def prefixEnd_755044 : Nat := 4983230072969 + 3 ^ 40 * 755044 * 2
def baseEnd_755044 : Nat := 114874218457318257948925

theorem tailTrace_755044 : CollatzResearch.WordTrace tailWord_755044 prefixEnd_755044 114874218457318257948925 := by
  unfold tailWord_755044
  simp only [CollatzResearch.WordTrace]
  refine ⟨13769358538306007046988093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18359144717741342729317457 13769358538306007046988093)
  ·
    refine ⟨5163509451864752642620535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13769358538306007046988093 5163509451864752642620535)
    ·
      refine ⟨7745264177797128963930803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5163509451864752642620535 7745264177797128963930803)
      ·
        refine ⟨11617896266695693445896205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7745264177797128963930803 11617896266695693445896205)
        ·
          refine ⟨4356711100010885042211077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11617896266695693445896205 4356711100010885042211077)
          ·
            refine ⟨816883331252040945414577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4356711100010885042211077 816883331252040945414577)
            ·
              refine ⟨612662498439030709060933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816883331252040945414577 612662498439030709060933)
              ·
                refine ⟨114874218457318257948925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 612662498439030709060933 114874218457318257948925)
                ·
                  rfl

theorem cell20_755044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_755044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755044 prefixEnd_755044 := by exact prefixLift 755044
  have htrace : WordTrace (prefixWord ++ tailWord_755044) baseStart_755044 baseEnd_755044 := by
    simpa [prefixWord, tailWord_755044, baseEnd_755044] using wordTrace_append hprefix tailTrace_755044
  have hstable : (prefixWord ++ tailWord_755044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755044).length < 2 ^ (prefixWord ++ tailWord_755044).sum := by decide
  have hdescent : baseEnd_755044 < baseStart_755044 := by decide
  rcases family_descends (prefixWord ++ tailWord_755044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755055 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 7]
def baseStart_755055 : Nat := 118140960795 + 755055 * 2 ^ 59
def prefixEnd_755055 : Nat := 4983230072969 + 3 ^ 40 * 755055 * 2
def baseEnd_755055 : Nat := 344627676071687624480063

theorem tailTrace_755055 : CollatzResearch.WordTrace tailWord_755055 prefixEnd_755055 344627676071687624480063 := by
  unfold tailWord_755055
  simp only [CollatzResearch.WordTrace]
  refine ⟨27539118279572162972626619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18359412186381441981751079 27539118279572162972626619)
  ·
    refine ⟨41308677419358244458939929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27539118279572162972626619 41308677419358244458939929)
    ·
      refine ⟨30981508064518683344204947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41308677419358244458939929 30981508064518683344204947)
      ·
        refine ⟨46472262096778025016307421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30981508064518683344204947 46472262096778025016307421)
        ·
          refine ⟨17427098286291759381115283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46472262096778025016307421 17427098286291759381115283)
          ·
            refine ⟨26140647429437639071672925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17427098286291759381115283 26140647429437639071672925)
            ·
              refine ⟨9802742786039114651877347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26140647429437639071672925 9802742786039114651877347)
              ·
                refine ⟨14704114179058671977816021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9802742786039114651877347 14704114179058671977816021)
                ·
                  refine ⟨344627676071687624480063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14704114179058671977816021 344627676071687624480063)
                  ·
                    rfl

theorem cell20_755055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_755055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755055 prefixEnd_755055 := by exact prefixLift 755055
  have htrace : WordTrace (prefixWord ++ tailWord_755055) baseStart_755055 baseEnd_755055 := by
    simpa [prefixWord, tailWord_755055, baseEnd_755055] using wordTrace_append hprefix tailTrace_755055
  have hstable : (prefixWord ++ tailWord_755055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755055).length < 2 ^ (prefixWord ++ tailWord_755055).sum := by decide
  have hdescent : baseEnd_755055 < baseStart_755055 := by decide
  rcases family_descends (prefixWord ++ tailWord_755055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755189 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 4]
def baseStart_755189 : Nat := 118140960795 + 755189 * 2 ^ 59
def prefixEnd_755189 : Nat := 4983230072969 + 3 ^ 40 * 755189 * 2
def baseEnd_755189 : Nat := 344688837322978714012849

theorem tailTrace_755189 : CollatzResearch.WordTrace tailWord_755189 prefixEnd_755189 344688837322978714012849 := by
  unfold tailWord_755189
  simp only [CollatzResearch.WordTrace]
  refine ⟨27544005661086703858004621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18362670440724469238669747 27544005661086703858004621)
  ·
    refine ⟨10329002122907513946751733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27544005661086703858004621 10329002122907513946751733)
    ·
      refine ⟨968343949022579432507975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10329002122907513946751733 968343949022579432507975)
      ·
        refine ⟨1452515923533869148761963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968343949022579432507975 1452515923533869148761963)
        ·
          refine ⟨2178773885300803723142945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452515923533869148761963 2178773885300803723142945)
          ·
            refine ⟨1634080413975602792357209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2178773885300803723142945 1634080413975602792357209)
            ·
              refine ⟨1225560310481702094267907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1634080413975602792357209 1225560310481702094267907)
              ·
                refine ⟨1838340465722553141401861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225560310481702094267907 1838340465722553141401861)
                ·
                  refine ⟨344688837322978714012849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1838340465722553141401861 344688837322978714012849)
                  ·
                    rfl

theorem cell20_755189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_755189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755189 prefixEnd_755189 := by exact prefixLift 755189
  have htrace : WordTrace (prefixWord ++ tailWord_755189) baseStart_755189 baseEnd_755189 := by
    simpa [prefixWord, tailWord_755189, baseEnd_755189] using wordTrace_append hprefix tailTrace_755189
  have hstable : (prefixWord ++ tailWord_755189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755189).length < 2 ^ (prefixWord ++ tailWord_755189).sum := by decide
  have hdescent : baseEnd_755189 < baseStart_755189 := by decide
  rcases family_descends (prefixWord ++ tailWord_755189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755213 : List Nat := [1, 7, 1, 1, 2, 1, 1, 6]
def baseStart_755213 : Nat := 118140960795 + 755213 * 2 ^ 59
def prefixEnd_755213 : Nat := 4983230072969 + 3 ^ 40 * 755213 * 2
def baseEnd_755213 : Nat := 114899930525647099070917

theorem tailTrace_755213 : CollatzResearch.WordTrace tailWord_755213 prefixEnd_755213 114899930525647099070917 := by
  unfold tailWord_755213
  simp only [CollatzResearch.WordTrace]
  refine ⟨27544881012999755956878293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18363254008666503971252195 27544881012999755956878293)
  ·
    refine ⟨645583148742181780239335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 27544881012999755956878293 645583148742181780239335)
    ·
      refine ⟨968374723113272670359003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 645583148742181780239335 968374723113272670359003)
      ·
        refine ⟨1452562084669909005538505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968374723113272670359003 1452562084669909005538505)
        ·
          refine ⟨1089421563502431754153879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1452562084669909005538505 1089421563502431754153879)
          ·
            refine ⟨1634132345253647631230819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089421563502431754153879 1634132345253647631230819)
            ·
              refine ⟨2451198517880471446846229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1634132345253647631230819 2451198517880471446846229)
              ·
                refine ⟨114899930525647099070917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2451198517880471446846229 114899930525647099070917)
                ·
                  rfl

theorem cell20_755213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 6].length) (baseStart_755213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755213 prefixEnd_755213 := by exact prefixLift 755213
  have htrace : WordTrace (prefixWord ++ tailWord_755213) baseStart_755213 baseEnd_755213 := by
    simpa [prefixWord, tailWord_755213, baseEnd_755213] using wordTrace_append hprefix tailTrace_755213
  have hstable : (prefixWord ++ tailWord_755213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755213).length < 2 ^ (prefixWord ++ tailWord_755213).sum := by decide
  have hdescent : baseEnd_755213 < baseStart_755213 := by decide
  rcases family_descends (prefixWord ++ tailWord_755213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755230 : List Nat := [4, 3, 3, 1, 1, 2, 6]
def baseStart_755230 : Nat := 118140960795 + 755230 * 2 ^ 59
def prefixEnd_755230 : Nat := 4983230072969 + 3 ^ 40 * 755230 * 2
def baseEnd_755230 : Nat := 38300838982240532627335

theorem tailTrace_755230 : CollatzResearch.WordTrace tailWord_755230 prefixEnd_755230 38300838982240532627335 := by
  unfold tailWord_755230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3443187631742270982530893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18363667369292111906831429 3443187631742270982530893)
  ·
    refine ⟨1291195361903351618449085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3443187631742270982530893 1291195361903351618449085)
    ·
      refine ⟨484198260713756856918407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1291195361903351618449085 484198260713756856918407)
      ·
        refine ⟨726297391070635285377611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484198260713756856918407 726297391070635285377611)
        ·
          refine ⟨1089446086605952928066417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726297391070635285377611 1089446086605952928066417)
          ·
            refine ⟨817084564954464696049813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1089446086605952928066417 817084564954464696049813)
            ·
              refine ⟨38300838982240532627335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 817084564954464696049813 38300838982240532627335)
              ·
                rfl

theorem cell20_755230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 6].length) (baseStart_755230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755230 prefixEnd_755230 := by exact prefixLift 755230
  have htrace : WordTrace (prefixWord ++ tailWord_755230) baseStart_755230 baseEnd_755230 := by
    simpa [prefixWord, tailWord_755230, baseEnd_755230] using wordTrace_append hprefix tailTrace_755230
  have hstable : (prefixWord ++ tailWord_755230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755230).length < 2 ^ (prefixWord ++ tailWord_755230).sum := by decide
  have hdescent : baseEnd_755230 < baseStart_755230 := by decide
  rcases family_descends (prefixWord ++ tailWord_755230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755254 : List Nat := [5, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_755254 : Nat := 118140960795 + 755254 * 2 ^ 59
def prefixEnd_755254 : Nat := 4983230072969 + 3 ^ 40 * 755254 * 2
def baseEnd_755254 : Nat := 344718505094127376845917

theorem tailTrace_755254 : CollatzResearch.WordTrace tailWord_755254 prefixEnd_755254 344718505094127376845917 := by
  unfold tailWord_755254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1721648525365701247445051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18364250937234146639413877 1721648525365701247445051)
  ·
    refine ⟨2582472788048551871167577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1721648525365701247445051 2582472788048551871167577)
    ·
      refine ⟨1936854591036413903375683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2582472788048551871167577 1936854591036413903375683)
      ·
        refine ⟨2905281886554620855063525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1936854591036413903375683 2905281886554620855063525)
        ·
          refine ⟨544740353728991410324411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2905281886554620855063525 544740353728991410324411)
          ·
            refine ⟨817110530593487115486617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544740353728991410324411 817110530593487115486617)
            ·
              refine ⟨612832897945115336614963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817110530593487115486617 612832897945115336614963)
              ·
                refine ⟨919249346917673004922445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612832897945115336614963 919249346917673004922445)
                ·
                  refine ⟨344718505094127376845917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919249346917673004922445 344718505094127376845917)
                  ·
                    rfl

theorem cell20_755254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_755254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755254 prefixEnd_755254 := by exact prefixLift 755254
  have htrace : WordTrace (prefixWord ++ tailWord_755254) baseStart_755254 baseEnd_755254 := by
    simpa [prefixWord, tailWord_755254, baseEnd_755254] using wordTrace_append hprefix tailTrace_755254
  have hstable : (prefixWord ++ tailWord_755254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755254).length < 2 ^ (prefixWord ++ tailWord_755254).sum := by decide
  have hdescent : baseEnd_755254 < baseStart_755254 := by decide
  rcases family_descends (prefixWord ++ tailWord_755254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755276 : List Nat := [2, 2, 1, 3, 1, 3, 2, 6]
def baseStart_755276 : Nat := 118140960795 + 755276 * 2 ^ 59
def prefixEnd_755276 : Nat := 4983230072969 + 3 ^ 40 * 755276 * 2
def baseEnd_755276 : Nat := 114909515497864359370831

theorem tailTrace_755276 : CollatzResearch.WordTrace tailWord_755276 prefixEnd_755276 114909515497864359370831 := by
  unfold tailWord_755276
  simp only [CollatzResearch.WordTrace]
  refine ⟨13773589405885758858210841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18364785874514345144281121 13773589405885758858210841)
  ·
    refine ⟨10330192054414319143658131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13773589405885758858210841 10330192054414319143658131)
    ·
      refine ⟨15495288081621478715487197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10330192054414319143658131 15495288081621478715487197)
      ·
        refine ⟨5810733030608054518307699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15495288081621478715487197 5810733030608054518307699)
        ·
          refine ⟨8716099545912081777461549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5810733030608054518307699 8716099545912081777461549)
          ·
            refine ⟨3268537329717030666548081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8716099545912081777461549 3268537329717030666548081)
            ·
              refine ⟨2451402997287772999911061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3268537329717030666548081 2451402997287772999911061)
              ·
                refine ⟨114909515497864359370831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2451402997287772999911061 114909515497864359370831)
                ·
                  rfl

theorem cell20_755276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_755276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755276 prefixEnd_755276 := by exact prefixLift 755276
  have htrace : WordTrace (prefixWord ++ tailWord_755276) baseStart_755276 baseEnd_755276 := by
    simpa [prefixWord, tailWord_755276, baseEnd_755276] using wordTrace_append hprefix tailTrace_755276
  have hstable : (prefixWord ++ tailWord_755276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755276).length < 2 ^ (prefixWord ++ tailWord_755276).sum := by decide
  have hdescent : baseEnd_755276 < baseStart_755276 := by decide
  rcases family_descends (prefixWord ++ tailWord_755276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755293 : List Nat := [1, 4, 4, 2, 9]
def baseStart_755293 : Nat := 118140960795 + 755293 * 2 ^ 59
def prefixEnd_755293 : Nat := 4983230072969 + 3 ^ 40 * 755293 * 2
def baseEnd_755293 : Nat := 4256003774775513265997

theorem tailTrace_755293 : CollatzResearch.WordTrace tailWord_755293 prefixEnd_755293 4256003774775513265997 := by
  unfold tailWord_755293
  simp only [CollatzResearch.WordTrace]
  refine ⟨27547798852709929619790533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18365199235139953079860355 27547798852709929619790533)
  ·
    refine ⟨5165212284883111803710725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27547798852709929619790533 5165212284883111803710725)
    ·
      refine ⟨968477303415583463195761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5165212284883111803710725 968477303415583463195761)
      ·
        refine ⟨726357977561687597396821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 968477303415583463195761 726357977561687597396821)
        ·
          refine ⟨4256003774775513265997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 726357977561687597396821 4256003774775513265997)
          ·
            rfl

theorem cell20_755293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 9].length) (baseStart_755293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755293 prefixEnd_755293 := by exact prefixLift 755293
  have htrace : WordTrace (prefixWord ++ tailWord_755293) baseStart_755293 baseEnd_755293 := by
    simpa [prefixWord, tailWord_755293, baseEnd_755293] using wordTrace_append hprefix tailTrace_755293
  have hstable : (prefixWord ++ tailWord_755293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755293).length < 2 ^ (prefixWord ++ tailWord_755293).sum := by decide
  have hdescent : baseEnd_755293 < baseStart_755293 := by decide
  rcases family_descends (prefixWord ++ tailWord_755293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755300 : List Nat := [2, 3, 1, 1, 2, 3, 1, 4, 3]
def baseStart_755300 : Nat := 118140960795 + 755300 * 2 ^ 59
def prefixEnd_755300 : Nat := 4983230072969 + 3 ^ 40 * 755300 * 2
def baseEnd_755300 : Nat := 344739500747555661312395

theorem tailTrace_755300 : CollatzResearch.WordTrace tailWord_755300 prefixEnd_755300 344739500747555661312395 := by
  unfold tailWord_755300
  simp only [CollatzResearch.WordTrace]
  refine ⟨13774027081842284907647677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18365369442456379876863569 13774027081842284907647677)
  ·
    refine ⟨5165260155690856840367879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13774027081842284907647677 5165260155690856840367879)
    ·
      refine ⟨7747890233536285260551819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5165260155690856840367879 7747890233536285260551819)
      ·
        refine ⟨11621835350304427890827729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7747890233536285260551819 11621835350304427890827729)
        ·
          refine ⟨8716376512728320918120797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11621835350304427890827729 8716376512728320918120797)
          ·
            refine ⟨3268641192273120344295299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8716376512728320918120797 3268641192273120344295299)
            ·
              refine ⟨4902961788409680516442949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3268641192273120344295299 4902961788409680516442949)
              ·
                refine ⟨919305335326815096833053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4902961788409680516442949 919305335326815096833053)
                ·
                  refine ⟨344739500747555661312395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919305335326815096833053 344739500747555661312395)
                  ·
                    rfl

theorem cell20_755300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_755300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755300 prefixEnd_755300 := by exact prefixLift 755300
  have htrace : WordTrace (prefixWord ++ tailWord_755300) baseStart_755300 baseEnd_755300 := by
    simpa [prefixWord, tailWord_755300, baseEnd_755300] using wordTrace_append hprefix tailTrace_755300
  have hstable : (prefixWord ++ tailWord_755300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755300).length < 2 ^ (prefixWord ++ tailWord_755300).sum := by decide
  have hdescent : baseEnd_755300 < baseStart_755300 := by decide
  rcases family_descends (prefixWord ++ tailWord_755300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755303 : List Nat := [1, 1, 5, 1, 1, 1, 6, 2, 2]
def baseStart_755303 : Nat := 118140960795 + 755303 * 2 ^ 59
def prefixEnd_755303 : Nat := 4983230072969 + 3 ^ 40 * 755303 * 2
def baseEnd_755303 : Nat := 344740870029300984212383

theorem tailTrace_755303 : CollatzResearch.WordTrace tailWord_755303 prefixEnd_755303 344740870029300984212383 := by
  unfold tailWord_755303
  simp only [CollatzResearch.WordTrace]
  refine ⟨27548163582673701327654563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18365442388449134218436375 27548163582673701327654563)
  ·
    refine ⟨41322245374010551991481845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27548163582673701327654563 41322245374010551991481845)
    ·
      refine ⟨3873960503813489249201423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41322245374010551991481845 3873960503813489249201423)
      ·
        refine ⟨5810940755720233873802135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3873960503813489249201423 5810940755720233873802135)
        ·
          refine ⟨8716411133580350810703203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5810940755720233873802135 8716411133580350810703203)
          ·
            refine ⟨13074616700370526216054805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8716411133580350810703203 13074616700370526216054805)
            ·
              refine ⟨612872657829868416377569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13074616700370526216054805 612872657829868416377569)
              ·
                refine ⟨459654493372401312283177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612872657829868416377569 459654493372401312283177)
                ·
                  refine ⟨344740870029300984212383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459654493372401312283177 344740870029300984212383)
                  ·
                    rfl

theorem cell20_755303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 2].length) (baseStart_755303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755303 prefixEnd_755303 := by exact prefixLift 755303
  have htrace : WordTrace (prefixWord ++ tailWord_755303) baseStart_755303 baseEnd_755303 := by
    simpa [prefixWord, tailWord_755303, baseEnd_755303] using wordTrace_append hprefix tailTrace_755303
  have hstable : (prefixWord ++ tailWord_755303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755303).length < 2 ^ (prefixWord ++ tailWord_755303).sum := by decide
  have hdescent : baseEnd_755303 < baseStart_755303 := by decide
  rcases family_descends (prefixWord ++ tailWord_755303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755310 : List Nat := [4, 1, 2, 2, 3, 2, 1, 5]
def baseStart_755310 : Nat := 118140960795 + 755310 * 2 ^ 59
def prefixEnd_755310 : Nat := 4983230072969 + 3 ^ 40 * 755310 * 2
def baseEnd_755310 : Nat := 114914688340013356993007

theorem tailTrace_755310 : CollatzResearch.WordTrace tailWord_755310 prefixEnd_755310 114914688340013356993007 := by
  unfold tailWord_755310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3443552361706042690394923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18365612595765561015439589 3443552361706042690394923)
  ·
    refine ⟨5165328542559064035592385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3443552361706042690394923 5165328542559064035592385)
    ·
      refine ⟨3873996406919298026694289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5165328542559064035592385 3873996406919298026694289)
      ·
        refine ⟨2905497305189473520020717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3873996406919298026694289 2905497305189473520020717)
        ·
          refine ⟨1089561489446052570007769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2905497305189473520020717 1089561489446052570007769)
          ·
            refine ⟨817171117084539427505827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1089561489446052570007769 817171117084539427505827)
            ·
              refine ⟨1225756675626809141258741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817171117084539427505827 1225756675626809141258741)
              ·
                refine ⟨114914688340013356993007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1225756675626809141258741 114914688340013356993007)
                ·
                  rfl

theorem cell20_755310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_755310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755310 prefixEnd_755310 := by exact prefixLift 755310
  have htrace : WordTrace (prefixWord ++ tailWord_755310) baseStart_755310 baseEnd_755310 := by
    simpa [prefixWord, tailWord_755310, baseEnd_755310] using wordTrace_append hprefix tailTrace_755310
  have hstable : (prefixWord ++ tailWord_755310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755310).length < 2 ^ (prefixWord ++ tailWord_755310).sum := by decide
  have hdescent : baseEnd_755310 < baseStart_755310 := by decide
  rcases family_descends (prefixWord ++ tailWord_755310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755317 : List Nat := [1, 3, 4, 2, 1, 1, 2, 3, 3]
def baseStart_755317 : Nat := 118140960795 + 755317 * 2 ^ 59
def prefixEnd_755317 : Nat := 4983230072969 + 3 ^ 40 * 755317 * 2
def baseEnd_755317 : Nat := 344747260010779157745659

theorem tailTrace_755317 : CollatzResearch.WordTrace tailWord_755317 prefixEnd_755317 344747260010779157745659 := by
  unfold tailWord_755317
  simp only [CollatzResearch.WordTrace]
  refine ⟨27548674204622981718664205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18365782803081987812442803 27548674204622981718664205)
  ·
    refine ⟨10330752826733618144499077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27548674204622981718664205 10330752826733618144499077)
    ·
      refine ⟨1937016155012553402093577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10330752826733618144499077 1937016155012553402093577)
      ·
        refine ⟨1452762116259415051570183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1937016155012553402093577 1452762116259415051570183)
        ·
          refine ⟨2179143174389122577355275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452762116259415051570183 2179143174389122577355275)
          ·
            refine ⟨3268714761583683866032913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2179143174389122577355275 3268714761583683866032913)
            ·
              refine ⟨2451536071187762899524685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3268714761583683866032913 2451536071187762899524685)
              ·
                refine ⟨919326026695411087321757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2451536071187762899524685 919326026695411087321757)
                ·
                  refine ⟨344747260010779157745659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919326026695411087321757 344747260010779157745659)
                  ·
                    rfl

theorem cell20_755317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_755317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755317 prefixEnd_755317 := by exact prefixLift 755317
  have htrace : WordTrace (prefixWord ++ tailWord_755317) baseStart_755317 baseEnd_755317 := by
    simpa [prefixWord, tailWord_755317, baseEnd_755317] using wordTrace_append hprefix tailTrace_755317
  have hstable : (prefixWord ++ tailWord_755317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755317).length < 2 ^ (prefixWord ++ tailWord_755317).sum := by decide
  have hdescent : baseEnd_755317 < baseStart_755317 := by decide
  rcases family_descends (prefixWord ++ tailWord_755317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755352 : List Nat := [2, 1, 2, 4, 1, 3, 7]
def baseStart_755352 : Nat := 118140960795 + 755352 * 2 ^ 59
def prefixEnd_755352 : Nat := 4983230072969 + 3 ^ 40 * 755352 * 2
def baseEnd_755352 : Nat := 38307026107163843508761

theorem tailTrace_755352 : CollatzResearch.WordTrace tailWord_755352 prefixEnd_755352 38307026107163843508761 := by
  unfold tailWord_755352
  simp only [CollatzResearch.WordTrace]
  refine ⟨13774975379748091348094155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18366633839664121797458873 13774975379748091348094155)
  ·
    refine ⟨20662463069622137022141233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13774975379748091348094155 20662463069622137022141233)
    ·
      refine ⟨15496847302216602766605925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20662463069622137022141233 15496847302216602766605925)
      ·
        refine ⟨2905658869165613018738611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15496847302216602766605925 2905658869165613018738611)
        ·
          refine ⟨4358488303748419528107917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2905658869165613018738611 4358488303748419528107917)
          ·
            refine ⟨1634433113905657323040469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4358488303748419528107917 1634433113905657323040469)
            ·
              refine ⟨38307026107163843508761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1634433113905657323040469 38307026107163843508761)
              ·
                rfl

theorem cell20_755352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 7].length) (baseStart_755352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755352 prefixEnd_755352 := by exact prefixLift 755352
  have htrace : WordTrace (prefixWord ++ tailWord_755352) baseStart_755352 baseEnd_755352 := by
    simpa [prefixWord, tailWord_755352, baseEnd_755352] using wordTrace_append hprefix tailTrace_755352
  have hstable : (prefixWord ++ tailWord_755352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755352).length < 2 ^ (prefixWord ++ tailWord_755352).sum := by decide
  have hdescent : baseEnd_755352 < baseStart_755352 := by decide
  rcases family_descends (prefixWord ++ tailWord_755352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755368 : List Nat := [2, 1, 7, 1, 1, 1, 3, 1, 3]
def baseStart_755368 : Nat := 118140960795 + 755368 * 2 ^ 59
def prefixEnd_755368 : Nat := 4983230072969 + 3 ^ 40 * 755368 * 2
def baseEnd_755368 : Nat := 344770537800449647045451

theorem tailTrace_755368 : CollatzResearch.WordTrace tailWord_755368 prefixEnd_755368 344770537800449647045451 := by
  unfold tailWord_755368
  simp only [CollatzResearch.WordTrace]
  refine ⟨13775267163719108714385379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18367022884958811619180505 13775267163719108714385379)
  ·
    refine ⟨20662900745578663071578069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13775267163719108714385379 20662900745578663071578069)
    ·
      refine ⟨484286736224499915740111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 20662900745578663071578069 484286736224499915740111)
      ·
        refine ⟨726430104336749873610167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484286736224499915740111 726430104336749873610167)
        ·
          refine ⟨1089645156505124810415251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726430104336749873610167 1089645156505124810415251)
          ·
            refine ⟨1634467734757687215622877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089645156505124810415251 1634467734757687215622877)
            ·
              refine ⟨612925400534132705858579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1634467734757687215622877 612925400534132705858579)
              ·
                refine ⟨919388100801199058787869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612925400534132705858579 919388100801199058787869)
                ·
                  refine ⟨344770537800449647045451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919388100801199058787869 344770537800449647045451)
                  ·
                    rfl

theorem cell20_755368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 3].length) (baseStart_755368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755368 prefixEnd_755368 := by exact prefixLift 755368
  have htrace : WordTrace (prefixWord ++ tailWord_755368) baseStart_755368 baseEnd_755368 := by
    simpa [prefixWord, tailWord_755368, baseEnd_755368] using wordTrace_append hprefix tailTrace_755368
  have hstable : (prefixWord ++ tailWord_755368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755368).length < 2 ^ (prefixWord ++ tailWord_755368).sum := by decide
  have hdescent : baseEnd_755368 < baseStart_755368 := by decide
  rcases family_descends (prefixWord ++ tailWord_755368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755383 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 4]
def baseStart_755383 : Nat := 118140960795 + 755383 * 2 ^ 59
def prefixEnd_755383 : Nat := 4983230072969 + 3 ^ 40 * 755383 * 2
def baseEnd_755383 : Nat := 344777384209176261545389

theorem tailTrace_755383 : CollatzResearch.WordTrace tailWord_755383 prefixEnd_755383 344777384209176261545389 := by
  unfold tailWord_755383
  simp only [CollatzResearch.WordTrace]
  refine ⟨27551081422383874990566803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18367387614922583327044535 27551081422383874990566803)
  ·
    refine ⟨41326622133575812485850205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27551081422383874990566803 41326622133575812485850205)
    ·
      refine ⟨15497483300090929682193827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41326622133575812485850205 15497483300090929682193827)
      ·
        refine ⟨23246224950136394523290741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15497483300090929682193827 23246224950136394523290741)
        ·
          refine ⟨2179333589075286986558507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23246224950136394523290741 2179333589075286986558507)
          ·
            refine ⟨3269000383612930479837761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2179333589075286986558507 3269000383612930479837761)
            ·
              refine ⟨2451750287709697859878321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3269000383612930479837761 2451750287709697859878321)
              ·
                refine ⟨1838812715782273394908741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2451750287709697859878321 1838812715782273394908741)
                ·
                  refine ⟨344777384209176261545389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1838812715782273394908741 344777384209176261545389)
                  ·
                    rfl

theorem cell20_755383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_755383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755383 prefixEnd_755383 := by exact prefixLift 755383
  have htrace : WordTrace (prefixWord ++ tailWord_755383) baseStart_755383 baseEnd_755383 := by
    simpa [prefixWord, tailWord_755383, baseEnd_755383] using wordTrace_append hprefix tailTrace_755383
  have hstable : (prefixWord ++ tailWord_755383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755383).length < 2 ^ (prefixWord ++ tailWord_755383).sum := by decide
  have hdescent : baseEnd_755383 < baseStart_755383 := by decide
  rcases family_descends (prefixWord ++ tailWord_755383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755417 : List Nat := [1, 2, 1, 2, 3, 4, 3, 2, 2]
def baseStart_755417 : Nat := 118140960795 + 755417 * 2 ^ 59
def prefixEnd_755417 : Nat := 4983230072969 + 3 ^ 40 * 755417 * 2
def baseEnd_755417 : Nat := 344792902735623254411917

theorem tailTrace_755417 : CollatzResearch.WordTrace tailWord_755417 prefixEnd_755417 344792902735623254411917 := by
  unfold tailWord_755417
  simp only [CollatzResearch.WordTrace]
  refine ⟨27552321504260698797304505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18368214336173799198203003 27552321504260698797304505)
  ·
    refine ⟨20664241128195524097978379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27552321504260698797304505 20664241128195524097978379)
    ·
      refine ⟨30996361692293286146967569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20664241128195524097978379 30996361692293286146967569)
      ·
        refine ⟨23247271269219964610225677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30996361692293286146967569 23247271269219964610225677)
        ·
          refine ⟨8717726725957486728834629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23247271269219964610225677 8717726725957486728834629)
          ·
            refine ⟨1634573761117028761656493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8717726725957486728834629 1634573761117028761656493)
            ·
              refine ⟨612965160418885785621185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1634573761117028761656493 612965160418885785621185)
              ·
                refine ⟨459723870314164339215889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612965160418885785621185 459723870314164339215889)
                ·
                  refine ⟨344792902735623254411917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459723870314164339215889 344792902735623254411917)
                  ·
                    rfl

theorem cell20_755417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 2].length) (baseStart_755417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755417 prefixEnd_755417 := by exact prefixLift 755417
  have htrace : WordTrace (prefixWord ++ tailWord_755417) baseStart_755417 baseEnd_755417 := by
    simpa [prefixWord, tailWord_755417, baseEnd_755417] using wordTrace_append hprefix tailTrace_755417
  have hstable : (prefixWord ++ tailWord_755417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755417).length < 2 ^ (prefixWord ++ tailWord_755417).sum := by decide
  have hdescent : baseEnd_755417 < baseStart_755417 := by decide
  rcases family_descends (prefixWord ++ tailWord_755417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755427 : List Nat := [1, 1, 1, 7, 3, 1, 2, 1, 3]
def baseStart_755427 : Nat := 118140960795 + 755427 * 2 ^ 59
def prefixEnd_755427 : Nat := 4983230072969 + 3 ^ 40 * 755427 * 2
def baseEnd_755427 : Nat := 344797467008107664078543

theorem tailTrace_755427 : CollatzResearch.WordTrace tailWord_755427 prefixEnd_755427 344797467008107664078543 := by
  unfold tailWord_755427
  simp only [CollatzResearch.WordTrace]
  refine ⟨27552686234224470505168535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18368457489482980336779023 27552686234224470505168535)
  ·
    refine ⟨41329029351336705757752803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27552686234224470505168535 41329029351336705757752803)
    ·
      refine ⟨61993544027005058636629205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41329029351336705757752803 61993544027005058636629205)
      ·
        refine ⟨1452973688132931061795997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 61993544027005058636629205 1452973688132931061795997)
        ·
          refine ⟨544865133049849148173499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1452973688132931061795997 544865133049849148173499)
          ·
            refine ⟨817297699574773722260249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544865133049849148173499 817297699574773722260249)
            ·
              refine ⟨612973274681080291695187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817297699574773722260249 612973274681080291695187)
              ·
                refine ⟨919459912021620437542781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612973274681080291695187 919459912021620437542781)
                ·
                  refine ⟨344797467008107664078543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919459912021620437542781 344797467008107664078543)
                  ·
                    rfl

theorem cell20_755427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 3].length) (baseStart_755427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755427 prefixEnd_755427 := by exact prefixLift 755427
  have htrace : WordTrace (prefixWord ++ tailWord_755427) baseStart_755427 baseEnd_755427 := by
    simpa [prefixWord, tailWord_755427, baseEnd_755427] using wordTrace_append hprefix tailTrace_755427
  have hstable : (prefixWord ++ tailWord_755427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755427).length < 2 ^ (prefixWord ++ tailWord_755427).sum := by decide
  have hdescent : baseEnd_755427 < baseStart_755427 := by decide
  rcases family_descends (prefixWord ++ tailWord_755427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755428 : List Nat := [2, 3, 1, 1, 1, 3, 4, 5]
def baseStart_755428 : Nat := 118140960795 + 755428 * 2 ^ 59
def prefixEnd_755428 : Nat := 4983230072969 + 3 ^ 40 * 755428 * 2
def baseEnd_755428 : Nat := 114932641145118701681735

theorem tailTrace_755428 : CollatzResearch.WordTrace tailWord_755428 prefixEnd_755428 114932641145118701681735 := by
  unfold tailWord_755428
  simp only [CollatzResearch.WordTrace]
  refine ⟨13776361353610423837977469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18368481804813898450636625 13776361353610423837977469)
  ·
    refine ⟨5166135507603908939241551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13776361353610423837977469 5166135507603908939241551)
    ·
      refine ⟨7749203261405863408862327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5166135507603908939241551 7749203261405863408862327)
      ·
        refine ⟨11623804892108795113293491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7749203261405863408862327 11623804892108795113293491)
        ·
          refine ⟨17435707338163192669940237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11623804892108795113293491 17435707338163192669940237)
          ·
            refine ⟨6538390251811197251227589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17435707338163192669940237 6538390251811197251227589)
            ·
              refine ⟨1225948172214599484605173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6538390251811197251227589 1225948172214599484605173)
              ·
                refine ⟨114932641145118701681735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1225948172214599484605173 114932641145118701681735)
                ·
                  rfl

theorem cell20_755428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_755428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755428 prefixEnd_755428 := by exact prefixLift 755428
  have htrace : WordTrace (prefixWord ++ tailWord_755428) baseStart_755428 baseEnd_755428 := by
    simpa [prefixWord, tailWord_755428, baseEnd_755428] using wordTrace_append hprefix tailTrace_755428
  have hstable : (prefixWord ++ tailWord_755428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755428).length < 2 ^ (prefixWord ++ tailWord_755428).sum := by decide
  have hdescent : baseEnd_755428 < baseStart_755428 := by decide
  rcases family_descends (prefixWord ++ tailWord_755428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755490 : List Nat := [3, 3, 1, 1, 2, 1, 1, 5, 3]
def baseStart_755490 : Nat := 118140960795 + 755490 * 2 ^ 59
def prefixEnd_755490 : Nat := 4983230072969 + 3 ^ 40 * 755490 * 2
def baseEnd_755490 : Nat := 344826221924759444978285

theorem tailTrace_755490 : CollatzResearch.WordTrace tailWord_755490 prefixEnd_755490 344826221924759444978285 := by
  unfold tailWord_755490
  simp only [CollatzResearch.WordTrace]
  refine ⟨6888746008249058066177981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18369989355330821509807949 6888746008249058066177981)
  ·
    refine ⟨2583279753093396774816743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6888746008249058066177981 2583279753093396774816743)
    ·
      refine ⟨3874919629640095162225115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2583279753093396774816743 3874919629640095162225115)
      ·
        refine ⟨5812379444460142743337673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3874919629640095162225115 5812379444460142743337673)
        ·
          refine ⟨4359284583345107057503255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5812379444460142743337673 4359284583345107057503255)
          ·
            refine ⟨6538926875017660586254883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4359284583345107057503255 6538926875017660586254883)
            ·
              refine ⟨9808390312526490879382325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6538926875017660586254883 9808390312526490879382325)
              ·
                refine ⟨919536591799358519942093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9808390312526490879382325 919536591799358519942093)
                ·
                  refine ⟨344826221924759444978285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919536591799358519942093 344826221924759444978285)
                  ·
                    rfl

theorem cell20_755490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_755490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755490 prefixEnd_755490 := by exact prefixLift 755490
  have htrace : WordTrace (prefixWord ++ tailWord_755490) baseStart_755490 baseEnd_755490 := by
    simpa [prefixWord, tailWord_755490, baseEnd_755490] using wordTrace_append hprefix tailTrace_755490
  have hstable : (prefixWord ++ tailWord_755490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755490).length < 2 ^ (prefixWord ++ tailWord_755490).sum := by decide
  have hdescent : baseEnd_755490 < baseStart_755490 := by decide
  rcases family_descends (prefixWord ++ tailWord_755490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755510 : List Nat := [5, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_755510 : Nat := 118140960795 + 755510 * 2 ^ 59
def prefixEnd_755510 : Nat := 4983230072969 + 3 ^ 40 * 755510 * 2
def baseEnd_755510 : Nat := 344835350469728264311537

theorem tailTrace_755510 : CollatzResearch.WordTrace tailWord_755510 prefixEnd_755510 344835350469728264311537 := by
  unfold tailWord_755510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1722232093307735980027499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18370475661949183786959989 1722232093307735980027499)
  ·
    refine ⟨2583348139961603970041249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1722232093307735980027499 2583348139961603970041249)
    ·
      refine ⟨1937511104971202977530937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2583348139961603970041249 1937511104971202977530937)
      ·
        refine ⟨1453133328728402233148203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1937511104971202977530937 1453133328728402233148203)
        ·
          refine ⟨2179699993092603349722305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1453133328728402233148203 2179699993092603349722305)
          ·
            refine ⟨1634774994819452512291729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2179699993092603349722305 1634774994819452512291729)
            ·
              refine ⟨1226081246114589384218797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1634774994819452512291729 1226081246114589384218797)
              ·
                refine ⟨459780467292971019082049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1226081246114589384218797 459780467292971019082049)
                ·
                  refine ⟨344835350469728264311537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459780467292971019082049 344835350469728264311537)
                  ·
                    rfl

theorem cell20_755510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_755510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755510 prefixEnd_755510 := by exact prefixLift 755510
  have htrace : WordTrace (prefixWord ++ tailWord_755510) baseStart_755510 baseEnd_755510 := by
    simpa [prefixWord, tailWord_755510, baseEnd_755510] using wordTrace_append hprefix tailTrace_755510
  have hstable : (prefixWord ++ tailWord_755510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755510).length < 2 ^ (prefixWord ++ tailWord_755510).sum := by decide
  have hdescent : baseEnd_755510 < baseStart_755510 := by decide
  rcases family_descends (prefixWord ++ tailWord_755510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755514 : List Nat := [3, 1, 1, 1, 5, 1, 1, 5, 2]
def baseStart_755514 : Nat := 118140960795 + 755514 * 2 ^ 59
def prefixEnd_755514 : Nat := 4983230072969 + 3 ^ 40 * 755514 * 2
def baseEnd_755514 : Nat := 344837176178722028178187

theorem tailTrace_755514 : CollatzResearch.WordTrace tailWord_755514 prefixEnd_755514 344837176178722028178187 := by
  unfold tailWord_755514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6888964846227321090896399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18370572923272856242390397 6888964846227321090896399)
  ·
    refine ⟨10333447269340981636344599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6888964846227321090896399 10333447269340981636344599)
    ·
      refine ⟨15500170904011472454516899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10333447269340981636344599 15500170904011472454516899)
      ·
        refine ⟨23250256356017208681775349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15500170904011472454516899 23250256356017208681775349)
        ·
          refine ⟨2179711533376613313916439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23250256356017208681775349 2179711533376613313916439)
          ·
            refine ⟨3269567300064919970874659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2179711533376613313916439 3269567300064919970874659)
            ·
              refine ⟨4904350950097379956311989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269567300064919970874659 4904350950097379956311989)
              ·
                refine ⟨459782901571629370904249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4904350950097379956311989 459782901571629370904249)
                ·
                  refine ⟨344837176178722028178187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459782901571629370904249 344837176178722028178187)
                  ·
                    rfl

theorem cell20_755514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_755514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755514 prefixEnd_755514 := by exact prefixLift 755514
  have htrace : WordTrace (prefixWord ++ tailWord_755514) baseStart_755514 baseEnd_755514 := by
    simpa [prefixWord, tailWord_755514, baseEnd_755514] using wordTrace_append hprefix tailTrace_755514
  have hstable : (prefixWord ++ tailWord_755514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755514).length < 2 ^ (prefixWord ++ tailWord_755514).sum := by decide
  have hdescent : baseEnd_755514 < baseStart_755514 := by decide
  rcases family_descends (prefixWord ++ tailWord_755514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755525 : List Nat := [1, 3, 1, 1, 1, 2, 11]
def baseStart_755525 : Nat := 118140960795 + 755525 * 2 ^ 59
def prefixEnd_755525 : Nat := 4983230072969 + 3 ^ 40 * 755525 * 2
def baseEnd_755525 : Nat := 38315799653161653201275

theorem tailTrace_755525 : CollatzResearch.WordTrace tailWord_755525 prefixEnd_755525 38315799653161653201275 := by
  unfold tailWord_755525
  simp only [CollatzResearch.WordTrace]
  refine ⟨27556260587869433242236029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18370840391912955494824019 27556260587869433242236029)
  ·
    refine ⟨10333597720451037465838511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27556260587869433242236029 10333597720451037465838511)
    ·
      refine ⟨15500396580676556198757767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10333597720451037465838511 15500396580676556198757767)
      ·
        refine ⟨23250594871014834298136651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15500396580676556198757767 23250594871014834298136651)
        ·
          refine ⟨34875892306522251447204977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23250594871014834298136651 34875892306522251447204977)
          ·
            refine ⟨26156919229891688585403733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34875892306522251447204977 26156919229891688585403733)
            ·
              refine ⟨38315799653161653201275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26156919229891688585403733 38315799653161653201275)
              ·
                rfl

theorem cell20_755525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 11].length) (baseStart_755525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755525 prefixEnd_755525 := by exact prefixLift 755525
  have htrace : WordTrace (prefixWord ++ tailWord_755525) baseStart_755525 baseEnd_755525 := by
    simpa [prefixWord, tailWord_755525, baseEnd_755525] using wordTrace_append hprefix tailTrace_755525
  have hstable : (prefixWord ++ tailWord_755525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755525).length < 2 ^ (prefixWord ++ tailWord_755525).sum := by decide
  have hdescent : baseEnd_755525 < baseStart_755525 := by decide
  rcases family_descends (prefixWord ++ tailWord_755525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755528 : List Nat := [2, 1, 3, 1, 1, 4, 3, 2, 3]
def baseStart_755528 : Nat := 118140960795 + 755528 * 2 ^ 59
def prefixEnd_755528 : Nat := 4983230072969 + 3 ^ 40 * 755528 * 2
def baseEnd_755528 : Nat := 344843566160200201711463

theorem tailTrace_755528 : CollatzResearch.WordTrace tailWord_755528 prefixEnd_755528 344843566160200201711463 := by
  unfold tailWord_755528
  simp only [CollatzResearch.WordTrace]
  refine ⟨13778185003429282377297619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18370913337905709836396825 13778185003429282377297619)
  ·
    refine ⟨20667277505143923565946429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13778185003429282377297619 20667277505143923565946429)
    ·
      refine ⟨7750229064428971337229911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20667277505143923565946429 7750229064428971337229911)
      ·
        refine ⟨11625343596643457005844867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7750229064428971337229911 11625343596643457005844867)
        ·
          refine ⟨17438015394965185508767301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11625343596643457005844867 17438015394965185508767301)
          ·
            refine ⟨3269627886555972282893869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17438015394965185508767301 3269627886555972282893869)
            ·
              refine ⟨1226110457458489606085201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3269627886555972282893869 1226110457458489606085201)
              ·
                refine ⟨919582843093867204563901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226110457458489606085201 919582843093867204563901)
                ·
                  refine ⟨344843566160200201711463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919582843093867204563901 344843566160200201711463)
                  ·
                    rfl

theorem cell20_755528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_755528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755528 prefixEnd_755528 := by exact prefixLift 755528
  have htrace : WordTrace (prefixWord ++ tailWord_755528) baseStart_755528 baseEnd_755528 := by
    simpa [prefixWord, tailWord_755528, baseEnd_755528] using wordTrace_append hprefix tailTrace_755528
  have hstable : (prefixWord ++ tailWord_755528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755528).length < 2 ^ (prefixWord ++ tailWord_755528).sum := by decide
  have hdescent : baseEnd_755528 < baseStart_755528 := by decide
  rcases family_descends (prefixWord ++ tailWord_755528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755566 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_755566 : Nat := 118140960795 + 755566 * 2 ^ 59
def prefixEnd_755566 : Nat := 4983230072969 + 3 ^ 40 * 755566 * 2
def baseEnd_755566 : Nat := 344860910395640958444641

theorem tailTrace_755566 : CollatzResearch.WordTrace tailWord_755566 prefixEnd_755566 344860910395640958444641 := by
  unfold tailWord_755566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3444719497590112155559819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18371837320480598162985701 3444719497590112155559819)
  ·
    refine ⟨5167079246385168233339729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3444719497590112155559819 5167079246385168233339729)
    ·
      refine ⟨3875309434788876175004797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5167079246385168233339729 3875309434788876175004797)
      ·
        refine ⟨1453241038045828565626799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3875309434788876175004797 1453241038045828565626799)
        ·
          refine ⟨2179861557068742848440199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1453241038045828565626799 2179861557068742848440199)
          ·
            refine ⟨3269792335603114272660299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2179861557068742848440199 3269792335603114272660299)
            ·
              refine ⟨4904688503404671408990449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269792335603114272660299 4904688503404671408990449)
              ·
                refine ⟨3678516377553503556742837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4904688503404671408990449 3678516377553503556742837)
                ·
                  refine ⟨344860910395640958444641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3678516377553503556742837 344860910395640958444641)
                  ·
                    rfl

theorem cell20_755566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_755566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755566 prefixEnd_755566 := by exact prefixLift 755566
  have htrace : WordTrace (prefixWord ++ tailWord_755566) baseStart_755566 baseEnd_755566 := by
    simpa [prefixWord, tailWord_755566, baseEnd_755566] using wordTrace_append hprefix tailTrace_755566
  have hstable : (prefixWord ++ tailWord_755566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755566).length < 2 ^ (prefixWord ++ tailWord_755566).sum := by decide
  have hdescent : baseEnd_755566 < baseStart_755566 := by decide
  rcases family_descends (prefixWord ++ tailWord_755566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755587 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 5]
def baseStart_755587 : Nat := 118140960795 + 755587 * 2 ^ 59
def prefixEnd_755587 : Nat := 4983230072969 + 3 ^ 40 * 755587 * 2
def baseEnd_755587 : Nat := 344870495367858218744555

theorem tailTrace_755587 : CollatzResearch.WordTrace tailWord_755587 prefixEnd_755587 344870495367858218744555 := by
  unfold tailWord_755587
  simp only [CollatzResearch.WordTrace]
  refine ⟨27558521913644817830993015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18372347942429878553995343 27558521913644817830993015)
  ·
    refine ⟨41337782870467226746489523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27558521913644817830993015 41337782870467226746489523)
    ·
      refine ⟨62006674305700840119734285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41337782870467226746489523 62006674305700840119734285)
      ·
        refine ⟨23252502864637815044900357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62006674305700840119734285 23252502864637815044900357)
        ·
          refine ⟨4359844287119590320918817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23252502864637815044900357 4359844287119590320918817)
          ·
            refine ⟨3269883215339692740689113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4359844287119590320918817 3269883215339692740689113)
            ·
              refine ⟨2452412411504769555516835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3269883215339692740689113 2452412411504769555516835)
              ·
                refine ⟨3678618617257154333275253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2452412411504769555516835 3678618617257154333275253)
                ·
                  refine ⟨344870495367858218744555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3678618617257154333275253 344870495367858218744555)
                  ·
                    rfl

theorem cell20_755587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_755587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755587 prefixEnd_755587 := by exact prefixLift 755587
  have htrace : WordTrace (prefixWord ++ tailWord_755587) baseStart_755587 baseEnd_755587 := by
    simpa [prefixWord, tailWord_755587, baseEnd_755587] using wordTrace_append hprefix tailTrace_755587
  have hstable : (prefixWord ++ tailWord_755587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755587).length < 2 ^ (prefixWord ++ tailWord_755587).sum := by decide
  have hdescent : baseEnd_755587 < baseStart_755587 := by decide
  rcases family_descends (prefixWord ++ tailWord_755587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755601 : List Nat := [1, 2, 2, 1, 1, 1, 5, 7]
def baseStart_755601 : Nat := 118140960795 + 755601 * 2 ^ 59
def prefixEnd_755601 : Nat := 4983230072969 + 3 ^ 40 * 755601 * 2
def baseEnd_755601 : Nat := 114958961783112130759277

theorem tailTrace_755601 : CollatzResearch.WordTrace tailWord_755601 prefixEnd_755601 114958961783112130759277 := by
  unfold tailWord_755601
  simp only [CollatzResearch.WordTrace]
  refine ⟨27559032535594098222002657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18372688357062732148001771 27559032535594098222002657)
  ·
    refine ⟨20669274401695573666501993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27559032535594098222002657 20669274401695573666501993)
    ·
      refine ⟨15501955801271680249876495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20669274401695573666501993 15501955801271680249876495)
      ·
        refine ⟨23252933701907520374814743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15501955801271680249876495 23252933701907520374814743)
        ·
          refine ⟨34879400552861280562222115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23252933701907520374814743 34879400552861280562222115)
          ·
            refine ⟨52319100829291920843333173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34879400552861280562222115 52319100829291920843333173)
            ·
              refine ⟨4904915702746117579062485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52319100829291920843333173 4904915702746117579062485)
              ·
                refine ⟨114958961783112130759277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4904915702746117579062485 114958961783112130759277)
                ·
                  rfl

theorem cell20_755601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_755601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755601 prefixEnd_755601 := by exact prefixLift 755601
  have htrace : WordTrace (prefixWord ++ tailWord_755601) baseStart_755601 baseEnd_755601 := by
    simpa [prefixWord, tailWord_755601, baseEnd_755601] using wordTrace_append hprefix tailTrace_755601
  have hstable : (prefixWord ++ tailWord_755601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755601).length < 2 ^ (prefixWord ++ tailWord_755601).sum := by decide
  have hdescent : baseEnd_755601 < baseStart_755601 := by decide
  rcases family_descends (prefixWord ++ tailWord_755601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755645 : List Nat := [1, 4, 1, 2, 3, 1, 4, 2, 2]
def baseStart_755645 : Nat := 118140960795 + 755645 * 2 ^ 59
def prefixEnd_755645 : Nat := 4983230072969 + 3 ^ 40 * 755645 * 2
def baseEnd_755645 : Nat := 344896968148267794810985

theorem tailTrace_755645 : CollatzResearch.WordTrace tailWord_755645 prefixEnd_755645 344896968148267794810985 := by
  unfold tailWord_755645
  simp only [CollatzResearch.WordTrace]
  refine ⟨27560637347434693736604389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18373758231623129157736259 27560637347434693736604389)
  ·
    refine ⟨5167619502644005075613323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27560637347434693736604389 5167619502644005075613323)
    ·
      refine ⟨7751429253966007613419985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5167619502644005075613323 7751429253966007613419985)
      ·
        refine ⟨5813571940474505710064989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7751429253966007613419985 5813571940474505710064989)
        ·
          refine ⟨2180089477677939641274371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5813571940474505710064989 2180089477677939641274371)
          ·
            refine ⟨3270134216516909461911557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180089477677939641274371 3270134216516909461911557)
            ·
              refine ⟨613150165596920524108417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3270134216516909461911557 613150165596920524108417)
              ·
                refine ⟨459862624197690393081313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 613150165596920524108417 459862624197690393081313)
                ·
                  refine ⟨344896968148267794810985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459862624197690393081313 344896968148267794810985)
                  ·
                    rfl

theorem cell20_755645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_755645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755645 prefixEnd_755645 := by exact prefixLift 755645
  have htrace : WordTrace (prefixWord ++ tailWord_755645) baseStart_755645 baseEnd_755645 := by
    simpa [prefixWord, tailWord_755645, baseEnd_755645] using wordTrace_append hprefix tailTrace_755645
  have hstable : (prefixWord ++ tailWord_755645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755645).length < 2 ^ (prefixWord ++ tailWord_755645).sum := by decide
  have hdescent : baseEnd_755645 < baseStart_755645 := by decide
  rcases family_descends (prefixWord ++ tailWord_755645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755656 : List Nat := [2, 1, 3, 1, 4, 1, 3, 5]
def baseStart_755656 : Nat := 118140960795 + 755656 * 2 ^ 59
def prefixEnd_755656 : Nat := 4983230072969 + 3 ^ 40 * 755656 * 2
def baseEnd_755656 : Nat := 114967329616000215148091

theorem tailTrace_755656 : CollatzResearch.WordTrace tailWord_755656 prefixEnd_755656 114967329616000215148091 := by
  unfold tailWord_755656
  simp only [CollatzResearch.WordTrace]
  refine ⟨13780519275197421307627411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18374025700263228410169881 13780519275197421307627411)
  ·
    refine ⟨20670778912796131961441117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13780519275197421307627411 20670778912796131961441117)
    ·
      refine ⟨7751542092298549485540419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20670778912796131961441117 7751542092298549485540419)
      ·
        refine ⟨11627313138447824228310629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7751542092298549485540419 11627313138447824228310629)
        ·
          refine ⟨2180121213458967042808243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11627313138447824228310629 2180121213458967042808243)
          ·
            refine ⟨3270181820188450564212365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180121213458967042808243 3270181820188450564212365)
            ·
              refine ⟨1226318182570668961579637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3270181820188450564212365 1226318182570668961579637)
              ·
                refine ⟨114967329616000215148091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1226318182570668961579637 114967329616000215148091)
                ·
                  rfl

theorem cell20_755656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_755656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755656 prefixEnd_755656 := by exact prefixLift 755656
  have htrace : WordTrace (prefixWord ++ tailWord_755656) baseStart_755656 baseEnd_755656 := by
    simpa [prefixWord, tailWord_755656, baseEnd_755656] using wordTrace_append hprefix tailTrace_755656
  have hstable : (prefixWord ++ tailWord_755656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755656).length < 2 ^ (prefixWord ++ tailWord_755656).sum := by decide
  have hdescent : baseEnd_755656 < baseStart_755656 := by decide
  rcases family_descends (prefixWord ++ tailWord_755656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755663 : List Nat := [1, 1, 2, 1, 1, 5, 1, 5, 3]
def baseStart_755663 : Nat := 118140960795 + 755663 * 2 ^ 59
def prefixEnd_755663 : Nat := 4983230072969 + 3 ^ 40 * 755663 * 2
def baseEnd_755663 : Nat := 344905183838739732210911

theorem tailTrace_755663 : CollatzResearch.WordTrace tailWord_755663 prefixEnd_755663 344905183838739732210911 := by
  unfold tailWord_755663
  simp only [CollatzResearch.WordTrace]
  refine ⟨27561293861369482810759643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18374195907579655207173095 27561293861369482810759643)
  ·
    refine ⟨41341940792054224216139465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27561293861369482810759643 41341940792054224216139465)
    ·
      refine ⟨31006455594040668162104599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41341940792054224216139465 31006455594040668162104599)
      ·
        refine ⟨46509683391061002243156899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31006455594040668162104599 46509683391061002243156899)
        ·
          refine ⟨69764525086591503364735349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46509683391061002243156899 69764525086591503364735349)
          ·
            refine ⟨6540424226867953440443939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69764525086591503364735349 6540424226867953440443939)
            ·
              refine ⟨9810636340301930160665909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6540424226867953440443939 9810636340301930160665909)
              ·
                refine ⟨919747156903305952562429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9810636340301930160665909 919747156903305952562429)
                ·
                  refine ⟨344905183838739732210911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919747156903305952562429 344905183838739732210911)
                  ·
                    rfl

theorem cell20_755663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 3].length) (baseStart_755663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755663 prefixEnd_755663 := by exact prefixLift 755663
  have htrace : WordTrace (prefixWord ++ tailWord_755663) baseStart_755663 baseEnd_755663 := by
    simpa [prefixWord, tailWord_755663, baseEnd_755663] using wordTrace_append hprefix tailTrace_755663
  have hstable : (prefixWord ++ tailWord_755663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755663).length < 2 ^ (prefixWord ++ tailWord_755663).sum := by decide
  have hdescent : baseEnd_755663 < baseStart_755663 := by decide
  rcases family_descends (prefixWord ++ tailWord_755663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755666 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 4]
def baseStart_755666 : Nat := 118140960795 + 755666 * 2 ^ 59
def prefixEnd_755666 : Nat := 4983230072969 + 3 ^ 40 * 755666 * 2
def baseEnd_755666 : Nat := 344906553120485055110899

theorem tailTrace_755666 : CollatzResearch.WordTrace tailWord_755666 prefixEnd_755666 344906553120485055110899 := by
  unfold tailWord_755666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6890350820089653580779713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18374268853572409548745901 6890350820089653580779713)
  ·
    refine ⟨5167763115067240185584785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6890350820089653580779713 5167763115067240185584785)
    ·
      refine ⟨3875822336300430139188589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5167763115067240185584785 3875822336300430139188589)
      ·
        refine ⟨1453433376112661302195721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3875822336300430139188589 1453433376112661302195721)
        ·
          refine ⟨1090075032084495976646791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1453433376112661302195721 1090075032084495976646791)
          ·
            refine ⟨1635112548126743964970187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090075032084495976646791 1635112548126743964970187)
            ·
              refine ⟨2452668822190115947455281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635112548126743964970187 2452668822190115947455281)
              ·
                refine ⟨1839501616642586960591461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2452668822190115947455281 1839501616642586960591461)
                ·
                  refine ⟨344906553120485055110899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1839501616642586960591461 344906553120485055110899)
                  ·
                    rfl

theorem cell20_755666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_755666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755666 prefixEnd_755666 := by exact prefixLift 755666
  have htrace : WordTrace (prefixWord ++ tailWord_755666) baseStart_755666 baseEnd_755666 := by
    simpa [prefixWord, tailWord_755666, baseEnd_755666] using wordTrace_append hprefix tailTrace_755666
  have hstable : (prefixWord ++ tailWord_755666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755666).length < 2 ^ (prefixWord ++ tailWord_755666).sum := by decide
  have hdescent : baseEnd_755666 < baseStart_755666 := by decide
  rcases family_descends (prefixWord ++ tailWord_755666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755673 : List Nat := [1, 2, 1, 2, 6, 1, 3, 4]
def baseStart_755673 : Nat := 118140960795 + 755673 * 2 ^ 59
def prefixEnd_755673 : Nat := 4983230072969 + 3 ^ 40 * 755673 * 2
def baseEnd_755673 : Nat := 114969916037074713959179

theorem tailTrace_755673 : CollatzResearch.WordTrace tailWord_755673 prefixEnd_755673 114969916037074713959179 := by
  unfold tailWord_755673
  simp only [CollatzResearch.WordTrace]
  refine ⟨27561658591333254518623673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18374439060888836345749115 27561658591333254518623673)
  ·
    refine ⟨20671243943499940888967755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27561658591333254518623673 20671243943499940888967755)
    ·
      refine ⟨31006865915249911333451633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20671243943499940888967755 31006865915249911333451633)
      ·
        refine ⟨23255149436437433500088725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31006865915249911333451633 23255149436437433500088725)
        ·
          refine ⟨1090085129833004695316659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23255149436437433500088725 1090085129833004695316659)
          ·
            refine ⟨1635127694749507042974989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090085129833004695316659 1635127694749507042974989)
            ·
              refine ⟨613172885531065141115621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1635127694749507042974989 613172885531065141115621)
              ·
                refine ⟨114969916037074713959179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 613172885531065141115621 114969916037074713959179)
                ·
                  rfl

theorem cell20_755673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 4].length) (baseStart_755673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755673 prefixEnd_755673 := by exact prefixLift 755673
  have htrace : WordTrace (prefixWord ++ tailWord_755673) baseStart_755673 baseEnd_755673 := by
    simpa [prefixWord, tailWord_755673, baseEnd_755673] using wordTrace_append hprefix tailTrace_755673
  have hstable : (prefixWord ++ tailWord_755673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755673).length < 2 ^ (prefixWord ++ tailWord_755673).sum := by decide
  have hdescent : baseEnd_755673 < baseStart_755673 := by decide
  rcases family_descends (prefixWord ++ tailWord_755673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755693 : List Nat := [1, 5, 1, 4, 2, 1, 1, 2, 3]
def baseStart_755693 : Nat := 118140960795 + 755693 * 2 ^ 59
def prefixEnd_755693 : Nat := 4983230072969 + 3 ^ 40 * 755693 * 2
def baseEnd_755693 : Nat := 344918876656192961210789

theorem tailTrace_755693 : CollatzResearch.WordTrace tailWord_755693 prefixEnd_755693 344918876656192961210789 := by
  unfold tailWord_755693
  simp only [CollatzResearch.WordTrace]
  refine ⟨27562388051260797934351733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18374925367507198622901155 27562388051260797934351733)
  ·
    refine ⟨2583973879805699806345475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27562388051260797934351733 2583973879805699806345475)
    ·
      refine ⟨3875960819708549709518213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2583973879805699806345475 3875960819708549709518213)
      ·
        refine ⟨726742653695353070534665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3875960819708549709518213 726742653695353070534665)
        ·
          refine ⟨545056990271514802900999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 726742653695353070534665 545056990271514802900999)
          ·
            refine ⟨817585485407272204351499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545056990271514802900999 817585485407272204351499)
            ·
              refine ⟨1226378228110908306527249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817585485407272204351499 1226378228110908306527249)
              ·
                refine ⟨919783671083181229895437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226378228110908306527249 919783671083181229895437)
                ·
                  refine ⟨344918876656192961210789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919783671083181229895437 344918876656192961210789)
                  ·
                    rfl

theorem cell20_755693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_755693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755693 prefixEnd_755693 := by exact prefixLift 755693
  have htrace : WordTrace (prefixWord ++ tailWord_755693) baseStart_755693 baseEnd_755693 := by
    simpa [prefixWord, tailWord_755693, baseEnd_755693] using wordTrace_append hprefix tailTrace_755693
  have hstable : (prefixWord ++ tailWord_755693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755693).length < 2 ^ (prefixWord ++ tailWord_755693).sum := by decide
  have hdescent : baseEnd_755693 < baseStart_755693 := by decide
  rcases family_descends (prefixWord ++ tailWord_755693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755694 : List Nat := [4, 1, 2, 1, 3, 2, 7]
def baseStart_755694 : Nat := 118140960795 + 755694 * 2 ^ 59
def prefixEnd_755694 : Nat := 4983230072969 + 3 ^ 40 * 755694 * 2
def baseEnd_755694 : Nat := 38324370342604600241939

theorem tailTrace_755694 : CollatzResearch.WordTrace tailWord_755694 prefixEnd_755694 38324370342604600241939 := by
  unfold tailWord_755694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3445303065532146888142267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18374949682838116736758757 3445303065532146888142267)
  ·
    refine ⟨5167954598298220332213401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3445303065532146888142267 5167954598298220332213401)
    ·
      refine ⟨3875965948723665249160051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5167954598298220332213401 3875965948723665249160051)
      ·
        refine ⟨5813948923085497873740077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3875965948723665249160051 5813948923085497873740077)
        ·
          refine ⟨2180230846157061702652529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5813948923085497873740077 2180230846157061702652529)
          ·
            refine ⟨1635173134617796276989397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2180230846157061702652529 1635173134617796276989397)
            ·
              refine ⟨38324370342604600241939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1635173134617796276989397 38324370342604600241939)
              ·
                rfl

theorem cell20_755694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 7].length) (baseStart_755694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755694 prefixEnd_755694 := by exact prefixLift 755694
  have htrace : WordTrace (prefixWord ++ tailWord_755694) baseStart_755694 baseEnd_755694 := by
    simpa [prefixWord, tailWord_755694, baseEnd_755694] using wordTrace_append hprefix tailTrace_755694
  have hstable : (prefixWord ++ tailWord_755694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755694).length < 2 ^ (prefixWord ++ tailWord_755694).sum := by decide
  have hdescent : baseEnd_755694 < baseStart_755694 := by decide
  rcases family_descends (prefixWord ++ tailWord_755694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755697 : List Nat := [1, 2, 2, 2, 5, 2, 1, 2, 3]
def baseStart_755697 : Nat := 118140960795 + 755697 * 2 ^ 59
def prefixEnd_755697 : Nat := 4983230072969 + 3 ^ 40 * 755697 * 2
def baseEnd_755697 : Nat := 344920702365186725077439

theorem tailTrace_755697 : CollatzResearch.WordTrace tailWord_755697 prefixEnd_755697 344920702365186725077439 := by
  unfold tailWord_755697
  simp only [CollatzResearch.WordTrace]
  refine ⟨27562533943246306617497345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18375022628830871078331563 27562533943246306617497345)
  ·
    refine ⟨20671900457434729963123009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27562533943246306617497345 20671900457434729963123009)
    ·
      refine ⟨15503925343076047472342257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20671900457434729963123009 15503925343076047472342257)
      ·
        refine ⟨11627944007307035604256693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15503925343076047472342257 11627944007307035604256693)
        ·
          refine ⟨1090119750685034587899065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11627944007307035604256693 1090119750685034587899065)
          ·
            refine ⟨817589813013775940924299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1090119750685034587899065 817589813013775940924299)
            ·
              refine ⟨1226384719520663911386449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817589813013775940924299 1226384719520663911386449)
              ·
                refine ⟨919788539640497933539837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226384719520663911386449 919788539640497933539837)
                ·
                  refine ⟨344920702365186725077439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919788539640497933539837 344920702365186725077439)
                  ·
                    rfl

theorem cell20_755697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_755697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755697 prefixEnd_755697 := by exact prefixLift 755697
  have htrace : WordTrace (prefixWord ++ tailWord_755697) baseStart_755697 baseEnd_755697 := by
    simpa [prefixWord, tailWord_755697, baseEnd_755697] using wordTrace_append hprefix tailTrace_755697
  have hstable : (prefixWord ++ tailWord_755697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755697).length < 2 ^ (prefixWord ++ tailWord_755697).sum := by decide
  have hdescent : baseEnd_755697 < baseStart_755697 := by decide
  rcases family_descends (prefixWord ++ tailWord_755697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755763 : List Nat := [1, 1, 1, 2, 4, 1, 2, 6, 2]
def baseStart_755763 : Nat := 118140960795 + 755763 * 2 ^ 59
def prefixEnd_755763 : Nat := 4983230072969 + 3 ^ 40 * 755763 * 2
def baseEnd_755763 : Nat := 344950826563583828877169

theorem tailTrace_755763 : CollatzResearch.WordTrace tailWord_755763 prefixEnd_755763 344950826563583828877169 := by
  unfold tailWord_755763
  simp only [CollatzResearch.WordTrace]
  refine ⟨27564941161007199889399943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18376627440671466592933295 27564941161007199889399943)
  ·
    refine ⟨41347411741510799834099915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27564941161007199889399943 41347411741510799834099915)
    ·
      refine ⟨62021117612266199751149873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41347411741510799834099915 62021117612266199751149873)
      ·
        refine ⟨46515838209199649813362405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62021117612266199751149873 46515838209199649813362405)
        ·
          refine ⟨8721719664224934340005451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46515838209199649813362405 8721719664224934340005451)
          ·
            refine ⟨13082579496337401510008177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8721719664224934340005451 13082579496337401510008177)
            ·
              refine ⟨9811934622253051132506133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13082579496337401510008177 9811934622253051132506133)
              ·
                refine ⟨459934435418111771836225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9811934622253051132506133 459934435418111771836225)
                ·
                  refine ⟨344950826563583828877169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459934435418111771836225 344950826563583828877169)
                  ·
                    rfl

theorem cell20_755763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 2].length) (baseStart_755763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755763 prefixEnd_755763 := by exact prefixLift 755763
  have htrace : WordTrace (prefixWord ++ tailWord_755763) baseStart_755763 baseEnd_755763 := by
    simpa [prefixWord, tailWord_755763, baseEnd_755763] using wordTrace_append hprefix tailTrace_755763
  have hstable : (prefixWord ++ tailWord_755763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755763).length < 2 ^ (prefixWord ++ tailWord_755763).sum := by decide
  have hdescent : baseEnd_755763 < baseStart_755763 := by decide
  rcases family_descends (prefixWord ++ tailWord_755763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755801 : List Nat := [1, 2, 1, 2, 2, 1, 4, 5, 2]
def baseStart_755801 : Nat := 118140960795 + 755801 * 2 ^ 59
def prefixEnd_755801 : Nat := 4983230072969 + 3 ^ 40 * 755801 * 2
def baseEnd_755801 : Nat := 344968170799024585610347

theorem tailTrace_755801 : CollatzResearch.WordTrace tailWord_755801 prefixEnd_755801 344968170799024585610347 := by
  unfold tailWord_755801
  simp only [CollatzResearch.WordTrace]
  refine ⟨27566327134869532379283257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18377551423246354919522171 27566327134869532379283257)
  ·
    refine ⟨20674745351152149284462443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27566327134869532379283257 20674745351152149284462443)
    ·
      refine ⟨31012118026728223926693665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20674745351152149284462443 31012118026728223926693665)
      ·
        refine ⟨23259088520046167945020249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31012118026728223926693665 23259088520046167945020249)
        ·
          refine ⟨17444316390034625958765187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23259088520046167945020249 17444316390034625958765187)
          ·
            refine ⟨26166474585051938938147781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17444316390034625958765187 26166474585051938938147781)
            ·
              refine ⟨4906213984697238550902709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26166474585051938938147781 4906213984697238550902709)
              ·
                refine ⟨459957561065366114147129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4906213984697238550902709 459957561065366114147129)
                ·
                  refine ⟨344968170799024585610347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459957561065366114147129 344968170799024585610347)
                  ·
                    rfl

theorem cell20_755801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 2].length) (baseStart_755801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755801 prefixEnd_755801 := by exact prefixLift 755801
  have htrace : WordTrace (prefixWord ++ tailWord_755801) baseStart_755801 baseEnd_755801 := by
    simpa [prefixWord, tailWord_755801, baseEnd_755801] using wordTrace_append hprefix tailTrace_755801
  have hstable : (prefixWord ++ tailWord_755801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755801).length < 2 ^ (prefixWord ++ tailWord_755801).sum := by decide
  have hdescent : baseEnd_755801 < baseStart_755801 := by decide
  rcases family_descends (prefixWord ++ tailWord_755801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755866 : List Nat := [3, 1, 1, 5, 3, 1, 1, 2, 3]
def baseStart_755866 : Nat := 118140960795 + 755866 * 2 ^ 59
def prefixEnd_755866 : Nat := 4983230072969 + 3 ^ 40 * 755866 * 2
def baseEnd_755866 : Nat := 344997838570173248443415

theorem tailTrace_755866 : CollatzResearch.WordTrace tailWord_755866 prefixEnd_755866 344997838570173248443415 := by
  unfold tailWord_755866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892174469908512120099863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18379131919756032320266301 6892174469908512120099863)
  ·
    refine ⟨10338261704862768180149795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6892174469908512120099863 10338261704862768180149795)
    ·
      refine ⟨15507392557294152270224693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10338261704862768180149795 15507392557294152270224693)
      ·
        refine ⟨1453818052246326775333565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15507392557294152270224693 1453818052246326775333565)
        ·
          refine ⟨545181769592372540750087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1453818052246326775333565 545181769592372540750087)
          ·
            refine ⟨817772654388558811125131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545181769592372540750087 817772654388558811125131)
            ·
              refine ⟨1226658981582838216687697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817772654388558811125131 1226658981582838216687697)
              ·
                refine ⟨919994236187128662515773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226658981582838216687697 919994236187128662515773)
                ·
                  refine ⟨344997838570173248443415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919994236187128662515773 344997838570173248443415)
                  ·
                    rfl

theorem cell20_755866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_755866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755866 prefixEnd_755866 := by exact prefixLift 755866
  have htrace : WordTrace (prefixWord ++ tailWord_755866) baseStart_755866 baseEnd_755866 := by
    simpa [prefixWord, tailWord_755866, baseEnd_755866] using wordTrace_append hprefix tailTrace_755866
  have hstable : (prefixWord ++ tailWord_755866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755866).length < 2 ^ (prefixWord ++ tailWord_755866).sum := by decide
  have hdescent : baseEnd_755866 < baseStart_755866 := by decide
  rcases family_descends (prefixWord ++ tailWord_755866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755877 : List Nat := [1, 3, 1, 2, 1, 3, 1, 6, 2]
def baseStart_755877 : Nat := 118140960795 + 755877 * 2 ^ 59
def prefixEnd_755877 : Nat := 4983230072969 + 3 ^ 40 * 755877 * 2
def baseEnd_755877 : Nat := 345002859269906099076703

theorem tailTrace_755877 : CollatzResearch.WordTrace tailWord_755877 prefixEnd_755877 345002859269906099076703 := by
  unfold tailWord_755877
  simp only [CollatzResearch.WordTrace]
  refine ⟨27569099082594197359049885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18379399388396131572699923 27569099082594197359049885)
  ·
    refine ⟨10338412155972824009643707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27569099082594197359049885 10338412155972824009643707)
    ·
      refine ⟨15507618233959236014465561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10338412155972824009643707 15507618233959236014465561)
      ·
        refine ⟨11630713675469427010849171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15507618233959236014465561 11630713675469427010849171)
        ·
          refine ⟨17446070513204140516273757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11630713675469427010849171 17446070513204140516273757)
          ·
            refine ⟨6542276442451552693602659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17446070513204140516273757 6542276442451552693602659)
            ·
              refine ⟨9813414663677329040403989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6542276442451552693602659 9813414663677329040403989)
              ·
                refine ⟨460003812359874798768937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9813414663677329040403989 460003812359874798768937)
                ·
                  refine ⟨345002859269906099076703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460003812359874798768937 345002859269906099076703)
                  ·
                    rfl

theorem cell20_755877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_755877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755877 prefixEnd_755877 := by exact prefixLift 755877
  have htrace : WordTrace (prefixWord ++ tailWord_755877) baseStart_755877 baseEnd_755877 := by
    simpa [prefixWord, tailWord_755877, baseEnd_755877] using wordTrace_append hprefix tailTrace_755877
  have hstable : (prefixWord ++ tailWord_755877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755877).length < 2 ^ (prefixWord ++ tailWord_755877).sum := by decide
  have hdescent : baseEnd_755877 < baseStart_755877 := by decide
  rcases family_descends (prefixWord ++ tailWord_755877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755898 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_755898 : Nat := 118140960795 + 755898 * 2 ^ 59
def prefixEnd_755898 : Nat := 4983230072969 + 3 ^ 40 * 755898 * 2
def baseEnd_755898 : Nat := 345012444242123359376617

theorem tailTrace_755898 : CollatzResearch.WordTrace tailWord_755898 prefixEnd_755898 345012444242123359376617 := by
  unfold tailWord_755898
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892466253879529486391087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18379910010345411963709565 6892466253879529486391087)
  ·
    refine ⟨10338699380819294229586631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6892466253879529486391087 10338699380819294229586631)
    ·
      refine ⟨15508049071228941344379947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10338699380819294229586631 15508049071228941344379947)
      ·
        refine ⟨23262073606843412016569921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15508049071228941344379947 23262073606843412016569921)
        ·
          refine ⟨17446555205132559012427441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23262073606843412016569921 17446555205132559012427441)
          ·
            refine ⟨13084916403849419259320581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17446555205132559012427441 13084916403849419259320581)
            ·
              refine ⟨2453421825721766111122609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13084916403849419259320581 2453421825721766111122609)
              ·
                refine ⟨1840066369291324583341957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2453421825721766111122609 1840066369291324583341957)
                ·
                  refine ⟨345012444242123359376617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1840066369291324583341957 345012444242123359376617)
                  ·
                    rfl

theorem cell20_755898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_755898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755898 prefixEnd_755898 := by exact prefixLift 755898
  have htrace : WordTrace (prefixWord ++ tailWord_755898) baseStart_755898 baseEnd_755898 := by
    simpa [prefixWord, tailWord_755898, baseEnd_755898] using wordTrace_append hprefix tailTrace_755898
  have hstable : (prefixWord ++ tailWord_755898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755898).length < 2 ^ (prefixWord ++ tailWord_755898).sum := by decide
  have hdescent : baseEnd_755898 < baseStart_755898 := by decide
  rcases family_descends (prefixWord ++ tailWord_755898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755922 : List Nat := [3, 2, 2, 2, 1, 4, 6]
def baseStart_755922 : Nat := 118140960795 + 755922 * 2 ^ 59
def prefixEnd_755922 : Nat := 4983230072969 + 3 ^ 40 * 755922 * 2
def baseEnd_755922 : Nat := 38335933166231771397391

theorem tailTrace_755922 : CollatzResearch.WordTrace tailWord_755922 prefixEnd_755922 38335933166231771397391 := by
  unfold tailWord_755922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892685091857792511109505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18380493578287446696292013 6892685091857792511109505)
  ·
    refine ⟨5169513818893344383332129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6892685091857792511109505 5169513818893344383332129)
    ·
      refine ⟨3877135364170008287499097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5169513818893344383332129 3877135364170008287499097)
      ·
        refine ⟨2907851523127506215624323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3877135364170008287499097 2907851523127506215624323)
        ·
          refine ⟨4361777284691259323436485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2907851523127506215624323 4361777284691259323436485)
          ·
            refine ⟨817833240879611123144341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4361777284691259323436485 817833240879611123144341)
            ·
              refine ⟨38335933166231771397391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 817833240879611123144341 38335933166231771397391)
              ·
                rfl

theorem cell20_755922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 6].length) (baseStart_755922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755922 prefixEnd_755922 := by exact prefixLift 755922
  have htrace : WordTrace (prefixWord ++ tailWord_755922) baseStart_755922 baseEnd_755922 := by
    simpa [prefixWord, tailWord_755922, baseEnd_755922] using wordTrace_append hprefix tailTrace_755922
  have hstable : (prefixWord ++ tailWord_755922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755922).length < 2 ^ (prefixWord ++ tailWord_755922).sum := by decide
  have hdescent : baseEnd_755922 < baseStart_755922 := by decide
  rcases family_descends (prefixWord ++ tailWord_755922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755938 : List Nat := [3, 3, 4, 1, 1, 2, 2, 1, 3]
def baseStart_755938 : Nat := 118140960795 + 755938 * 2 ^ 59
def prefixEnd_755938 : Nat := 4983230072969 + 3 ^ 40 * 755938 * 2
def baseEnd_755938 : Nat := 345030701332060998043121

theorem tailTrace_755938 : CollatzResearch.WordTrace tailWord_755938 prefixEnd_755938 345030701332060998043121 := by
  unfold tailWord_755938
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892830983843301194255117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18380882623582136518013645 6892830983843301194255117)
  ·
    refine ⟨2584811618941237947845669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6892830983843301194255117 2584811618941237947845669)
    ·
      refine ⟨484652178551482115221063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2584811618941237947845669 484652178551482115221063)
      ·
        refine ⟨726978267827223172831595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484652178551482115221063 726978267827223172831595)
        ·
          refine ⟨1090467401740834759247393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726978267827223172831595 1090467401740834759247393)
          ·
            refine ⟨817850551305626069435545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1090467401740834759247393 817850551305626069435545)
            ·
              refine ⟨613387913479219552076659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817850551305626069435545 613387913479219552076659)
              ·
                refine ⟨920081870218829328114989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613387913479219552076659 920081870218829328114989)
                ·
                  refine ⟨345030701332060998043121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920081870218829328114989 345030701332060998043121)
                  ·
                    rfl

theorem cell20_755938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_755938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755938 prefixEnd_755938 := by exact prefixLift 755938
  have htrace : WordTrace (prefixWord ++ tailWord_755938) baseStart_755938 baseEnd_755938 := by
    simpa [prefixWord, tailWord_755938, baseEnd_755938] using wordTrace_append hprefix tailTrace_755938
  have hstable : (prefixWord ++ tailWord_755938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755938).length < 2 ^ (prefixWord ++ tailWord_755938).sum := by decide
  have hdescent : baseEnd_755938 < baseStart_755938 := by decide
  rcases family_descends (prefixWord ++ tailWord_755938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755939 : List Nat := [1, 1, 1, 8, 1, 1, 2, 5]
def baseStart_755939 : Nat := 118140960795 + 755939 * 2 ^ 59
def prefixEnd_755939 : Nat := 4983230072969 + 3 ^ 40 * 755939 * 2
def baseEnd_755939 : Nat := 115010385919769813003261

theorem tailTrace_755939 : CollatzResearch.WordTrace tailWord_755939 prefixEnd_755939 115010385919769813003261 := by
  unfold tailWord_755939
  simp only [CollatzResearch.WordTrace]
  refine ⟨27571360408369581947806871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18380906938913054631871247 27571360408369581947806871)
  ·
    refine ⟨41357040612554372921710307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27571360408369581947806871 41357040612554372921710307)
    ·
      refine ⟨62035560918831559382565461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41357040612554372921710307 62035560918831559382565461)
      ·
        refine ⟨726979229517557336514439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 62035560918831559382565461 726979229517557336514439)
        ·
          refine ⟨1090468844276336004771659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726979229517557336514439 1090468844276336004771659)
          ·
            refine ⟨1635703266414504007157489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090468844276336004771659 1635703266414504007157489)
            ·
              refine ⟨1226777449810878005368117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1635703266414504007157489 1226777449810878005368117)
              ·
                refine ⟨115010385919769813003261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1226777449810878005368117 115010385919769813003261)
                ·
                  rfl

theorem cell20_755939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 5].length) (baseStart_755939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_755939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_755939 prefixEnd_755939 := by exact prefixLift 755939
  have htrace : WordTrace (prefixWord ++ tailWord_755939) baseStart_755939 baseEnd_755939 := by
    simpa [prefixWord, tailWord_755939, baseEnd_755939] using wordTrace_append hprefix tailTrace_755939
  have hstable : (prefixWord ++ tailWord_755939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755939).length < 2 ^ (prefixWord ++ tailWord_755939).sum := by decide
  have hdescent : baseEnd_755939 < baseStart_755939 := by decide
  rcases family_descends (prefixWord ++ tailWord_755939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756050 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_756050 : Nat := 118140960795 + 756050 * 2 ^ 59
def prefixEnd_756050 : Nat := 4983230072969 + 3 ^ 40 * 756050 * 2
def baseEnd_756050 : Nat := 345081821183886386309329

theorem tailTrace_756050 : CollatzResearch.WordTrace tailWord_756050 prefixEnd_756050 345081821183886386309329 := by
  unfold tailWord_756050
  simp only [CollatzResearch.WordTrace]
  refine ⟨6893852227741861976274401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18383605940644965270065069 6893852227741861976274401)
  ·
    refine ⟨5170389170806396482205801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6893852227741861976274401 5170389170806396482205801)
    ·
      refine ⟨3877791878104797361654351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5170389170806396482205801 3877791878104797361654351)
      ·
        refine ⟨5816687817157196042481527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3877791878104797361654351 5816687817157196042481527)
        ·
          refine ⟨8725031725735794063722291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5816687817157196042481527 8725031725735794063722291)
          ·
            refine ⟨13087547588603691095583437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8725031725735794063722291 13087547588603691095583437)
            ·
              refine ⟨4907830345726384160843789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13087547588603691095583437 4907830345726384160843789)
              ·
                refine ⟨1840436379647394060316421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4907830345726384160843789 1840436379647394060316421)
                ·
                  refine ⟨345081821183886386309329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1840436379647394060316421 345081821183886386309329)
                  ·
                    rfl

theorem cell20_756050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_756050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756050 prefixEnd_756050 := by exact prefixLift 756050
  have htrace : WordTrace (prefixWord ++ tailWord_756050) baseStart_756050 baseEnd_756050 := by
    simpa [prefixWord, tailWord_756050, baseEnd_756050] using wordTrace_append hprefix tailTrace_756050
  have hstable : (prefixWord ++ tailWord_756050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756050).length < 2 ^ (prefixWord ++ tailWord_756050).sum := by decide
  have hdescent : baseEnd_756050 < baseStart_756050 := by decide
  rcases family_descends (prefixWord ++ tailWord_756050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756074 : List Nat := [3, 1, 3, 3, 1, 2, 1, 6]
def baseStart_756074 : Nat := 118140960795 + 756074 * 2 ^ 59
def prefixEnd_756074 : Nat := 4983230072969 + 3 ^ 40 * 756074 * 2
def baseEnd_756074 : Nat := 115030925145949656503077

theorem tailTrace_756074 : CollatzResearch.WordTrace tailWord_756074 prefixEnd_756074 115030925145949656503077 := by
  unfold tailWord_756074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6894071065720125000992819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18384189508587000002647517 6894071065720125000992819)
  ·
    refine ⟨10341106598580187501489229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6894071065720125000992819 10341106598580187501489229)
    ·
      refine ⟨3877914974467570313058461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10341106598580187501489229 3877914974467570313058461)
      ·
        refine ⟨1454218115425338867396923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3877914974467570313058461 1454218115425338867396923)
        ·
          refine ⟨2181327173138008301095385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1454218115425338867396923 2181327173138008301095385)
          ·
            refine ⟨1635995379853506225821539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2181327173138008301095385 1635995379853506225821539)
            ·
              refine ⟨2453993069780259338732309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635995379853506225821539 2453993069780259338732309)
              ·
                refine ⟨115030925145949656503077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2453993069780259338732309 115030925145949656503077)
                ·
                  rfl

theorem cell20_756074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_756074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756074 prefixEnd_756074 := by exact prefixLift 756074
  have htrace : WordTrace (prefixWord ++ tailWord_756074) baseStart_756074 baseEnd_756074 := by
    simpa [prefixWord, tailWord_756074, baseEnd_756074] using wordTrace_append hprefix tailTrace_756074
  have hstable : (prefixWord ++ tailWord_756074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756074).length < 2 ^ (prefixWord ++ tailWord_756074).sum := by decide
  have hdescent : baseEnd_756074 < baseStart_756074 := by decide
  rcases family_descends (prefixWord ++ tailWord_756074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756105 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 4]
def baseStart_756105 : Nat := 118140960795 + 756105 * 2 ^ 59
def prefixEnd_756105 : Nat := 4983230072969 + 3 ^ 40 * 756105 * 2
def baseEnd_756105 : Nat := 345106924682550639475771

theorem tailTrace_756105 : CollatzResearch.WordTrace tailWord_756105 prefixEnd_756105 345106924682550639475771 := by
  unfold tailWord_756105
  simp only [CollatzResearch.WordTrace]
  refine ⟨27577414925768192298349769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18384943283845461532233179 27577414925768192298349769)
  ·
    refine ⟨20683061194326144223762327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27577414925768192298349769 20683061194326144223762327)
    ·
      refine ⟨31024591791489216335643491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20683061194326144223762327 31024591791489216335643491)
      ·
        refine ⟨46536887687233824503465237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31024591791489216335643491 46536887687233824503465237)
        ·
          refine ⟨2181416610339085523599933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46536887687233824503465237 2181416610339085523599933)
          ·
            refine ⟨818031228877157071349975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2181416610339085523599933 818031228877157071349975)
            ·
              refine ⟨1227046843315735607024963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818031228877157071349975 1227046843315735607024963)
              ·
                refine ⟨1840570264973603410537445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227046843315735607024963 1840570264973603410537445)
                ·
                  refine ⟨345106924682550639475771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1840570264973603410537445 345106924682550639475771)
                  ·
                    rfl

theorem cell20_756105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_756105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756105 prefixEnd_756105 := by exact prefixLift 756105
  have htrace : WordTrace (prefixWord ++ tailWord_756105) baseStart_756105 baseEnd_756105 := by
    simpa [prefixWord, tailWord_756105, baseEnd_756105] using wordTrace_append hprefix tailTrace_756105
  have hstable : (prefixWord ++ tailWord_756105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756105).length < 2 ^ (prefixWord ++ tailWord_756105).sum := by decide
  have hdescent : baseEnd_756105 < baseStart_756105 := by decide
  rcases family_descends (prefixWord ++ tailWord_756105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756157 : List Nat := [1, 4, 1, 2, 2, 2, 1, 4, 3]
def baseStart_756157 : Nat := 118140960795 + 756157 * 2 ^ 59
def prefixEnd_756157 : Nat := 4983230072969 + 3 ^ 40 * 756157 * 2
def baseEnd_756157 : Nat := 345130658899469569742225

theorem tailTrace_756157 : CollatzResearch.WordTrace tailWord_756157 prefixEnd_756157 345130658899469569742225 := by
  unfold tailWord_756157
  simp only [CollatzResearch.WordTrace]
  refine ⟨27579311521579805179242725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18386207681053203452828483 27579311521579805179242725)
  ·
    refine ⟨5171120910296213471108011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27579311521579805179242725 5171120910296213471108011)
    ·
      refine ⟨7756681365444320206662017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5171120910296213471108011 7756681365444320206662017)
      ·
        refine ⟨5817511024083240154996513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7756681365444320206662017 5817511024083240154996513)
        ·
          refine ⟨4363133268062430116247385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5817511024083240154996513 4363133268062430116247385)
          ·
            refine ⟨3272349951046822587185539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4363133268062430116247385 3272349951046822587185539)
            ·
              refine ⟨4908524926570233880778309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3272349951046822587185539 4908524926570233880778309)
              ·
                refine ⟨920348423731918852645933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4908524926570233880778309 920348423731918852645933)
                ·
                  refine ⟨345130658899469569742225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920348423731918852645933 345130658899469569742225)
                  ·
                    rfl

theorem cell20_756157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_756157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756157 prefixEnd_756157 := by exact prefixLift 756157
  have htrace : WordTrace (prefixWord ++ tailWord_756157) baseStart_756157 baseEnd_756157 := by
    simpa [prefixWord, tailWord_756157, baseEnd_756157] using wordTrace_append hprefix tailTrace_756157
  have hstable : (prefixWord ++ tailWord_756157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756157).length < 2 ^ (prefixWord ++ tailWord_756157).sum := by decide
  have hdescent : baseEnd_756157 < baseStart_756157 := by decide
  rcases family_descends (prefixWord ++ tailWord_756157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756194 : List Nat := [3, 3, 3, 2, 1, 1, 2, 3, 2]
def baseStart_756194 : Nat := 118140960795 + 756194 * 2 ^ 59
def prefixEnd_756194 : Nat := 4983230072969 + 3 ^ 40 * 756194 * 2
def baseEnd_756194 : Nat := 345147546707661885508741

theorem tailTrace_756194 : CollatzResearch.WordTrace tailWord_756194 prefixEnd_756194 345147546707661885508741 := by
  unfold tailWord_756194
  simp only [CollatzResearch.WordTrace]
  refine ⟨6895165255611440124584909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18387107348297173665559757 6895165255611440124584909)
  ·
    refine ⟨2585686970854290046719341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6895165255611440124584909 2585686970854290046719341)
    ·
      refine ⟨969632614070358767519753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2585686970854290046719341 969632614070358767519753)
      ·
        refine ⟨727224460552769075639815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 969632614070358767519753 727224460552769075639815)
        ·
          refine ⟨1090836690829153613459723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727224460552769075639815 1090836690829153613459723)
          ·
            refine ⟨1636255036243730420189585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090836690829153613459723 1636255036243730420189585)
            ·
              refine ⟨1227191277182797815142189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1636255036243730420189585 1227191277182797815142189)
              ·
                refine ⟨460196728943549180678321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1227191277182797815142189 460196728943549180678321)
                ·
                  refine ⟨345147546707661885508741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460196728943549180678321 345147546707661885508741)
                  ·
                    rfl

theorem cell20_756194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_756194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756194 prefixEnd_756194 := by exact prefixLift 756194
  have htrace : WordTrace (prefixWord ++ tailWord_756194) baseStart_756194 baseEnd_756194 := by
    simpa [prefixWord, tailWord_756194, baseEnd_756194] using wordTrace_append hprefix tailTrace_756194
  have hstable : (prefixWord ++ tailWord_756194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756194).length < 2 ^ (prefixWord ++ tailWord_756194).sum := by decide
  have hdescent : baseEnd_756194 < baseStart_756194 := by decide
  rcases family_descends (prefixWord ++ tailWord_756194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756216 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 5]
def baseStart_756216 : Nat := 118140960795 + 756216 * 2 ^ 59
def prefixEnd_756216 : Nat := 4983230072969 + 3 ^ 40 * 756216 * 2
def baseEnd_756216 : Nat := 345157588107127586775317

theorem tailTrace_756216 : CollatzResearch.WordTrace tailWord_756216 prefixEnd_756216 345157588107127586775317 := by
  unfold tailWord_756216
  simp only [CollatzResearch.WordTrace]
  refine ⟨13790731714183029127820251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18387642285577372170427001 13790731714183029127820251)
  ·
    refine ⟨20686097571274543691730377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13790731714183029127820251 20686097571274543691730377)
    ·
      refine ⟨15514573178455907768797783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20686097571274543691730377 15514573178455907768797783)
      ·
        refine ⟨23271859767683861653196675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15514573178455907768797783 23271859767683861653196675)
        ·
          refine ⟨34907789651525792479795013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23271859767683861653196675 34907789651525792479795013)
          ·
            refine ⟨6545210559661086089961565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34907789651525792479795013 6545210559661086089961565)
            ·
              refine ⟨2454453959872907283735587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6545210559661086089961565 2454453959872907283735587)
              ·
                refine ⟨3681680939809360925603381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2454453959872907283735587 3681680939809360925603381)
                ·
                  refine ⟨345157588107127586775317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3681680939809360925603381 345157588107127586775317)
                  ·
                    rfl

theorem cell20_756216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_756216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756216 prefixEnd_756216 := by exact prefixLift 756216
  have htrace : WordTrace (prefixWord ++ tailWord_756216) baseStart_756216 baseEnd_756216 := by
    simpa [prefixWord, tailWord_756216, baseEnd_756216] using wordTrace_append hprefix tailTrace_756216
  have hstable : (prefixWord ++ tailWord_756216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756216).length < 2 ^ (prefixWord ++ tailWord_756216).sum := by decide
  have hdescent : baseEnd_756216 < baseStart_756216 := by decide
  rcases family_descends (prefixWord ++ tailWord_756216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756261 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 6]
def baseStart_756261 : Nat := 118140960795 + 756261 * 2 ^ 59
def prefixEnd_756261 : Nat := 4983230072969 + 3 ^ 40 * 756261 * 2
def baseEnd_756261 : Nat := 345178127333307430275133

theorem tailTrace_756261 : CollatzResearch.WordTrace tailWord_756261 prefixEnd_756261 345178127333307430275133 := by
  unfold tailWord_756261
  simp only [CollatzResearch.WordTrace]
  refine ⟨27583104713203030941028637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18388736475468687294019091 27583104713203030941028637)
  ·
    refine ⟨10343664267451136602885739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27583104713203030941028637 10343664267451136602885739)
    ·
      refine ⟨15515496401176704904328609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10343664267451136602885739 15515496401176704904328609)
      ·
        refine ⟨11636622300882528678246457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15515496401176704904328609 11636622300882528678246457)
        ·
          refine ⟨8727466725661896508684843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11636622300882528678246457 8727466725661896508684843)
          ·
            refine ⟨13091200088492844763027265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8727466725661896508684843 13091200088492844763027265)
            ·
              refine ⟨9818400066369633572270449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13091200088492844763027265 9818400066369633572270449)
              ·
                refine ⟨7363800049777225179202837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9818400066369633572270449 7363800049777225179202837)
                ·
                  refine ⟨345178127333307430275133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7363800049777225179202837 345178127333307430275133)
                  ·
                    rfl

theorem cell20_756261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_756261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756261 prefixEnd_756261 := by exact prefixLift 756261
  have htrace : WordTrace (prefixWord ++ tailWord_756261) baseStart_756261 baseEnd_756261 := by
    simpa [prefixWord, tailWord_756261, baseEnd_756261] using wordTrace_append hprefix tailTrace_756261
  have hstable : (prefixWord ++ tailWord_756261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756261).length < 2 ^ (prefixWord ++ tailWord_756261).sum := by decide
  have hdescent : baseEnd_756261 < baseStart_756261 := by decide
  rcases family_descends (prefixWord ++ tailWord_756261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756264 : List Nat := [2, 1, 5, 2, 1, 3, 6]
def baseStart_756264 : Nat := 118140960795 + 756264 * 2 ^ 59
def prefixEnd_756264 : Nat := 4983230072969 + 3 ^ 40 * 756264 * 2
def baseEnd_756264 : Nat := 38353277401672528130569

theorem tailTrace_756264 : CollatzResearch.WordTrace tailWord_756264 prefixEnd_756264 38353277401672528130569 := by
  unfold tailWord_756264
  simp only [CollatzResearch.WordTrace]
  refine ⟨13791607066096081226693923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18388809421461441635591897 13791607066096081226693923)
  ·
    refine ⟨20687410599144121840040885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13791607066096081226693923 20687410599144121840040885)
    ·
      refine ⟨1939444743669761422503833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20687410599144121840040885 1939444743669761422503833)
      ·
        refine ⟨1454583557752321066877875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1939444743669761422503833 1454583557752321066877875)
        ·
          refine ⟨2181875336628481600316813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1454583557752321066877875 2181875336628481600316813)
          ·
            refine ⟨818203251235680600118805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2181875336628481600316813 818203251235680600118805)
            ·
              refine ⟨38353277401672528130569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 818203251235680600118805 38353277401672528130569)
              ·
                rfl

theorem cell20_756264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 6].length) (baseStart_756264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756264 prefixEnd_756264 := by exact prefixLift 756264
  have htrace : WordTrace (prefixWord ++ tailWord_756264) baseStart_756264 baseEnd_756264 := by
    simpa [prefixWord, tailWord_756264, baseEnd_756264] using wordTrace_append hprefix tailTrace_756264
  have hstable : (prefixWord ++ tailWord_756264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756264).length < 2 ^ (prefixWord ++ tailWord_756264).sum := by decide
  have hdescent : baseEnd_756264 < baseStart_756264 := by decide
  rcases family_descends (prefixWord ++ tailWord_756264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756285 : List Nat := [1, 4, 1, 3, 2, 1, 1, 7]
def baseStart_756285 : Nat := 118140960795 + 756285 * 2 ^ 59
def prefixEnd_756285 : Nat := 4983230072969 + 3 ^ 40 * 756285 * 2
def baseEnd_756285 : Nat := 115063027195756671158345

theorem tailTrace_756285 : CollatzResearch.WordTrace tailWord_756285 prefixEnd_756285 115063027195756671158345 := by
  unfold tailWord_756285
  simp only [CollatzResearch.WordTrace]
  refine ⟨27583980065116083039902309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18389320043410722026601539 27583980065116083039902309)
  ·
    refine ⟨5171996262209265569981683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27583980065116083039902309 5171996262209265569981683)
    ·
      refine ⟨7757994393313898354972525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5171996262209265569981683 7757994393313898354972525)
      ·
        refine ⟨2909247897492711883114697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7757994393313898354972525 2909247897492711883114697)
        ·
          refine ⟨2181935923119533912336023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2909247897492711883114697 2181935923119533912336023)
          ·
            refine ⟨3272903884679300868504035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181935923119533912336023 3272903884679300868504035)
            ·
              refine ⟨4909355827018951302756053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3272903884679300868504035 4909355827018951302756053)
              ·
                refine ⟨115063027195756671158345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4909355827018951302756053 115063027195756671158345)
                ·
                  rfl

theorem cell20_756285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 7].length) (baseStart_756285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756285 prefixEnd_756285 := by exact prefixLift 756285
  have htrace : WordTrace (prefixWord ++ tailWord_756285) baseStart_756285 baseEnd_756285 := by
    simpa [prefixWord, tailWord_756285, baseEnd_756285] using wordTrace_append hprefix tailTrace_756285
  have hstable : (prefixWord ++ tailWord_756285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756285).length < 2 ^ (prefixWord ++ tailWord_756285).sum := by decide
  have hdescent : baseEnd_756285 < baseStart_756285 := by decide
  rcases family_descends (prefixWord ++ tailWord_756285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756299 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 4]
def baseStart_756299 : Nat := 118140960795 + 756299 * 2 ^ 59
def prefixEnd_756299 : Nat := 4983230072969 + 3 ^ 40 * 756299 * 2
def baseEnd_756299 : Nat := 345195471568748187008311

theorem tailTrace_756299 : CollatzResearch.WordTrace tailWord_756299 prefixEnd_756299 345195471568748187008311 := by
  unfold tailWord_756299
  simp only [CollatzResearch.WordTrace]
  refine ⟨27584490687065363430911951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18389660458043575620607967 27584490687065363430911951)
  ·
    refine ⟨41376736030598045146367927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27584490687065363430911951 41376736030598045146367927)
    ·
      refine ⟨62065104045897067719551891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41376736030598045146367927 62065104045897067719551891)
      ·
        refine ⟨93097656068845601579327837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62065104045897067719551891 93097656068845601579327837)
        ·
          refine ⟨34911621025817100592247939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93097656068845601579327837 34911621025817100592247939)
          ·
            refine ⟨52367431538725650888371909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34911621025817100592247939 52367431538725650888371909)
            ·
              refine ⟨9818893413511059541569733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52367431538725650888371909 9818893413511059541569733)
              ·
                refine ⟨1841042515033323664044325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9818893413511059541569733 1841042515033323664044325)
                ·
                  refine ⟨345195471568748187008311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1841042515033323664044325 345195471568748187008311)
                  ·
                    rfl

theorem cell20_756299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_756299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756299 prefixEnd_756299 := by exact prefixLift 756299
  have htrace : WordTrace (prefixWord ++ tailWord_756299) baseStart_756299 baseEnd_756299 := by
    simpa [prefixWord, tailWord_756299, baseEnd_756299] using wordTrace_append hprefix tailTrace_756299
  have hstable : (prefixWord ++ tailWord_756299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756299).length < 2 ^ (prefixWord ++ tailWord_756299).sum := by decide
  have hdescent : baseEnd_756299 < baseStart_756299 := by decide
  rcases family_descends (prefixWord ++ tailWord_756299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756375 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 6]
def baseStart_756375 : Nat := 118140960795 + 756375 * 2 ^ 59
def prefixEnd_756375 : Nat := 4983230072969 + 3 ^ 40 * 756375 * 2
def baseEnd_756375 : Nat := 345230160039629700474667

theorem tailTrace_756375 : CollatzResearch.WordTrace tailWord_756375 prefixEnd_756375 345230160039629700474667 := by
  unfold tailWord_756375
  simp only [CollatzResearch.WordTrace]
  refine ⟨27587262634790028410678579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18391508423193352273785719 27587262634790028410678579)
  ·
    refine ⟨41380893952185042616017869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27587262634790028410678579 41380893952185042616017869)
    ·
      refine ⟨15517835232069390981006701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41380893952185042616017869 15517835232069390981006701)
      ·
        refine ⟨5819188212026021617877513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15517835232069390981006701 5819188212026021617877513)
        ·
          refine ⟨4364391159019516213408135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5819188212026021617877513 4364391159019516213408135)
          ·
            refine ⟨6546586738529274320112203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4364391159019516213408135 6546586738529274320112203)
            ·
              refine ⟨9819880107793911480168305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6546586738529274320112203 9819880107793911480168305)
              ·
                refine ⟨7364910080845433610126229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9819880107793911480168305 7364910080845433610126229)
                ·
                  refine ⟨345230160039629700474667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7364910080845433610126229 345230160039629700474667)
                  ·
                    rfl

theorem cell20_756375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_756375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756375 prefixEnd_756375 := by exact prefixLift 756375
  have htrace : WordTrace (prefixWord ++ tailWord_756375) baseStart_756375 baseEnd_756375 := by
    simpa [prefixWord, tailWord_756375, baseEnd_756375] using wordTrace_append hprefix tailTrace_756375
  have hstable : (prefixWord ++ tailWord_756375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756375).length < 2 ^ (prefixWord ++ tailWord_756375).sum := by decide
  have hdescent : baseEnd_756375 < baseStart_756375 := by decide
  rcases family_descends (prefixWord ++ tailWord_756375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756378 : List Nat := [3, 1, 1, 6, 1, 1, 7]
def baseStart_756378 : Nat := 118140960795 + 756378 * 2 ^ 59
def prefixEnd_756378 : Nat := 4983230072969 + 3 ^ 40 * 756378 * 2
def baseEnd_756378 : Nat := 38359058813486113708295

theorem tailTrace_756378 : CollatzResearch.WordTrace tailWord_756378 prefixEnd_756378 38359058813486113708295 := by
  unfold tailWord_756378
  simp only [CollatzResearch.WordTrace]
  refine ⟨6896843013444789980759447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18391581369186106615358525 6896843013444789980759447)
  ·
    refine ⟨10345264520167184971139171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6896843013444789980759447 10345264520167184971139171)
    ·
      refine ⟨15517896780250777456708757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10345264520167184971139171 15517896780250777456708757)
      ·
        refine ⟨727401411574255193283223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15517896780250777456708757 727401411574255193283223)
        ·
          refine ⟨1091102117361382789924835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727401411574255193283223 1091102117361382789924835)
          ·
            refine ⟨1636653176042074184887253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091102117361382789924835 1636653176042074184887253)
            ·
              refine ⟨38359058813486113708295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1636653176042074184887253 38359058813486113708295)
              ·
                rfl

theorem cell20_756378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 7].length) (baseStart_756378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756378 prefixEnd_756378 := by exact prefixLift 756378
  have htrace : WordTrace (prefixWord ++ tailWord_756378) baseStart_756378 baseEnd_756378 := by
    simpa [prefixWord, tailWord_756378, baseEnd_756378] using wordTrace_append hprefix tailTrace_756378
  have hstable : (prefixWord ++ tailWord_756378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756378).length < 2 ^ (prefixWord ++ tailWord_756378).sum := by decide
  have hdescent : baseEnd_756378 < baseStart_756378 := by decide
  rcases family_descends (prefixWord ++ tailWord_756378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756385 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 5]
def baseStart_756385 : Nat := 118140960795 + 756385 * 2 ^ 59
def prefixEnd_756385 : Nat := 4983230072969 + 3 ^ 40 * 756385 * 2
def baseEnd_756385 : Nat := 345234724312114110141293

theorem tailTrace_756385 : CollatzResearch.WordTrace tailWord_756385 prefixEnd_756385 345234724312114110141293 := by
  unfold tailWord_756385
  simp only [CollatzResearch.WordTrace]
  refine ⟨27587627364753800118542609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18391751576502533412361739 27587627364753800118542609)
  ·
    refine ⟨20690720523565350088906957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27587627364753800118542609 20690720523565350088906957)
    ·
      refine ⟨7759020196337006283340109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20690720523565350088906957 7759020196337006283340109)
      ·
        refine ⟨2909632573626377356252541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7759020196337006283340109 2909632573626377356252541)
        ·
          refine ⟨1091112215109891508594703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2909632573626377356252541 1091112215109891508594703)
          ·
            refine ⟨1636668322664837262892055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091112215109891508594703 1636668322664837262892055)
            ·
              refine ⟨2455002483997255894338083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636668322664837262892055 2455002483997255894338083)
              ·
                refine ⟨3682503725995883841507125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2455002483997255894338083 3682503725995883841507125)
                ·
                  refine ⟨345234724312114110141293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3682503725995883841507125 345234724312114110141293)
                  ·
                    rfl

theorem cell20_756385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_756385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756385 prefixEnd_756385 := by exact prefixLift 756385
  have htrace : WordTrace (prefixWord ++ tailWord_756385) baseStart_756385 baseEnd_756385 := by
    simpa [prefixWord, tailWord_756385, baseEnd_756385] using wordTrace_append hprefix tailTrace_756385
  have hstable : (prefixWord ++ tailWord_756385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756385).length < 2 ^ (prefixWord ++ tailWord_756385).sum := by decide
  have hdescent : baseEnd_756385 < baseStart_756385 := by decide
  rcases family_descends (prefixWord ++ tailWord_756385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756416 : List Nat := [2, 1, 1, 2, 4, 4, 2, 4]
def baseStart_756416 : Nat := 118140960795 + 756416 * 2 ^ 59
def prefixEnd_756416 : Nat := 4983230072969 + 3 ^ 40 * 756416 * 2
def baseEnd_756416 : Nat := 115082957852271926702611

theorem tailTrace_756416 : CollatzResearch.WordTrace tailWord_756416 prefixEnd_756416 115082957852271926702611 := by
  unfold tailWord_756416
  simp only [CollatzResearch.WordTrace]
  refine ⟨13794379013820746206460551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18392505351760994941947401 13794379013820746206460551)
  ·
    refine ⟨20691568520731119309690827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13794379013820746206460551 20691568520731119309690827)
    ·
      refine ⟨31037352781096678964536241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20691568520731119309690827 31037352781096678964536241)
      ·
        refine ⟨23278014585822509223402181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31037352781096678964536241 23278014585822509223402181)
        ·
          refine ⟨4364627734841720479387909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23278014585822509223402181 4364627734841720479387909)
          ·
            refine ⟨818367700282822589885233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4364627734841720479387909 818367700282822589885233)
            ·
              refine ⟨613775775212116942413925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 818367700282822589885233 613775775212116942413925)
              ·
                refine ⟨115082957852271926702611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 613775775212116942413925 115082957852271926702611)
                ·
                  rfl

theorem cell20_756416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_756416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756416 prefixEnd_756416 := by exact prefixLift 756416
  have htrace : WordTrace (prefixWord ++ tailWord_756416) baseStart_756416 baseEnd_756416 := by
    simpa [prefixWord, tailWord_756416, baseEnd_756416] using wordTrace_append hprefix tailTrace_756416
  have hstable : (prefixWord ++ tailWord_756416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756416).length < 2 ^ (prefixWord ++ tailWord_756416).sum := by decide
  have hdescent : baseEnd_756416 < baseStart_756416 := by decide
  rcases family_descends (prefixWord ++ tailWord_756416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756426 : List Nat := [3, 1, 2, 1, 4, 3, 1, 3, 2]
def baseStart_756426 : Nat := 118140960795 + 756426 * 2 ^ 59
def prefixEnd_756426 : Nat := 4983230072969 + 3 ^ 40 * 756426 * 2
def baseEnd_756426 : Nat := 345253437829300189774459

theorem tailTrace_756426 : CollatzResearch.WordTrace tailWord_756426 prefixEnd_756426 345253437829300189774459 := by
  unfold tailWord_756426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6897280689401316030196283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18392748505070176080523421 6897280689401316030196283)
  ·
    refine ⟨10345921034101974045294425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6897280689401316030196283 10345921034101974045294425)
    ·
      refine ⟨7759440775576480533970819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10345921034101974045294425 7759440775576480533970819)
      ·
        refine ⟨11639161163364720800956229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7759440775576480533970819 11639161163364720800956229)
        ·
          refine ⟨2182342718130885150179293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11639161163364720800956229 2182342718130885150179293)
          ·
            refine ⟨818378519299081931317235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2182342718130885150179293 818378519299081931317235)
            ·
              refine ⟨1227567778948622896975853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818378519299081931317235 1227567778948622896975853)
              ·
                refine ⟨460337917105733586365945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1227567778948622896975853 460337917105733586365945)
                ·
                  refine ⟨345253437829300189774459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460337917105733586365945 345253437829300189774459)
                  ·
                    rfl

theorem cell20_756426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_756426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756426 prefixEnd_756426 := by exact prefixLift 756426
  have htrace : WordTrace (prefixWord ++ tailWord_756426) baseStart_756426 baseEnd_756426 := by
    simpa [prefixWord, tailWord_756426, baseEnd_756426] using wordTrace_append hprefix tailTrace_756426
  have hstable : (prefixWord ++ tailWord_756426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756426).length < 2 ^ (prefixWord ++ tailWord_756426).sum := by decide
  have hdescent : baseEnd_756426 < baseStart_756426 := by decide
  rcases family_descends (prefixWord ++ tailWord_756426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756461 : List Nat := [1, 5, 1, 2, 1, 1, 3, 3, 3]
def baseStart_756461 : Nat := 118140960795 + 756461 * 2 ^ 59
def prefixEnd_756461 : Nat := 4983230072969 + 3 ^ 40 * 756461 * 2
def baseEnd_756461 : Nat := 345269412782995623607649

theorem tailTrace_756461 : CollatzResearch.WordTrace tailWord_756461 prefixEnd_756461 345269412782995623607649 := by
  unfold tailWord_756461
  simp only [CollatzResearch.WordTrace]
  refine ⟨27590399312478465098309237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18393599541652310065539491 27590399312478465098309237)
  ·
    refine ⟨2586599935544856102966491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27590399312478465098309237 2586599935544856102966491)
    ·
      refine ⟨3879899903317284154449737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2586599935544856102966491 3879899903317284154449737)
      ·
        refine ⟨2909924927487963115837303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3879899903317284154449737 2909924927487963115837303)
        ·
          refine ⟨4364887391231944673755955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2909924927487963115837303 4364887391231944673755955)
          ·
            refine ⟨6547331086847917010633933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4364887391231944673755955 6547331086847917010633933)
            ·
              refine ⟨2455249157567968878987725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6547331086847917010633933 2455249157567968878987725)
              ·
                refine ⟨920718434087988329620397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2455249157567968878987725 920718434087988329620397)
                ·
                  refine ⟨345269412782995623607649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920718434087988329620397 345269412782995623607649)
                  ·
                    rfl

theorem cell20_756461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_756461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756461 prefixEnd_756461 := by exact prefixLift 756461
  have htrace : WordTrace (prefixWord ++ tailWord_756461) baseStart_756461 baseEnd_756461 := by
    simpa [prefixWord, tailWord_756461, baseEnd_756461] using wordTrace_append hprefix tailTrace_756461
  have hstable : (prefixWord ++ tailWord_756461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756461).length < 2 ^ (prefixWord ++ tailWord_756461).sum := by decide
  have hdescent : baseEnd_756461 < baseStart_756461 := by decide
  rcases family_descends (prefixWord ++ tailWord_756461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756498 : List Nat := [3, 2, 4, 1, 2, 2, 2, 2, 2]
def baseStart_756498 : Nat := 118140960795 + 756498 * 2 ^ 59
def prefixEnd_756498 : Nat := 4983230072969 + 3 ^ 40 * 756498 * 2
def baseEnd_756498 : Nat := 345286300591187939374165

theorem tailTrace_756498 : CollatzResearch.WordTrace tailWord_756498 prefixEnd_756498 345286300591187939374165 := by
  unfold tailWord_756498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6897937203336105104351537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18394499208896280278270765 6897937203336105104351537)
  ·
    refine ⟨5173452902502078828263653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6897937203336105104351537 5173452902502078828263653)
    ·
      refine ⟨970022419219139780299435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5173452902502078828263653 970022419219139780299435)
      ·
        refine ⟨1455033628828709670449153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970022419219139780299435 1455033628828709670449153)
        ·
          refine ⟨1091275221621532252836865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1455033628828709670449153 1091275221621532252836865)
          ·
            refine ⟨818456416216149189627649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091275221621532252836865 818456416216149189627649)
            ·
              refine ⟨613842312162111892220737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 818456416216149189627649 613842312162111892220737)
              ·
                refine ⟨460381734121583919165553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 613842312162111892220737 460381734121583919165553)
                ·
                  refine ⟨345286300591187939374165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460381734121583919165553 345286300591187939374165)
                  ·
                    rfl

theorem cell20_756498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_756498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756498 prefixEnd_756498 := by exact prefixLift 756498
  have htrace : WordTrace (prefixWord ++ tailWord_756498) baseStart_756498 baseEnd_756498 := by
    simpa [prefixWord, tailWord_756498, baseEnd_756498] using wordTrace_append hprefix tailTrace_756498
  have hstable : (prefixWord ++ tailWord_756498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756498).length < 2 ^ (prefixWord ++ tailWord_756498).sum := by decide
  have hdescent : baseEnd_756498 < baseStart_756498 := by decide
  rcases family_descends (prefixWord ++ tailWord_756498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756509 : List Nat := [1, 4, 2, 4, 1, 2, 1, 5]
def baseStart_756509 : Nat := 118140960795 + 756509 * 2 ^ 59
def prefixEnd_756509 : Nat := 4983230072969 + 3 ^ 40 * 756509 * 2
def baseEnd_756509 : Nat := 115097107096973596669151

theorem tailTrace_756509 : CollatzResearch.WordTrace tailWord_756509 prefixEnd_756509 115097107096973596669151 := by
  unfold tailWord_756509
  simp only [CollatzResearch.WordTrace]
  refine ⟨27592150016304569296056581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18394766677536379530704387 27592150016304569296056581)
  ·
    refine ⟨5173528128057106743010609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27592150016304569296056581 5173528128057106743010609)
    ·
      refine ⟨3880146096042830057257957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5173528128057106743010609 3880146096042830057257957)
      ·
        refine ⟨727527393008030635735867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3880146096042830057257957 727527393008030635735867)
        ·
          refine ⟨1091291089512045953603801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727527393008030635735867 1091291089512045953603801)
          ·
            refine ⟨818468317134034465202851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091291089512045953603801 818468317134034465202851)
            ·
              refine ⟨1227702475701051697804277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818468317134034465202851 1227702475701051697804277)
              ·
                refine ⟨115097107096973596669151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1227702475701051697804277 115097107096973596669151)
                ·
                  rfl

theorem cell20_756509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 5].length) (baseStart_756509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756509 prefixEnd_756509 := by exact prefixLift 756509
  have htrace : WordTrace (prefixWord ++ tailWord_756509) baseStart_756509 baseEnd_756509 := by
    simpa [prefixWord, tailWord_756509, baseEnd_756509] using wordTrace_append hprefix tailTrace_756509
  have hstable : (prefixWord ++ tailWord_756509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756509).length < 2 ^ (prefixWord ++ tailWord_756509).sum := by decide
  have hdescent : baseEnd_756509 < baseStart_756509 := by decide
  rcases family_descends (prefixWord ++ tailWord_756509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756550 : List Nat := [6, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_756550 : Nat := 118140960795 + 756550 * 2 ^ 59
def prefixEnd_756550 : Nat := 4983230072969 + 3 ^ 40 * 756550 * 2
def baseEnd_756550 : Nat := 345310034808106869640619

theorem tailTrace_756550 : CollatzResearch.WordTrace tailWord_756550 prefixEnd_756550 345310034808106869640619 := by
  unfold tailWord_756550
  simp only [CollatzResearch.WordTrace]
  refine ⟨862301419036126040571847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18395763606104022198866069 862301419036126040571847)
  ·
    refine ⟨1293452128554189060857771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 862301419036126040571847 1293452128554189060857771)
    ·
      refine ⟨1940178192831283591286657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1293452128554189060857771 1940178192831283591286657)
      ·
        refine ⟨1455133644623462693464993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1940178192831283591286657 1455133644623462693464993)
        ·
          refine ⟨1091350233467597020098745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1455133644623462693464993 1091350233467597020098745)
          ·
            refine ⟨818512675100697765074059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091350233467597020098745 818512675100697765074059)
            ·
              refine ⟨1227769012651046647611089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818512675100697765074059 1227769012651046647611089)
              ·
                refine ⟨920826759488284985708317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1227769012651046647611089 920826759488284985708317)
                ·
                  refine ⟨345310034808106869640619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920826759488284985708317 345310034808106869640619)
                  ·
                    rfl

theorem cell20_756550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_756550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756550 prefixEnd_756550 := by exact prefixLift 756550
  have htrace : WordTrace (prefixWord ++ tailWord_756550) baseStart_756550 baseEnd_756550 := by
    simpa [prefixWord, tailWord_756550, baseEnd_756550] using wordTrace_append hprefix tailTrace_756550
  have hstable : (prefixWord ++ tailWord_756550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756550).length < 2 ^ (prefixWord ++ tailWord_756550).sum := by decide
  have hdescent : baseEnd_756550 < baseStart_756550 := by decide
  rcases family_descends (prefixWord ++ tailWord_756550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756575 : List Nat := [1, 1, 2, 3, 1, 3, 5, 1, 3]
def baseStart_756575 : Nat := 118140960795 + 756575 * 2 ^ 59
def prefixEnd_756575 : Nat := 4983230072969 + 3 ^ 40 * 756575 * 2
def baseEnd_756575 : Nat := 345321445489317893807183

theorem tailTrace_756575 : CollatzResearch.WordTrace tailWord_756575 prefixEnd_756575 345321445489317893807183 := by
  unfold tailWord_756575
  simp only [CollatzResearch.WordTrace]
  refine ⟨27594557234065462567959179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18396371489376975045306119 27594557234065462567959179)
  ·
    refine ⟨41391835851098193851938769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27594557234065462567959179 41391835851098193851938769)
    ·
      refine ⟨31043876888323645388954077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41391835851098193851938769 31043876888323645388954077)
      ·
        refine ⟨11641453833121367020857779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31043876888323645388954077 11641453833121367020857779)
        ·
          refine ⟨17462180749682050531286669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11641453833121367020857779 17462180749682050531286669)
          ·
            refine ⟨6548317781130768949232501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17462180749682050531286669 6548317781130768949232501)
            ·
              refine ⟨613904791981009588990547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6548317781130768949232501 613904791981009588990547)
              ·
                refine ⟨920857187971514383485821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613904791981009588990547 920857187971514383485821)
                ·
                  refine ⟨345321445489317893807183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920857187971514383485821 345321445489317893807183)
                  ·
                    rfl

theorem cell20_756575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 3].length) (baseStart_756575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756575 prefixEnd_756575 := by exact prefixLift 756575
  have htrace : WordTrace (prefixWord ++ tailWord_756575) baseStart_756575 baseEnd_756575 := by
    simpa [prefixWord, tailWord_756575, baseEnd_756575] using wordTrace_append hprefix tailTrace_756575
  have hstable : (prefixWord ++ tailWord_756575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756575).length < 2 ^ (prefixWord ++ tailWord_756575).sum := by decide
  have hdescent : baseEnd_756575 < baseStart_756575 := by decide
  rcases family_descends (prefixWord ++ tailWord_756575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756616 : List Nat := [2, 1, 3, 3, 2, 2, 3, 2, 2]
def baseStart_756616 : Nat := 118140960795 + 756616 * 2 ^ 59
def prefixEnd_756616 : Nat := 4983230072969 + 3 ^ 40 * 756616 * 2
def baseEnd_756616 : Nat := 345340159006503973440349

theorem tailTrace_756616 : CollatzResearch.WordTrace tailWord_756616 prefixEnd_756616 345340159006503973440349 := by
  unfold tailWord_756616
  simp only [CollatzResearch.WordTrace]
  refine ⟨13798026313458463285100851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18397368417944617713467801 13798026313458463285100851)
  ·
    refine ⟨20697039470187694927651277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13798026313458463285100851 20697039470187694927651277)
    ·
      refine ⟨7761389801320385597869229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20697039470187694927651277 7761389801320385597869229)
      ·
        refine ⟨2910521175495144599200961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7761389801320385597869229 2910521175495144599200961)
        ·
          refine ⟨2182890881621358449400721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2910521175495144599200961 2182890881621358449400721)
          ·
            refine ⟨1637168161216018837050541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2182890881621358449400721 1637168161216018837050541)
            ·
              refine ⟨613938060456007063893953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1637168161216018837050541 613938060456007063893953)
              ·
                refine ⟨460453545342005297920465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 613938060456007063893953 460453545342005297920465)
                ·
                  refine ⟨345340159006503973440349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460453545342005297920465 345340159006503973440349)
                  ·
                    rfl

theorem cell20_756616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 2].length) (baseStart_756616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756616 prefixEnd_756616 := by exact prefixLift 756616
  have htrace : WordTrace (prefixWord ++ tailWord_756616) baseStart_756616 baseEnd_756616 := by
    simpa [prefixWord, tailWord_756616, baseEnd_756616] using wordTrace_append hprefix tailTrace_756616
  have hstable : (prefixWord ++ tailWord_756616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756616).length < 2 ^ (prefixWord ++ tailWord_756616).sum := by decide
  have hdescent : baseEnd_756616 < baseStart_756616 := by decide
  rcases family_descends (prefixWord ++ tailWord_756616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756620 : List Nat := [2, 2, 1, 2, 1, 2, 2, 6, 2]
def baseStart_756620 : Nat := 118140960795 + 756620 * 2 ^ 59
def prefixEnd_756620 : Nat := 4983230072969 + 3 ^ 40 * 756620 * 2
def baseEnd_756620 : Nat := 345341984715497737306999

theorem tailTrace_756620 : CollatzResearch.WordTrace tailWord_756620 prefixEnd_756620 345341984715497737306999 := by
  unfold tailWord_756620
  simp only [CollatzResearch.WordTrace]
  refine ⟨13798099259451217626673657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18397465679268290168898209 13798099259451217626673657)
  ·
    refine ⟨10348574444588413220005243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13798099259451217626673657 10348574444588413220005243)
    ·
      refine ⟨15522861666882619830007865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10348574444588413220005243 15522861666882619830007865)
      ·
        refine ⟨11642146250161964872505899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15522861666882619830007865 11642146250161964872505899)
        ·
          refine ⟨17463219375242947308758849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11642146250161964872505899 17463219375242947308758849)
          ·
            refine ⟨13097414531432210481569137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17463219375242947308758849 13097414531432210481569137)
            ·
              refine ⟨9823060898574157861176853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13097414531432210481569137 9823060898574157861176853)
              ·
                refine ⟨460455979620663649742665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9823060898574157861176853 460455979620663649742665)
                ·
                  refine ⟨345341984715497737306999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460455979620663649742665 345341984715497737306999)
                  ·
                    rfl

theorem cell20_756620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_756620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756620 prefixEnd_756620 := by exact prefixLift 756620
  have htrace : WordTrace (prefixWord ++ tailWord_756620) baseStart_756620 baseEnd_756620 := by
    simpa [prefixWord, tailWord_756620, baseEnd_756620] using wordTrace_append hprefix tailTrace_756620
  have hstable : (prefixWord ++ tailWord_756620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756620).length < 2 ^ (prefixWord ++ tailWord_756620).sum := by decide
  have hdescent : baseEnd_756620 < baseStart_756620 := by decide
  rcases family_descends (prefixWord ++ tailWord_756620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756626 : List Nat := [3, 2, 3, 2, 3, 1, 2, 1, 3]
def baseStart_756626 : Nat := 118140960795 + 756626 * 2 ^ 59
def prefixEnd_756626 : Nat := 4983230072969 + 3 ^ 40 * 756626 * 2
def baseEnd_756626 : Nat := 345344723278988383106975

theorem tailTrace_756626 : CollatzResearch.WordTrace tailWord_756626 prefixEnd_756626 345344723278988383106975 := by
  unfold tailWord_756626
  simp only [CollatzResearch.WordTrace]
  refine ⟨6899104339220174569516433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18397611571253798852043821 6899104339220174569516433)
  ·
    refine ⟨5174328254415130927137325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6899104339220174569516433 5174328254415130927137325)
    ·
      refine ⟨1940373095405674097676497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5174328254415130927137325 1940373095405674097676497)
      ·
        refine ⟨1455279821554255573257373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1940373095405674097676497 1455279821554255573257373)
        ·
          refine ⟨545729933082845839971515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1455279821554255573257373 545729933082845839971515)
          ·
            refine ⟨818594899624268759957273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545729933082845839971515 818594899624268759957273)
            ·
              refine ⟨613946174718201569967955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 818594899624268759957273 613946174718201569967955)
              ·
                refine ⟨920919262077302354951933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613946174718201569967955 920919262077302354951933)
                ·
                  refine ⟨345344723278988383106975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920919262077302354951933 345344723278988383106975)
                  ·
                    rfl

theorem cell20_756626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_756626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756626 prefixEnd_756626 := by exact prefixLift 756626
  have htrace : WordTrace (prefixWord ++ tailWord_756626) baseStart_756626 baseEnd_756626 := by
    simpa [prefixWord, tailWord_756626, baseEnd_756626] using wordTrace_append hprefix tailTrace_756626
  have hstable : (prefixWord ++ tailWord_756626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756626).length < 2 ^ (prefixWord ++ tailWord_756626).sum := by decide
  have hdescent : baseEnd_756626 < baseStart_756626 := by decide
  rcases family_descends (prefixWord ++ tailWord_756626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756655 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 5]
def baseStart_756655 : Nat := 118140960795 + 756655 * 2 ^ 59
def prefixEnd_756655 : Nat := 4983230072969 + 3 ^ 40 * 756655 * 2
def baseEnd_756655 : Nat := 345357959669193171140189

theorem tailTrace_756655 : CollatzResearch.WordTrace tailWord_756655 prefixEnd_756655 345357959669193171140189 := by
  unfold tailWord_756655
  simp only [CollatzResearch.WordTrace]
  refine ⟨27597475073775636230871419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18398316715850424153914279 27597475073775636230871419)
  ·
    refine ⟨41396212610663454346307129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27597475073775636230871419 41396212610663454346307129)
    ·
      refine ⟨31047159457997590759730347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41396212610663454346307129 31047159457997590759730347)
      ·
        refine ⟨46570739186996386139595521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31047159457997590759730347 46570739186996386139595521)
        ·
          refine ⟨34928054390247289604696641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46570739186996386139595521 34928054390247289604696641)
          ·
            refine ⟨26196040792685467203522481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34928054390247289604696641 26196040792685467203522481)
            ·
              refine ⟨19647030594514100402641861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26196040792685467203522481 19647030594514100402641861)
              ·
                refine ⟨3683818236471393825495349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19647030594514100402641861 3683818236471393825495349)
                ·
                  refine ⟨345357959669193171140189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3683818236471393825495349 345357959669193171140189)
                  ·
                    rfl

theorem cell20_756655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_756655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756655 prefixEnd_756655 := by exact prefixLift 756655
  have htrace : WordTrace (prefixWord ++ tailWord_756655) baseStart_756655 baseEnd_756655 := by
    simpa [prefixWord, tailWord_756655, baseEnd_756655] using wordTrace_append hprefix tailTrace_756655
  have hstable : (prefixWord ++ tailWord_756655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756655).length < 2 ^ (prefixWord ++ tailWord_756655).sum := by decide
  have hdescent : baseEnd_756655 < baseStart_756655 := by decide
  rcases family_descends (prefixWord ++ tailWord_756655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756672 : List Nat := [2, 1, 1, 2, 3, 3, 1, 4, 3]
def baseStart_756672 : Nat := 118140960795 + 756672 * 2 ^ 59
def prefixEnd_756672 : Nat := 4983230072969 + 3 ^ 40 * 756672 * 2
def baseEnd_756672 : Nat := 345365718932416667573453

theorem tailTrace_756672 : CollatzResearch.WordTrace tailWord_756672 prefixEnd_756672 345365718932416667573453 := by
  unfold tailWord_756672
  simp only [CollatzResearch.WordTrace]
  refine ⟨13799047557357024067120135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18398730076476032089493513 13799047557357024067120135)
  ·
    refine ⟨20698571336035536100680203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13799047557357024067120135 20698571336035536100680203)
    ·
      refine ⟨31047857004053304151020305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20698571336035536100680203 31047857004053304151020305)
      ·
        refine ⟨23285892753039978113265229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31047857004053304151020305 23285892753039978113265229)
        ·
          refine ⟨8732209782389991792474461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23285892753039978113265229 8732209782389991792474461)
          ·
            refine ⟨3274578668396246922177923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8732209782389991792474461 3274578668396246922177923)
            ·
              refine ⟨4911868002594370383266885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3274578668396246922177923 4911868002594370383266885)
              ·
                refine ⟨920975250486444446862541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4911868002594370383266885 920975250486444446862541)
                ·
                  refine ⟨345365718932416667573453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920975250486444446862541 345365718932416667573453)
                  ·
                    rfl

theorem cell20_756672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_756672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756672 prefixEnd_756672 := by exact prefixLift 756672
  have htrace : WordTrace (prefixWord ++ tailWord_756672) baseStart_756672 baseEnd_756672 := by
    simpa [prefixWord, tailWord_756672, baseEnd_756672] using wordTrace_append hprefix tailTrace_756672
  have hstable : (prefixWord ++ tailWord_756672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756672).length < 2 ^ (prefixWord ++ tailWord_756672).sum := by decide
  have hdescent : baseEnd_756672 < baseStart_756672 := by decide
  rcases family_descends (prefixWord ++ tailWord_756672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756762 : List Nat := [3, 1, 1, 3, 1, 2, 3, 6]
def baseStart_756762 : Nat := 118140960795 + 756762 * 2 ^ 59
def prefixEnd_756762 : Nat := 4983230072969 + 3 ^ 40 * 756762 * 2
def baseEnd_756762 : Nat := 115135599128258784857695

theorem tailTrace_756762 : CollatzResearch.WordTrace tailWord_756762 prefixEnd_756762 115135599128258784857695 := by
  unfold tailWord_756762
  simp only [CollatzResearch.WordTrace]
  refine ⟨6900344421096998376254135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18400918456258662336677693 6900344421096998376254135)
  ·
    refine ⟨10350516631645497564381203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6900344421096998376254135 10350516631645497564381203)
    ·
      refine ⟨15525774947468246346571805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10350516631645497564381203 15525774947468246346571805)
      ·
        refine ⟨5822165605300592379964427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15525774947468246346571805 5822165605300592379964427)
        ·
          refine ⟨8733248407950888569946641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5822165605300592379964427 8733248407950888569946641)
          ·
            refine ⟨6549936305963166427459981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8733248407950888569946641 6549936305963166427459981)
            ·
              refine ⟨2456226114736187410297493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6549936305963166427459981 2456226114736187410297493)
              ·
                refine ⟨115135599128258784857695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2456226114736187410297493 115135599128258784857695)
                ·
                  rfl

theorem cell20_756762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_756762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756762 prefixEnd_756762 := by exact prefixLift 756762
  have htrace : WordTrace (prefixWord ++ tailWord_756762) baseStart_756762 baseEnd_756762 := by
    simpa [prefixWord, tailWord_756762, baseEnd_756762] using wordTrace_append hprefix tailTrace_756762
  have hstable : (prefixWord ++ tailWord_756762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756762).length < 2 ^ (prefixWord ++ tailWord_756762).sum := by decide
  have hdescent : baseEnd_756762 < baseStart_756762 := by decide
  rcases family_descends (prefixWord ++ tailWord_756762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756786 : List Nat := [3, 2, 1, 1, 2, 2, 2, 4, 3]
def baseStart_756786 : Nat := 118140960795 + 756786 * 2 ^ 59
def prefixEnd_756786 : Nat := 4983230072969 + 3 ^ 40 * 756786 * 2
def baseEnd_756786 : Nat := 345417751638738937772987

theorem tailTrace_756786 : CollatzResearch.WordTrace tailWord_756786 prefixEnd_756786 345417751638738937772987 := by
  unfold tailWord_756786
  simp only [CollatzResearch.WordTrace]
  refine ⟨6900563259075261400972553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18401502024200697069260141 6900563259075261400972553)
  ·
    refine ⟨5175422444306446050729415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6900563259075261400972553 5175422444306446050729415)
    ·
      refine ⟨7763133666459669076094123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5175422444306446050729415 7763133666459669076094123)
      ·
        refine ⟨11644700499689503614141185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7763133666459669076094123 11644700499689503614141185)
        ·
          refine ⟨8733525374767127710605889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11644700499689503614141185 8733525374767127710605889)
          ·
            refine ⟨6550144031075345782954417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8733525374767127710605889 6550144031075345782954417)
            ·
              refine ⟨4912608023306509337215813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6550144031075345782954417 4912608023306509337215813)
              ·
                refine ⟨921114004369970500727965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4912608023306509337215813 921114004369970500727965)
                ·
                  refine ⟨345417751638738937772987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 921114004369970500727965 345417751638738937772987)
                  ·
                    rfl

theorem cell20_756786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_756786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756786 prefixEnd_756786 := by exact prefixLift 756786
  have htrace : WordTrace (prefixWord ++ tailWord_756786) baseStart_756786 baseEnd_756786 := by
    simpa [prefixWord, tailWord_756786, baseEnd_756786] using wordTrace_append hprefix tailTrace_756786
  have hstable : (prefixWord ++ tailWord_756786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756786).length < 2 ^ (prefixWord ++ tailWord_756786).sum := by decide
  have hdescent : baseEnd_756786 < baseStart_756786 := by decide
  rcases family_descends (prefixWord ++ tailWord_756786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756800 : List Nat := [2, 1, 1, 2, 2, 3, 4, 5]
def baseStart_756800 : Nat := 118140960795 + 756800 * 2 ^ 59
def prefixEnd_756800 : Nat := 4983230072969 + 3 ^ 40 * 756800 * 2
def baseEnd_756800 : Nat := 115141380540072370435421

theorem tailTrace_756800 : CollatzResearch.WordTrace tailWord_756800 prefixEnd_756800 115141380540072370435421 := by
  unfold tailWord_756800
  simp only [CollatzResearch.WordTrace]
  refine ⟨13801381829125162997449927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18401842438833550663266569 13801381829125162997449927)
  ·
    refine ⟨20702072743687744496174891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13801381829125162997449927 20702072743687744496174891)
    ·
      refine ⟨31053109115531616744262337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20702072743687744496174891 31053109115531616744262337)
      ·
        refine ⟨23289831836648712558196753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31053109115531616744262337 23289831836648712558196753)
        ·
          refine ⟨17467373877486534418647565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23289831836648712558196753 17467373877486534418647565)
          ·
            refine ⟨6550265204057450406992837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17467373877486534418647565 6550265204057450406992837)
            ·
              refine ⟨1228174725760771951311157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6550265204057450406992837 1228174725760771951311157)
              ·
                refine ⟨115141380540072370435421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1228174725760771951311157 115141380540072370435421)
                ·
                  rfl

theorem cell20_756800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_756800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756800 prefixEnd_756800 := by exact prefixLift 756800
  have htrace : WordTrace (prefixWord ++ tailWord_756800) baseStart_756800 baseEnd_756800 := by
    simpa [prefixWord, tailWord_756800, baseEnd_756800] using wordTrace_append hprefix tailTrace_756800
  have hstable : (prefixWord ++ tailWord_756800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756800).length < 2 ^ (prefixWord ++ tailWord_756800).sum := by decide
  have hdescent : baseEnd_756800 < baseStart_756800 := by decide
  rcases family_descends (prefixWord ++ tailWord_756800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756840 : List Nat := [2, 1, 4, 4, 2, 1, 2, 2, 2]
def baseStart_756840 : Nat := 118140960795 + 756840 * 2 ^ 59
def prefixEnd_756840 : Nat := 4983230072969 + 3 ^ 40 * 756840 * 2
def baseEnd_756840 : Nat := 345442398710154749972767

theorem tailTrace_756840 : CollatzResearch.WordTrace tailWord_756840 prefixEnd_756840 345442398710154749972767 := by
  unfold tailWord_756840
  simp only [CollatzResearch.WordTrace]
  refine ⟨13802111289052706413177987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18402815052070275217570649 13802111289052706413177987)
  ·
    refine ⟨20703166933579059619766981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13802111289052706413177987 20703166933579059619766981)
    ·
      refine ⟨3881843800046073678706309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20703166933579059619766981 3881843800046073678706309)
      ·
        refine ⟨727845712508638814757433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3881843800046073678706309 727845712508638814757433)
        ·
          refine ⟨545884284381479111068075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 727845712508638814757433 545884284381479111068075)
          ·
            refine ⟨818826426572218666602113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545884284381479111068075 818826426572218666602113)
            ·
              refine ⟨614119819929163999951585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 818826426572218666602113 614119819929163999951585)
              ·
                refine ⟨460589864946872999963689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 614119819929163999951585 460589864946872999963689)
                ·
                  refine ⟨345442398710154749972767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460589864946872999963689 345442398710154749972767)
                  ·
                    rfl

theorem cell20_756840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 2].length) (baseStart_756840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756840 prefixEnd_756840 := by exact prefixLift 756840
  have htrace : WordTrace (prefixWord ++ tailWord_756840) baseStart_756840 baseEnd_756840 := by
    simpa [prefixWord, tailWord_756840, baseEnd_756840] using wordTrace_append hprefix tailTrace_756840
  have hstable : (prefixWord ++ tailWord_756840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756840).length < 2 ^ (prefixWord ++ tailWord_756840).sum := by decide
  have hdescent : baseEnd_756840 < baseStart_756840 := by decide
  rcases family_descends (prefixWord ++ tailWord_756840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756848 : List Nat := [2, 1, 1, 1, 5, 1, 3, 4, 2]
def baseStart_756848 : Nat := 118140960795 + 756848 * 2 ^ 59
def prefixEnd_756848 : Nat := 4983230072969 + 3 ^ 40 * 756848 * 2
def baseEnd_756848 : Nat := 345446050128142277706067

theorem tailTrace_756848 : CollatzResearch.WordTrace tailWord_756848 prefixEnd_756848 345446050128142277706067 := by
  unfold tailWord_756848
  simp only [CollatzResearch.WordTrace]
  refine ⟨13802257181038215096323599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18403009574717620128431465 13802257181038215096323599)
  ·
    refine ⟨20703385771557322644485399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13802257181038215096323599 20703385771557322644485399)
    ·
      refine ⟨31055078657335983966728099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20703385771557322644485399 31055078657335983966728099)
      ·
        refine ⟨46582617986003975950092149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31055078657335983966728099 46582617986003975950092149)
        ·
          refine ⟨4367120436187872745321139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46582617986003975950092149 4367120436187872745321139)
          ·
            refine ⟨6550680654281809117981709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4367120436187872745321139 6550680654281809117981709)
            ·
              refine ⟨2456505245355678419243141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6550680654281809117981709 2456505245355678419243141)
              ·
                refine ⟨460594733504189703608089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2456505245355678419243141 460594733504189703608089)
                ·
                  refine ⟨345446050128142277706067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460594733504189703608089 345446050128142277706067)
                  ·
                    rfl

theorem cell20_756848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 2].length) (baseStart_756848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756848 prefixEnd_756848 := by exact prefixLift 756848
  have htrace : WordTrace (prefixWord ++ tailWord_756848) baseStart_756848 baseEnd_756848 := by
    simpa [prefixWord, tailWord_756848, baseEnd_756848] using wordTrace_append hprefix tailTrace_756848
  have hstable : (prefixWord ++ tailWord_756848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756848).length < 2 ^ (prefixWord ++ tailWord_756848).sum := by decide
  have hdescent : baseEnd_756848 < baseStart_756848 := by decide
  rcases family_descends (prefixWord ++ tailWord_756848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756872 : List Nat := [2, 1, 3, 4, 2, 1, 3, 4]
def baseStart_756872 : Nat := 118140960795 + 756872 * 2 ^ 59
def prefixEnd_756872 : Nat := 4983230072969 + 3 ^ 40 * 756872 * 2
def baseEnd_756872 : Nat := 115152334794034953635323

theorem tailTrace_756872 : CollatzResearch.WordTrace tailWord_756872 prefixEnd_756872 115152334794034953635323 := by
  unfold tailWord_756872
  simp only [CollatzResearch.WordTrace]
  refine ⟨13802694856994741145760435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18403593142659654861013913 13802694856994741145760435)
  ·
    refine ⟨20704042285492111718640653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13802694856994741145760435 20704042285492111718640653)
    ·
      refine ⟨7764015857059541894490245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20704042285492111718640653 7764015857059541894490245)
      ·
        refine ⟨1455752973198664105216921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7764015857059541894490245 1455752973198664105216921)
        ·
          refine ⟨1091814729898998078912691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1455752973198664105216921 1091814729898998078912691)
          ·
            refine ⟨1637722094848497118369037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091814729898998078912691 1637722094848497118369037)
            ·
              refine ⟨614145785568186419388389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1637722094848497118369037 614145785568186419388389)
              ·
                refine ⟨115152334794034953635323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 614145785568186419388389 115152334794034953635323)
                ·
                  rfl

theorem cell20_756872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_756872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756872 prefixEnd_756872 := by exact prefixLift 756872
  have htrace : WordTrace (prefixWord ++ tailWord_756872) baseStart_756872 baseEnd_756872 := by
    simpa [prefixWord, tailWord_756872, baseEnd_756872] using wordTrace_append hprefix tailTrace_756872
  have hstable : (prefixWord ++ tailWord_756872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756872).length < 2 ^ (prefixWord ++ tailWord_756872).sum := by decide
  have hdescent : baseEnd_756872 < baseStart_756872 := by decide
  rcases family_descends (prefixWord ++ tailWord_756872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756900 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 5]
def baseStart_756900 : Nat := 118140960795 + 756900 * 2 ^ 59
def prefixEnd_756900 : Nat := 4983230072969 + 3 ^ 40 * 756900 * 2
def baseEnd_756900 : Nat := 345469784345061207972521

theorem tailTrace_756900 : CollatzResearch.WordTrace tailWord_756900 prefixEnd_756900 345469784345061207972521 := by
  unfold tailWord_756900
  simp only [CollatzResearch.WordTrace]
  refine ⟨13803205478944021536770077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18404273971925362049026769 13803205478944021536770077)
  ·
    refine ⟨5176202054604008076288779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13803205478944021536770077 5176202054604008076288779)
    ·
      refine ⟨7764303081906012114433169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5176202054604008076288779 7764303081906012114433169)
      ·
        refine ⟨5823227311429509085824877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7764303081906012114433169 5823227311429509085824877)
        ·
          refine ⟨2183710241786065907184329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5823227311429509085824877 2183710241786065907184329)
          ·
            refine ⟨1637782681339549430388247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2183710241786065907184329 1637782681339549430388247)
            ·
              refine ⟨2456674022009324145582371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637782681339549430388247 2456674022009324145582371)
              ·
                refine ⟨3685011033013986218373557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2456674022009324145582371 3685011033013986218373557)
                ·
                  refine ⟨345469784345061207972521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3685011033013986218373557 345469784345061207972521)
                  ·
                    rfl

theorem cell20_756900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_756900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756900 prefixEnd_756900 := by exact prefixLift 756900
  have htrace : WordTrace (prefixWord ++ tailWord_756900) baseStart_756900 baseEnd_756900 := by
    simpa [prefixWord, tailWord_756900, baseEnd_756900] using wordTrace_append hprefix tailTrace_756900
  have hstable : (prefixWord ++ tailWord_756900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756900).length < 2 ^ (prefixWord ++ tailWord_756900).sum := by decide
  have hdescent : baseEnd_756900 < baseStart_756900 := by decide
  rcases family_descends (prefixWord ++ tailWord_756900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756903 : List Nat := [1, 1, 6, 2, 1, 1, 2, 4, 2]
def baseStart_756903 : Nat := 118140960795 + 756903 * 2 ^ 59
def prefixEnd_756903 : Nat := 4983230072969 + 3 ^ 40 * 756903 * 2
def baseEnd_756903 : Nat := 345471153626806530872509

theorem tailTrace_756903 : CollatzResearch.WordTrace tailWord_756903 prefixEnd_756903 345471153626806530872509 := by
  unfold tailWord_756903
  simp only [CollatzResearch.WordTrace]
  refine ⟨27606520376877174585899363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18404346917918116390599575 27606520376877174585899363)
  ·
    refine ⟨41409780565315761878849045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27606520376877174585899363 41409780565315761878849045)
    ·
      refine ⟨1941083463999176338071049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41409780565315761878849045 1941083463999176338071049)
      ·
        refine ⟨1455812597999382253553287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1941083463999176338071049 1455812597999382253553287)
        ·
          refine ⟨2183718896999073380329931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455812597999382253553287 2183718896999073380329931)
          ·
            refine ⟨3275578345498610070494897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183718896999073380329931 3275578345498610070494897)
            ·
              refine ⟨2456683759123957552871173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3275578345498610070494897 2456683759123957552871173)
              ·
                refine ⟨460628204835742041163345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2456683759123957552871173 460628204835742041163345)
                ·
                  refine ⟨345471153626806530872509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460628204835742041163345 345471153626806530872509)
                  ·
                    rfl

theorem cell20_756903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 2].length) (baseStart_756903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756903 prefixEnd_756903 := by exact prefixLift 756903
  have htrace : WordTrace (prefixWord ++ tailWord_756903) baseStart_756903 baseEnd_756903 := by
    simpa [prefixWord, tailWord_756903, baseEnd_756903] using wordTrace_append hprefix tailTrace_756903
  have hstable : (prefixWord ++ tailWord_756903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756903).length < 2 ^ (prefixWord ++ tailWord_756903).sum := by decide
  have hdescent : baseEnd_756903 < baseStart_756903 := by decide
  rcases family_descends (prefixWord ++ tailWord_756903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756948 : List Nat := [2, 4, 1, 4, 1, 2, 6]
def baseStart_756948 : Nat := 118140960795 + 756948 * 2 ^ 59
def prefixEnd_756948 : Nat := 4983230072969 + 3 ^ 40 * 756948 * 2
def baseEnd_756948 : Nat := 38387965872554041596925

theorem tailTrace_756948 : CollatzResearch.WordTrace tailWord_756948 prefixEnd_756948 38387965872554041596925 := by
  unfold tailWord_756948
  simp only [CollatzResearch.WordTrace]
  refine ⟨13804080830857073635643749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18405441107809431514191665 13804080830857073635643749)
  ·
    refine ⟨2588265155785701306683203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13804080830857073635643749 2588265155785701306683203)
    ·
      refine ⟨3882397733678551960024805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2588265155785701306683203 3882397733678551960024805)
      ·
        refine ⟨727949575064728492504651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3882397733678551960024805 727949575064728492504651)
        ·
          refine ⟨1091924362597092738756977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727949575064728492504651 1091924362597092738756977)
          ·
            refine ⟨818943271947819554067733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091924362597092738756977 818943271947819554067733)
            ·
              refine ⟨38387965872554041596925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 818943271947819554067733 38387965872554041596925)
              ·
                rfl

theorem cell20_756948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 6].length) (baseStart_756948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756948 prefixEnd_756948 := by exact prefixLift 756948
  have htrace : WordTrace (prefixWord ++ tailWord_756948) baseStart_756948 baseEnd_756948 := by
    simpa [prefixWord, tailWord_756948, baseEnd_756948] using wordTrace_append hprefix tailTrace_756948
  have hstable : (prefixWord ++ tailWord_756948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756948).length < 2 ^ (prefixWord ++ tailWord_756948).sum := by decide
  have hdescent : baseEnd_756948 < baseStart_756948 := by decide
  rcases family_descends (prefixWord ++ tailWord_756948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756959 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 5]
def baseStart_756959 : Nat := 118140960795 + 756959 * 2 ^ 59
def prefixEnd_756959 : Nat := 4983230072969 + 3 ^ 40 * 756959 * 2
def baseEnd_756959 : Nat := 345496713552719225005613

theorem tailTrace_756959 : CollatzResearch.WordTrace tailWord_756959 prefixEnd_756959 345496713552719225005613 := by
  unfold tailWord_756959
  simp only [CollatzResearch.WordTrace]
  refine ⟨27608562864674296149937931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18405708576449530766625287 27608562864674296149937931)
  ·
    refine ⟨41412844297011444224906897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27608562864674296149937931 41412844297011444224906897)
    ·
      refine ⟨31059633222758583168680173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41412844297011444224906897 31059633222758583168680173)
      ·
        refine ⟨11647362458534468688255065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31059633222758583168680173 11647362458534468688255065)
        ·
          refine ⟨8735521843900851516191299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11647362458534468688255065 8735521843900851516191299)
          ·
            refine ⟨13103282765851277274286949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8735521843900851516191299 13103282765851277274286949)
            ·
              refine ⟨2456865518597114488928803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13103282765851277274286949 2456865518597114488928803)
              ·
                refine ⟨3685298277895671733393205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2456865518597114488928803 3685298277895671733393205)
                ·
                  refine ⟨345496713552719225005613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3685298277895671733393205 345496713552719225005613)
                  ·
                    rfl

theorem cell20_756959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_756959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_756959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_756959 prefixEnd_756959 := by exact prefixLift 756959
  have htrace : WordTrace (prefixWord ++ tailWord_756959) baseStart_756959 baseEnd_756959 := by
    simpa [prefixWord, tailWord_756959, baseEnd_756959] using wordTrace_append hprefix tailTrace_756959
  have hstable : (prefixWord ++ tailWord_756959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756959).length < 2 ^ (prefixWord ++ tailWord_756959).sum := by decide
  have hdescent : baseEnd_756959 < baseStart_756959 := by decide
  rcases family_descends (prefixWord ++ tailWord_756959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757024 : List Nat := [2, 1, 1, 5, 4, 1, 1, 5]
def baseStart_757024 : Nat := 118140960795 + 757024 * 2 ^ 59
def prefixEnd_757024 : Nat := 4983230072969 + 3 ^ 40 * 757024 * 2
def baseEnd_757024 : Nat := 115175460441289295946227

theorem tailTrace_757024 : CollatzResearch.WordTrace tailWord_757024 prefixEnd_757024 115175460441289295946227 := by
  unfold tailWord_757024
  simp only [CollatzResearch.WordTrace]
  refine ⟨13805466804719406125527063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18407289072959208167369417 13805466804719406125527063)
  ·
    refine ⟨20708200207079109188290595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13805466804719406125527063 20708200207079109188290595)
    ·
      refine ⟨31062300310618663782435893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20708200207079109188290595 31062300310618663782435893)
      ·
        refine ⟨2912090654120499729603365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31062300310618663782435893 2912090654120499729603365)
        ·
          refine ⟨546016997647593699300631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2912090654120499729603365 546016997647593699300631)
          ·
            refine ⟨819025496471390548950947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546016997647593699300631 819025496471390548950947)
            ·
              refine ⟨1228538244707085823426421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819025496471390548950947 1228538244707085823426421)
              ·
                refine ⟨115175460441289295946227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1228538244707085823426421 115175460441289295946227)
                ·
                  rfl

theorem cell20_757024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_757024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757024 prefixEnd_757024 := by exact prefixLift 757024
  have htrace : WordTrace (prefixWord ++ tailWord_757024) baseStart_757024 baseEnd_757024 := by
    simpa [prefixWord, tailWord_757024, baseEnd_757024] using wordTrace_append hprefix tailTrace_757024
  have hstable : (prefixWord ++ tailWord_757024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757024).length < 2 ^ (prefixWord ++ tailWord_757024).sum := by decide
  have hdescent : baseEnd_757024 < baseStart_757024 := by decide
  rcases family_descends (prefixWord ++ tailWord_757024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757045 : List Nat := [1, 3, 3, 1, 2, 3, 3, 4]
def baseStart_757045 : Nat := 118140960795 + 757045 * 2 ^ 59
def prefixEnd_757045 : Nat := 4983230072969 + 3 ^ 40 * 757045 * 2
def baseEnd_757045 : Nat := 115178655432028382712865

theorem tailTrace_757045 : CollatzResearch.WordTrace tailWord_757045 prefixEnd_757045 115178655432028382712865 := by
  unfold tailWord_757045
  simp only [CollatzResearch.WordTrace]
  refine ⟨27611699542362732837568589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18407799694908488558379059 27611699542362732837568589)
  ·
    refine ⟨10354387328386024814088221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27611699542362732837568589 10354387328386024814088221)
    ·
      refine ⟨3882895248144759305283083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10354387328386024814088221 3882895248144759305283083)
      ·
        refine ⟨5824342872217138957924625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3882895248144759305283083 5824342872217138957924625)
        ·
          refine ⟨4368257154162854218443469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5824342872217138957924625 4368257154162854218443469)
          ·
            refine ⟨1638096432811070331916301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4368257154162854218443469 1638096432811070331916301)
            ·
              refine ⟨614286162304151374468613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1638096432811070331916301 614286162304151374468613)
              ·
                refine ⟨115178655432028382712865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 614286162304151374468613 115178655432028382712865)
                ·
                  rfl

theorem cell20_757045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 4].length) (baseStart_757045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757045 prefixEnd_757045 := by exact prefixLift 757045
  have htrace : WordTrace (prefixWord ++ tailWord_757045) baseStart_757045 baseEnd_757045 := by
    simpa [prefixWord, tailWord_757045, baseEnd_757045] using wordTrace_append hprefix tailTrace_757045
  have hstable : (prefixWord ++ tailWord_757045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757045).length < 2 ^ (prefixWord ++ tailWord_757045).sum := by decide
  have hdescent : baseEnd_757045 < baseStart_757045 := by decide
  rcases family_descends (prefixWord ++ tailWord_757045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757073 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 5]
def baseStart_757073 : Nat := 118140960795 + 757073 * 2 ^ 59
def prefixEnd_757073 : Nat := 4983230072969 + 3 ^ 40 * 757073 * 2
def baseEnd_757073 : Nat := 345548746259041495205147

theorem tailTrace_757073 : CollatzResearch.WordTrace tailWord_757073 prefixEnd_757073 345548746259041495205147 := by
  unfold tailWord_757073
  simp only [CollatzResearch.WordTrace]
  refine ⟨27612720786261293619587873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18408480524174195746391915 27612720786261293619587873)
  ·
    refine ⟨20709540589695970214690905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27612720786261293619587873 20709540589695970214690905)
    ·
      refine ⟨15532155442271977661018179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20709540589695970214690905 15532155442271977661018179)
      ·
        refine ⟨23298233163407966491527269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15532155442271977661018179 23298233163407966491527269)
        ·
          refine ⟨4368418718138993717161363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23298233163407966491527269 4368418718138993717161363)
          ·
            refine ⟨6552628077208490575742045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4368418718138993717161363 6552628077208490575742045)
            ·
              refine ⟨2457235528953183965903267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6552628077208490575742045 2457235528953183965903267)
              ·
                refine ⟨3685853293429775948854901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2457235528953183965903267 3685853293429775948854901)
                ·
                  refine ⟨345548746259041495205147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3685853293429775948854901 345548746259041495205147)
                  ·
                    rfl

theorem cell20_757073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_757073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757073 prefixEnd_757073 := by exact prefixLift 757073
  have htrace : WordTrace (prefixWord ++ tailWord_757073) baseStart_757073 baseEnd_757073 := by
    simpa [prefixWord, tailWord_757073, baseEnd_757073] using wordTrace_append hprefix tailTrace_757073
  have hstable : (prefixWord ++ tailWord_757073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757073).length < 2 ^ (prefixWord ++ tailWord_757073).sum := by decide
  have hdescent : baseEnd_757073 < baseStart_757073 := by decide
  rcases family_descends (prefixWord ++ tailWord_757073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757076 : List Nat := [2, 4, 1, 1, 2, 1, 1, 6, 2]
def baseStart_757076 : Nat := 118140960795 + 757076 * 2 ^ 59
def prefixEnd_757076 : Nat := 4983230072969 + 3 ^ 40 * 757076 * 2
def baseEnd_757076 : Nat := 345550115540786818105135

theorem tailTrace_757076 : CollatzResearch.WordTrace tailWord_757076 prefixEnd_757076 345550115540786818105135 := by
  unfold tailWord_757076
  simp only [CollatzResearch.WordTrace]
  refine ⟨13806415102625212565973541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18408553470166950087964721 13806415102625212565973541)
  ·
    refine ⟨2588702831742227356120039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13806415102625212565973541 2588702831742227356120039)
    ·
      refine ⟨3883054247613341034180059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2588702831742227356120039 3883054247613341034180059)
      ·
        refine ⟨5824581371420011551270089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3883054247613341034180059 5824581371420011551270089)
        ·
          refine ⟨4368436028565008663452567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5824581371420011551270089 4368436028565008663452567)
          ·
            refine ⟨6552654042847512995178851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4368436028565008663452567 6552654042847512995178851)
            ·
              refine ⟨9828981064271269492768277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6552654042847512995178851 9828981064271269492768277)
              ·
                refine ⟨460733487387715757473513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9828981064271269492768277 460733487387715757473513)
                ·
                  refine ⟨345550115540786818105135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460733487387715757473513 345550115540786818105135)
                  ·
                    rfl

theorem cell20_757076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_757076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757076 prefixEnd_757076 := by exact prefixLift 757076
  have htrace : WordTrace (prefixWord ++ tailWord_757076) baseStart_757076 baseEnd_757076 := by
    simpa [prefixWord, tailWord_757076, baseEnd_757076] using wordTrace_append hprefix tailTrace_757076
  have hstable : (prefixWord ++ tailWord_757076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757076).length < 2 ^ (prefixWord ++ tailWord_757076).sum := by decide
  have hdescent : baseEnd_757076 < baseStart_757076 := by decide
  rcases family_descends (prefixWord ++ tailWord_757076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757087 : List Nat := [1, 1, 2, 3, 1, 2, 1, 9]
def baseStart_757087 : Nat := 118140960795 + 757087 * 2 ^ 59
def prefixEnd_757087 : Nat := 4983230072969 + 3 ^ 40 * 757087 * 2
def baseEnd_757087 : Nat := 115185045413506556246141

theorem tailTrace_757087 : CollatzResearch.WordTrace tailWord_757087 prefixEnd_757087 115185045413506556246141 := by
  unfold tailWord_757087
  simp only [CollatzResearch.WordTrace]
  refine ⟨27613231408210574010597515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18408820938807049340398343 27613231408210574010597515)
  ·
    refine ⟨41419847112315861015896273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27613231408210574010597515 41419847112315861015896273)
    ·
      refine ⟨31064885334236895761922205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41419847112315861015896273 31064885334236895761922205)
      ·
        refine ⟨11649332000338835910720827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31064885334236895761922205 11649332000338835910720827)
        ·
          refine ⟨17473998000508253866081241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11649332000338835910720827 17473998000508253866081241)
          ·
            refine ⟨13105498500381190399560931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17473998000508253866081241 13105498500381190399560931)
            ·
              refine ⟨19658247750571785599341397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13105498500381190399560931 19658247750571785599341397)
              ·
                refine ⟨115185045413506556246141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19658247750571785599341397 115185045413506556246141)
                ·
                  rfl

theorem cell20_757087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 9].length) (baseStart_757087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757087 prefixEnd_757087 := by exact prefixLift 757087
  have htrace : WordTrace (prefixWord ++ tailWord_757087) baseStart_757087 baseEnd_757087 := by
    simpa [prefixWord, tailWord_757087, baseEnd_757087] using wordTrace_append hprefix tailTrace_757087
  have hstable : (prefixWord ++ tailWord_757087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757087).length < 2 ^ (prefixWord ++ tailWord_757087).sum := by decide
  have hdescent : baseEnd_757087 < baseStart_757087 := by decide
  rcases family_descends (prefixWord ++ tailWord_757087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757121 : List Nat := [1, 2, 4, 3, 2, 2, 6]
def baseStart_757121 : Nat := 118140960795 + 757121 * 2 ^ 59
def prefixEnd_757121 : Nat := 4983230072969 + 3 ^ 40 * 757121 * 2
def baseEnd_757121 : Nat := 38396739418551851289439

theorem tailTrace_757121 : CollatzResearch.WordTrace tailWord_757121 prefixEnd_757121 38396739418551851289439 := by
  unfold tailWord_757121
  simp only [CollatzResearch.WordTrace]
  refine ⟨27614471490087397817335217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18409647660058265211556811 27614471490087397817335217)
  ·
    refine ⟨20710853617565548363001413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27614471490087397817335217 20710853617565548363001413)
    ·
      refine ⟨3883285053293540318062765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20710853617565548363001413 3883285053293540318062765)
      ·
        refine ⟨1456231894985077619273537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3883285053293540318062765 1456231894985077619273537)
        ·
          refine ⟨1092173921238808214455153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1456231894985077619273537 1092173921238808214455153)
          ·
            refine ⟨819130440929106160841365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1092173921238808214455153 819130440929106160841365)
            ·
              refine ⟨38396739418551851289439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 819130440929106160841365 38396739418551851289439)
              ·
                rfl

theorem cell20_757121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 6].length) (baseStart_757121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757121 prefixEnd_757121 := by exact prefixLift 757121
  have htrace : WordTrace (prefixWord ++ tailWord_757121) baseStart_757121 baseEnd_757121 := by
    simpa [prefixWord, tailWord_757121, baseEnd_757121] using wordTrace_append hprefix tailTrace_757121
  have hstable : (prefixWord ++ tailWord_757121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757121).length < 2 ^ (prefixWord ++ tailWord_757121).sum := by decide
  have hdescent : baseEnd_757121 < baseStart_757121 := by decide
  rcases family_descends (prefixWord ++ tailWord_757121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757125 : List Nat := [1, 3, 1, 1, 3, 1, 10]
def baseStart_757125 : Nat := 118140960795 + 757125 * 2 ^ 59
def prefixEnd_757125 : Nat := 4983230072969 + 3 ^ 40 * 757125 * 2
def baseEnd_757125 : Nat := 38396942275106713941289

theorem tailTrace_757125 : CollatzResearch.WordTrace tailWord_757125 prefixEnd_757125 38396942275106713941289 := by
  unfold tailWord_757125
  simp only [CollatzResearch.WordTrace]
  refine ⟨27614617382072906500480829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18409744921381937666987219 27614617382072906500480829)
  ·
    refine ⟨10355481518277339937680311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27614617382072906500480829 10355481518277339937680311)
    ·
      refine ⟨15533222277416009906520467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10355481518277339937680311 15533222277416009906520467)
      ·
        refine ⟨23299833416124014859780701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15533222277416009906520467 23299833416124014859780701)
        ·
          refine ⟨8737437531046505572417763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23299833416124014859780701 8737437531046505572417763)
          ·
            refine ⟨13106156296569758358626645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8737437531046505572417763 13106156296569758358626645)
            ·
              refine ⟨38396942275106713941289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13106156296569758358626645 38396942275106713941289)
              ·
                rfl

theorem cell20_757125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 10].length) (baseStart_757125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757125 prefixEnd_757125 := by exact prefixLift 757125
  have htrace : WordTrace (prefixWord ++ tailWord_757125) baseStart_757125 baseEnd_757125 := by
    simpa [prefixWord, tailWord_757125, baseEnd_757125] using wordTrace_append hprefix tailTrace_757125
  have hstable : (prefixWord ++ tailWord_757125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757125).length < 2 ^ (prefixWord ++ tailWord_757125).sum := by decide
  have hdescent : baseEnd_757125 < baseStart_757125 := by decide
  rcases family_descends (prefixWord ++ tailWord_757125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757138 : List Nat := [3, 2, 3, 3, 1, 1, 2, 5]
def baseStart_757138 : Nat := 118140960795 + 757138 * 2 ^ 59
def prefixEnd_757138 : Nat := 4983230072969 + 3 ^ 40 * 757138 * 2
def baseEnd_757138 : Nat := 115192804676730052679405

theorem tailTrace_757138 : CollatzResearch.WordTrace tailWord_757138 prefixEnd_757138 115192804676730052679405 := by
  unfold tailWord_757138
  simp only [CollatzResearch.WordTrace]
  refine ⟨6903772882756452430176017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18410061020683873147136045 6903772882756452430176017)
  ·
    refine ⟨5177829662067339322632013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6903772882756452430176017 5177829662067339322632013)
    ·
      refine ⟨1941686123275252245987005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5177829662067339322632013 1941686123275252245987005)
      ·
        refine ⟨728132296228219592245127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1941686123275252245987005 728132296228219592245127)
        ·
          refine ⟨1092198444342329388367691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728132296228219592245127 1092198444342329388367691)
          ·
            refine ⟨1638297666513494082551537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092198444342329388367691 1638297666513494082551537)
            ·
              refine ⟨1228723249885120561913653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1638297666513494082551537 1228723249885120561913653)
              ·
                refine ⟨115192804676730052679405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1228723249885120561913653 115192804676730052679405)
                ·
                  rfl

theorem cell20_757138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_757138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757138 prefixEnd_757138 := by exact prefixLift 757138
  have htrace : WordTrace (prefixWord ++ tailWord_757138) baseStart_757138 baseEnd_757138 := by
    simpa [prefixWord, tailWord_757138, baseEnd_757138] using wordTrace_append hprefix tailTrace_757138
  have hstable : (prefixWord ++ tailWord_757138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757138).length < 2 ^ (prefixWord ++ tailWord_757138).sum := by decide
  have hdescent : baseEnd_757138 < baseStart_757138 := by decide
  rcases family_descends (prefixWord ++ tailWord_757138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757145 : List Nat := [1, 2, 1, 2, 1, 7, 2, 1, 3]
def baseStart_757145 : Nat := 118140960795 + 757145 * 2 ^ 59
def prefixEnd_757145 : Nat := 4983230072969 + 3 ^ 40 * 757145 * 2
def baseEnd_757145 : Nat := 345581609020929244804853

theorem tailTrace_757145 : CollatzResearch.WordTrace tailWord_757145 prefixEnd_757145 345581609020929244804853 := by
  unfold tailWord_757145
  simp only [CollatzResearch.WordTrace]
  refine ⟨27615346842000449916208889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18410231228000299944139259 27615346842000449916208889)
  ·
    refine ⟨20711510131500337437156667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27615346842000449916208889 20711510131500337437156667)
    ·
      refine ⟨31067265197250506155735001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20711510131500337437156667 31067265197250506155735001)
      ·
        refine ⟨23300448897937879616801251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31067265197250506155735001 23300448897937879616801251)
        ·
          refine ⟨34950673346906819425201877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23300448897937879616801251 34950673346906819425201877)
          ·
            refine ⟨819156406568128580278169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 34950673346906819425201877 819156406568128580278169)
            ·
              refine ⟨614367304926096435208627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819156406568128580278169 614367304926096435208627)
              ·
                refine ⟨921550957389144652812941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614367304926096435208627 921550957389144652812941)
                ·
                  refine ⟨345581609020929244804853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 921550957389144652812941 345581609020929244804853)
                  ·
                    rfl

theorem cell20_757145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_757145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757145 prefixEnd_757145 := by exact prefixLift 757145
  have htrace : WordTrace (prefixWord ++ tailWord_757145) baseStart_757145 baseEnd_757145 := by
    simpa [prefixWord, tailWord_757145, baseEnd_757145] using wordTrace_append hprefix tailTrace_757145
  have hstable : (prefixWord ++ tailWord_757145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757145).length < 2 ^ (prefixWord ++ tailWord_757145).sum := by decide
  have hdescent : baseEnd_757145 < baseStart_757145 := by decide
  rcases family_descends (prefixWord ++ tailWord_757145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757156 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_757156 : Nat := 118140960795 + 757156 * 2 ^ 59
def prefixEnd_757156 : Nat := 4983230072969 + 3 ^ 40 * 757156 * 2
def baseEnd_757156 : Nat := 345586629720662095438141

theorem tailTrace_757156 : CollatzResearch.WordTrace tailWord_757156 prefixEnd_757156 345586629720662095438141 := by
  unfold tailWord_757156
  simp only [CollatzResearch.WordTrace]
  refine ⟨13807874022480299397429661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18410498696640399196572881 13807874022480299397429661)
  ·
    refine ⟨5177952758430112274036123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13807874022480299397429661 5177952758430112274036123)
    ·
      refine ⟨7766929137645168411054185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5177952758430112274036123 7766929137645168411054185)
      ·
        refine ⟨5825196853233876308290639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7766929137645168411054185 5825196853233876308290639)
        ·
          refine ⟨8737795279850814462435959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5825196853233876308290639 8737795279850814462435959)
          ·
            refine ⟨13106692919776221693653939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8737795279850814462435959 13106692919776221693653939)
            ·
              refine ⟨19660039379664332540480909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13106692919776221693653939 19660039379664332540480909)
              ·
                refine ⟨7372514767374124702680341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19660039379664332540480909 7372514767374124702680341)
                ·
                  refine ⟨345586629720662095438141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7372514767374124702680341 345586629720662095438141)
                  ·
                    rfl

theorem cell20_757156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_757156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757156 prefixEnd_757156 := by exact prefixLift 757156
  have htrace : WordTrace (prefixWord ++ tailWord_757156) baseStart_757156 baseEnd_757156 := by
    simpa [prefixWord, tailWord_757156, baseEnd_757156] using wordTrace_append hprefix tailTrace_757156
  have hstable : (prefixWord ++ tailWord_757156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757156).length < 2 ^ (prefixWord ++ tailWord_757156).sum := by decide
  have hdescent : baseEnd_757156 < baseStart_757156 := by decide
  rcases family_descends (prefixWord ++ tailWord_757156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757180 : List Nat := [2, 2, 2, 4, 2, 8]
def baseStart_757180 : Nat := 118140960795 + 757180 * 2 ^ 59
def prefixEnd_757180 : Nat := 4983230072969 + 3 ^ 40 * 757180 * 2
def baseEnd_757180 : Nat := 12799910517578691801409

theorem tailTrace_757180 : CollatzResearch.WordTrace tailWord_757180 prefixEnd_757180 12799910517578691801409 := by
  unfold tailWord_757180
  simp only [CollatzResearch.WordTrace]
  refine ⟨13808311698436825446866497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18411082264582433929155329 13808311698436825446866497)
  ·
    refine ⟨10356233773827619085149873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13808311698436825446866497 10356233773827619085149873)
    ·
      refine ⟨7767175330370714313862405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10356233773827619085149873 7767175330370714313862405)
      ·
        refine ⟨1456345374444508933849201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7767175330370714313862405 1456345374444508933849201)
        ·
          refine ⟨1092259030833381700386901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1456345374444508933849201 1092259030833381700386901)
          ·
            refine ⟨12799910517578691801409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1092259030833381700386901 12799910517578691801409)
            ·
              rfl

theorem cell20_757180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 8].length) (baseStart_757180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757180 prefixEnd_757180 := by exact prefixLift 757180
  have htrace : WordTrace (prefixWord ++ tailWord_757180) baseStart_757180 baseEnd_757180 := by
    simpa [prefixWord, tailWord_757180, baseEnd_757180] using wordTrace_append hprefix tailTrace_757180
  have hstable : (prefixWord ++ tailWord_757180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757180).length < 2 ^ (prefixWord ++ tailWord_757180).sum := by decide
  have hdescent : baseEnd_757180 < baseStart_757180 := by decide
  rcases family_descends (prefixWord ++ tailWord_757180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757187 : List Nat := [1, 1, 1, 3, 1, 1, 5, 4, 3]
def baseStart_757187 : Nat := 118140960795 + 757187 * 2 ^ 59
def prefixEnd_757187 : Nat := 4983230072969 + 3 ^ 40 * 757187 * 2
def baseEnd_757187 : Nat := 345600778965363765404681

theorem tailTrace_757187 : CollatzResearch.WordTrace tailWord_757187 prefixEnd_757187 345600778965363765404681 := by
  unfold tailWord_757187
  simp only [CollatzResearch.WordTrace]
  refine ⟨27616878707848291089237815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18411252471898860726158543 27616878707848291089237815)
  ·
    refine ⟨41425318061772436633856723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27616878707848291089237815 41425318061772436633856723)
    ·
      refine ⟨62137977092658654950785085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41425318061772436633856723 62137977092658654950785085)
      ·
        refine ⟨23301741409746995606544407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62137977092658654950785085 23301741409746995606544407)
        ·
          refine ⟨34952612114620493409816611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23301741409746995606544407 34952612114620493409816611)
          ·
            refine ⟨52428918171930740114724917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34952612114620493409816611 52428918171930740114724917)
            ·
              refine ⟨4915211078618506885755461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52428918171930740114724917 4915211078618506885755461)
              ·
                refine ⟨921602077240970041079149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4915211078618506885755461 921602077240970041079149)
                ·
                  refine ⟨345600778965363765404681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 921602077240970041079149 345600778965363765404681)
                  ·
                    rfl

theorem cell20_757187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 3].length) (baseStart_757187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757187 prefixEnd_757187 := by exact prefixLift 757187
  have htrace : WordTrace (prefixWord ++ tailWord_757187) baseStart_757187 baseEnd_757187 := by
    simpa [prefixWord, tailWord_757187, baseEnd_757187] using wordTrace_append hprefix tailTrace_757187
  have hstable : (prefixWord ++ tailWord_757187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757187).length < 2 ^ (prefixWord ++ tailWord_757187).sum := by decide
  have hdescent : baseEnd_757187 < baseStart_757187 := by decide
  rcases family_descends (prefixWord ++ tailWord_757187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757259 : List Nat := [1, 1, 1, 1, 8, 1, 3, 1, 3]
def baseStart_757259 : Nat := 118140960795 + 757259 * 2 ^ 59
def prefixEnd_757259 : Nat := 4983230072969 + 3 ^ 40 * 757259 * 2
def baseEnd_757259 : Nat := 345633641727251515004387

theorem tailTrace_757259 : CollatzResearch.WordTrace tailWord_757259 prefixEnd_757259 345633641727251515004387 := by
  unfold tailWord_757259
  simp only [CollatzResearch.WordTrace]
  refine ⟨27619504763587447385858831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18413003175724964923905887 27619504763587447385858831)
  ·
    refine ⟨41429257145381171078788247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27619504763587447385858831 41429257145381171078788247)
    ·
      refine ⟨62143885718071756618182371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41429257145381171078788247 62143885718071756618182371)
      ·
        refine ⟨93215828577107634927273557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62143885718071756618182371 93215828577107634927273557)
        ·
          refine ⟨1092372991137980096803987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 93215828577107634927273557 1092372991137980096803987)
          ·
            refine ⟨1638559486706970145205981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092372991137980096803987 1638559486706970145205981)
            ·
              refine ⟨614459807515113804452243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1638559486706970145205981 614459807515113804452243)
              ·
                refine ⟨921689711272670706678365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614459807515113804452243 921689711272670706678365)
                ·
                  refine ⟨345633641727251515004387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 921689711272670706678365 345633641727251515004387)
                  ·
                    rfl

theorem cell20_757259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 3].length) (baseStart_757259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757259 prefixEnd_757259 := by exact prefixLift 757259
  have htrace : WordTrace (prefixWord ++ tailWord_757259) baseStart_757259 baseEnd_757259 := by
    simpa [prefixWord, tailWord_757259, baseEnd_757259] using wordTrace_append hprefix tailTrace_757259
  have hstable : (prefixWord ++ tailWord_757259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757259).length < 2 ^ (prefixWord ++ tailWord_757259).sum := by decide
  have hdescent : baseEnd_757259 < baseStart_757259 := by decide
  rcases family_descends (prefixWord ++ tailWord_757259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757283 : List Nat := [1, 1, 1, 4, 5, 2, 1, 3, 2]
def baseStart_757283 : Nat := 118140960795 + 757283 * 2 ^ 59
def prefixEnd_757283 : Nat := 4983230072969 + 3 ^ 40 * 757283 * 2
def baseEnd_757283 : Nat := 345644595981214098204289

theorem tailTrace_757283 : CollatzResearch.WordTrace tailWord_757283 prefixEnd_757283 345644595981214098204289 := by
  unfold tailWord_757283
  simp only [CollatzResearch.WordTrace]
  refine ⟨27620380115500499484732503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18413586743666999656488335 27620380115500499484732503)
  ·
    refine ⟨41430570173250749227098755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27620380115500499484732503 41430570173250749227098755)
    ·
      refine ⟨62145855259876123840648133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41430570173250749227098755 62145855259876123840648133)
      ·
        refine ⟨11652347861226773220121525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62145855259876123840648133 11652347861226773220121525)
        ·
          refine ⟨1092407611990009989386393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11652347861226773220121525 1092407611990009989386393)
          ·
            refine ⟨819305708992507492039795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1092407611990009989386393 819305708992507492039795)
            ·
              refine ⟨1228958563488761238059693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819305708992507492039795 1228958563488761238059693)
              ·
                refine ⟨460859461308285464272385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1228958563488761238059693 460859461308285464272385)
                ·
                  refine ⟨345644595981214098204289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460859461308285464272385 345644595981214098204289)
                  ·
                    rfl

theorem cell20_757283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 2].length) (baseStart_757283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757283 prefixEnd_757283 := by exact prefixLift 757283
  have htrace : WordTrace (prefixWord ++ tailWord_757283) baseStart_757283 baseEnd_757283 := by
    simpa [prefixWord, tailWord_757283, baseEnd_757283] using wordTrace_append hprefix tailTrace_757283
  have hstable : (prefixWord ++ tailWord_757283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757283).length < 2 ^ (prefixWord ++ tailWord_757283).sum := by decide
  have hdescent : baseEnd_757283 < baseStart_757283 := by decide
  rcases family_descends (prefixWord ++ tailWord_757283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757294 : List Nat := [4, 1, 3, 1, 2, 1, 8]
def baseStart_757294 : Nat := 118140960795 + 757294 * 2 ^ 59
def prefixEnd_757294 : Nat := 4983230072969 + 3 ^ 40 * 757294 * 2
def baseEnd_757294 : Nat := 38405512964549660981953

theorem tailTrace_757294 : CollatzResearch.WordTrace tailWord_757294 prefixEnd_757294 38405512964549660981953 := by
  unfold tailWord_757294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3452597664807581045422867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18413854212307098908921957 3452597664807581045422867)
  ·
    refine ⟨5178896497211371568134301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3452597664807581045422867 5178896497211371568134301)
    ·
      refine ⟨1942086186454264338050363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5178896497211371568134301 1942086186454264338050363)
      ·
        refine ⟨2913129279681396507075545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1942086186454264338050363 2913129279681396507075545)
        ·
          refine ⟨2184846959761047380306659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2913129279681396507075545 2184846959761047380306659)
          ·
            refine ⟨3277270439641571070459989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184846959761047380306659 3277270439641571070459989)
            ·
              refine ⟨38405512964549660981953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3277270439641571070459989 38405512964549660981953)
              ·
                rfl

theorem cell20_757294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 8].length) (baseStart_757294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757294 prefixEnd_757294 := by exact prefixLift 757294
  have htrace : WordTrace (prefixWord ++ tailWord_757294) baseStart_757294 baseEnd_757294 := by
    simpa [prefixWord, tailWord_757294, baseEnd_757294] using wordTrace_append hprefix tailTrace_757294
  have hstable : (prefixWord ++ tailWord_757294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757294).length < 2 ^ (prefixWord ++ tailWord_757294).sum := by decide
  have hdescent : baseEnd_757294 < baseStart_757294 := by decide
  rcases family_descends (prefixWord ++ tailWord_757294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757301 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 5]
def baseStart_757301 : Nat := 118140960795 + 757301 * 2 ^ 59
def prefixEnd_757301 : Nat := 4983230072969 + 3 ^ 40 * 757301 * 2
def baseEnd_757301 : Nat := 345652811671686035604215

theorem tailTrace_757301 : CollatzResearch.WordTrace tailWord_757301 prefixEnd_757301 345652811671686035604215 := by
  unfold tailWord_757301
  simp only [CollatzResearch.WordTrace]
  refine ⟨27621036629435288558887757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18414024419623525705925171 27621036629435288558887757)
  ·
    refine ⟨10357888736038233209582909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27621036629435288558887757 10357888736038233209582909)
    ·
      refine ⟨3884208276014337453593591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10357888736038233209582909 3884208276014337453593591)
      ·
        refine ⟨5826312414021506180390387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3884208276014337453593591 5826312414021506180390387)
        ·
          refine ⟨8739468621032259270585581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5826312414021506180390387 8739468621032259270585581)
          ·
            refine ⟨3277300732887097226469593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8739468621032259270585581 3277300732887097226469593)
            ·
              refine ⟨2457975549665322919852195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3277300732887097226469593 2457975549665322919852195)
              ·
                refine ⟨3686963324497984379778293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2457975549665322919852195 3686963324497984379778293)
                ·
                  refine ⟨345652811671686035604215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3686963324497984379778293 345652811671686035604215)
                  ·
                    rfl

theorem cell20_757301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_757301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757301 prefixEnd_757301 := by exact prefixLift 757301
  have htrace : WordTrace (prefixWord ++ tailWord_757301) baseStart_757301 baseEnd_757301 := by
    simpa [prefixWord, tailWord_757301, baseEnd_757301] using wordTrace_append hprefix tailTrace_757301
  have hstable : (prefixWord ++ tailWord_757301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757301).length < 2 ^ (prefixWord ++ tailWord_757301).sum := by decide
  have hdescent : baseEnd_757301 < baseStart_757301 := by decide
  rcases family_descends (prefixWord ++ tailWord_757301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757452 : List Nat := [2, 2, 1, 5, 3, 1, 1, 3, 2]
def baseStart_757452 : Nat := 118140960795 + 757452 * 2 ^ 59
def prefixEnd_757452 : Nat := 4983230072969 + 3 ^ 40 * 757452 * 2
def baseEnd_757452 : Nat := 345721732186200621570265

theorem tailTrace_757452 : CollatzResearch.WordTrace tailWord_757452 prefixEnd_757452 345721732186200621570265 := by
  unfold tailWord_757452
  simp only [CollatzResearch.WordTrace]
  refine ⟨13813272025944120673817305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18417696034592160898423073 13813272025944120673817305)
  ·
    refine ⟨10359954019458090505362979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13813272025944120673817305 10359954019458090505362979)
    ·
      refine ⟨15539931029187135758044469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10359954019458090505362979 15539931029187135758044469)
      ·
        refine ⟨1456868533986293977316669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15539931029187135758044469 1456868533986293977316669)
        ·
          refine ⟨546325700244860241493751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1456868533986293977316669 546325700244860241493751)
          ·
            refine ⟨819488550367290362240627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546325700244860241493751 819488550367290362240627)
            ·
              refine ⟨1229232825550935543360941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819488550367290362240627 1229232825550935543360941)
              ·
                refine ⟨460962309581600828760353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1229232825550935543360941 460962309581600828760353)
                ·
                  refine ⟨345721732186200621570265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460962309581600828760353 345721732186200621570265)
                  ·
                    rfl

theorem cell20_757452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_757452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757452 prefixEnd_757452 := by exact prefixLift 757452
  have htrace : WordTrace (prefixWord ++ tailWord_757452) baseStart_757452 baseEnd_757452 := by
    simpa [prefixWord, tailWord_757452, baseEnd_757452] using wordTrace_append hprefix tailTrace_757452
  have hstable : (prefixWord ++ tailWord_757452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757452).length < 2 ^ (prefixWord ++ tailWord_757452).sum := by decide
  have hdescent : baseEnd_757452 < baseStart_757452 := by decide
  rcases family_descends (prefixWord ++ tailWord_757452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757473 : List Nat := [1, 2, 3, 1, 5, 1, 3, 2, 2]
def baseStart_757473 : Nat := 118140960795 + 757473 * 2 ^ 59
def prefixEnd_757473 : Nat := 4983230072969 + 3 ^ 40 * 757473 * 2
def baseEnd_757473 : Nat := 345731317158417881870179

theorem tailTrace_757473 : CollatzResearch.WordTrace tailWord_757473 prefixEnd_757473 345731317158417881870179 := by
  unfold tailWord_757473
  simp only [CollatzResearch.WordTrace]
  refine ⟨27627309984812161934149073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18418206656541441289432715 27627309984812161934149073)
  ·
    refine ⟨20720482488609121450611805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27627309984812161934149073 20720482488609121450611805)
    ·
      refine ⟨7770180933228420543979427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20720482488609121450611805 7770180933228420543979427)
      ·
        refine ⟨11655271399842630815969141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7770180933228420543979427 11655271399842630815969141)
        ·
          refine ⟨1092681693735246638997107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11655271399842630815969141 1092681693735246638997107)
          ·
            refine ⟨1639022540602869958495661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092681693735246638997107 1639022540602869958495661)
            ·
              refine ⟨614633452726076234435873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1639022540602869958495661 614633452726076234435873)
              ·
                refine ⟨460975089544557175826905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 614633452726076234435873 460975089544557175826905)
                ·
                  refine ⟨345731317158417881870179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460975089544557175826905 345731317158417881870179)
                  ·
                    rfl

theorem cell20_757473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 2].length) (baseStart_757473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757473 prefixEnd_757473 := by exact prefixLift 757473
  have htrace : WordTrace (prefixWord ++ tailWord_757473) baseStart_757473 baseEnd_757473 := by
    simpa [prefixWord, tailWord_757473, baseEnd_757473] using wordTrace_append hprefix tailTrace_757473
  have hstable : (prefixWord ++ tailWord_757473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757473).length < 2 ^ (prefixWord ++ tailWord_757473).sum := by decide
  have hdescent : baseEnd_757473 < baseStart_757473 := by decide
  rcases family_descends (prefixWord ++ tailWord_757473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757505 : List Nat := [1, 2, 4, 1, 1, 1, 4, 6]
def baseStart_757505 : Nat := 118140960795 + 757505 * 2 ^ 59
def prefixEnd_757505 : Nat := 4983230072969 + 3 ^ 40 * 757505 * 2
def baseEnd_757505 : Nat := 115248640943455997601127

theorem tailTrace_757505 : CollatzResearch.WordTrace tailWord_757505 prefixEnd_757505 115248640943455997601127 := by
  unfold tailWord_757505
  simp only [CollatzResearch.WordTrace]
  refine ⟨27628477120696231399313969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18418984747130820932875979 27628477120696231399313969)
  ·
    refine ⟨20721357840522173549485477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27628477120696231399313969 20721357840522173549485477)
    ·
      refine ⟨3885254595097907540528527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20721357840522173549485477 3885254595097907540528527)
      ·
        refine ⟨5827881892646861310792791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3885254595097907540528527 5827881892646861310792791)
        ·
          refine ⟨8741822838970291966189187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5827881892646861310792791 8741822838970291966189187)
          ·
            refine ⟨13112734258455437949283781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8741822838970291966189187 13112734258455437949283781)
            ·
              refine ⟨2458637673460394615490709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13112734258455437949283781 2458637673460394615490709)
              ·
                refine ⟨115248640943455997601127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2458637673460394615490709 115248640943455997601127)
                ·
                  rfl

theorem cell20_757505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 6].length) (baseStart_757505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757505 prefixEnd_757505 := by exact prefixLift 757505
  have htrace : WordTrace (prefixWord ++ tailWord_757505) baseStart_757505 baseEnd_757505 := by
    simpa [prefixWord, tailWord_757505, baseEnd_757505] using wordTrace_append hprefix tailTrace_757505
  have hstable : (prefixWord ++ tailWord_757505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757505).length < 2 ^ (prefixWord ++ tailWord_757505).sum := by decide
  have hdescent : baseEnd_757505 < baseStart_757505 := by decide
  rcases family_descends (prefixWord ++ tailWord_757505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757519 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 8]
def baseStart_757519 : Nat := 118140960795 + 757519 * 2 ^ 59
def prefixEnd_757519 : Nat := 4983230072969 + 3 ^ 40 * 757519 * 2
def baseEnd_757519 : Nat := 345752312811846166336657

theorem tailTrace_757519 : CollatzResearch.WordTrace tailWord_757519 prefixEnd_757519 345752312811846166336657 := by
  unfold tailWord_757519
  simp only [CollatzResearch.WordTrace]
  refine ⟨27628987742645511790323611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18419325161763674526882407 27628987742645511790323611)
  ·
    refine ⟨41443481613968267685485417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27628987742645511790323611 41443481613968267685485417)
    ·
      refine ⟨31082611210476200764114063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41443481613968267685485417 31082611210476200764114063)
      ·
        refine ⟨46623916815714301146171095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31082611210476200764114063 46623916815714301146171095)
        ·
          refine ⟨69935875223571451719256643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46623916815714301146171095 69935875223571451719256643)
          ·
            refine ⟨104903812835357177578884965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69935875223571451719256643 104903812835357177578884965)
            ·
              refine ⟨19669464906629470796040931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104903812835357177578884965 19669464906629470796040931)
              ·
                refine ⟨29504197359944206194061397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19669464906629470796040931 29504197359944206194061397)
                ·
                  refine ⟨345752312811846166336657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29504197359944206194061397 345752312811846166336657)
                  ·
                    rfl

theorem cell20_757519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_757519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757519 prefixEnd_757519 := by exact prefixLift 757519
  have htrace : WordTrace (prefixWord ++ tailWord_757519) baseStart_757519 baseEnd_757519 := by
    simpa [prefixWord, tailWord_757519, baseEnd_757519] using wordTrace_append hprefix tailTrace_757519
  have hstable : (prefixWord ++ tailWord_757519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757519).length < 2 ^ (prefixWord ++ tailWord_757519).sum := by decide
  have hdescent : baseEnd_757519 < baseStart_757519 := by decide
  rcases family_descends (prefixWord ++ tailWord_757519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757522 : List Nat := [3, 2, 4, 1, 1, 9]
def baseStart_757522 : Nat := 118140960795 + 757522 * 2 ^ 59
def prefixEnd_757522 : Nat := 4983230072969 + 3 ^ 40 * 757522 * 2
def baseEnd_757522 : Nat := 12805691929392277379135

theorem tailTrace_757522 : CollatzResearch.WordTrace tailWord_757522 prefixEnd_757522 12805691929392277379135 := by
  unfold tailWord_757522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6907274290408660825670705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18419398107756428868455213 6907274290408660825670705)
  ·
    refine ⟨5180455717806495619253029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6907274290408660825670705 5180455717806495619253029)
    ·
      refine ⟨971335447088717928609943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5180455717806495619253029 971335447088717928609943)
      ·
        refine ⟨1457003170633076892914915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 971335447088717928609943 1457003170633076892914915)
        ·
          refine ⟨2185504755949615339372373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457003170633076892914915 2185504755949615339372373)
          ·
            refine ⟨12805691929392277379135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2185504755949615339372373 12805691929392277379135)
            ·
              rfl

theorem cell20_757522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 9].length) (baseStart_757522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757522 prefixEnd_757522 := by exact prefixLift 757522
  have htrace : WordTrace (prefixWord ++ tailWord_757522) baseStart_757522 baseEnd_757522 := by
    simpa [prefixWord, tailWord_757522, baseEnd_757522] using wordTrace_append hprefix tailTrace_757522
  have hstable : (prefixWord ++ tailWord_757522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757522).length < 2 ^ (prefixWord ++ tailWord_757522).sum := by decide
  have hdescent : baseEnd_757522 < baseStart_757522 := by decide
  rcases family_descends (prefixWord ++ tailWord_757522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757524 : List Nat := [2, 4, 4, 1, 1, 2, 2, 2, 2]
def baseStart_757524 : Nat := 118140960795 + 757524 * 2 ^ 59
def prefixEnd_757524 : Nat := 4983230072969 + 3 ^ 40 * 757524 * 2
def baseEnd_757524 : Nat := 345754594948088371169971

theorem tailTrace_757524 : CollatzResearch.WordTrace tailWord_757524 prefixEnd_757524 345754594948088371169971 := by
  unfold tailWord_757524
  simp only [CollatzResearch.WordTrace]
  refine ⟨13814585053813698822127813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18419446738418265096170417 13814585053813698822127813)
  ·
    refine ⟨2590234697590068529148965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13814585053813698822127813 2590234697590068529148965)
    ·
      refine ⟨485669005798137849215431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2590234697590068529148965 485669005798137849215431)
      ·
        refine ⟨728503508697206773823147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485669005798137849215431 728503508697206773823147)
        ·
          refine ⟨1092755263045810160734721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728503508697206773823147 1092755263045810160734721)
          ·
            refine ⟨819566447284357620551041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1092755263045810160734721 819566447284357620551041)
            ·
              refine ⟨614674835463268215413281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819566447284357620551041 614674835463268215413281)
              ·
                refine ⟨461006126597451161559961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 614674835463268215413281 461006126597451161559961)
                ·
                  refine ⟨345754594948088371169971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461006126597451161559961 345754594948088371169971)
                  ·
                    rfl

theorem cell20_757524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_757524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757524 prefixEnd_757524 := by exact prefixLift 757524
  have htrace : WordTrace (prefixWord ++ tailWord_757524) baseStart_757524 baseEnd_757524 := by
    simpa [prefixWord, tailWord_757524, baseEnd_757524] using wordTrace_append hprefix tailTrace_757524
  have hstable : (prefixWord ++ tailWord_757524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757524).length < 2 ^ (prefixWord ++ tailWord_757524).sum := by decide
  have hdescent : baseEnd_757524 < baseStart_757524 := by decide
  rcases family_descends (prefixWord ++ tailWord_757524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757536 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 4]
def baseStart_757536 : Nat := 118140960795 + 757536 * 2 ^ 59
def prefixEnd_757536 : Nat := 4983230072969 + 3 ^ 40 * 757536 * 2
def baseEnd_757536 : Nat := 345760072075069662769921

theorem tailTrace_757536 : CollatzResearch.WordTrace tailWord_757536 prefixEnd_757536 345760072075069662769921 := by
  unfold tailWord_757536
  simp only [CollatzResearch.WordTrace]
  refine ⟨13814803891791961846846231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18419738522389282462461641 13814803891791961846846231)
  ·
    refine ⟨20722205837687942770269347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13814803891791961846846231 20722205837687942770269347)
    ·
      refine ⟨31083308756531914155404021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20722205837687942770269347 31083308756531914155404021)
      ·
        refine ⟨2914060195924866952069127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31083308756531914155404021 2914060195924866952069127)
        ·
          refine ⟨4371090293887300428103691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2914060195924866952069127 4371090293887300428103691)
          ·
            refine ⟨6556635440830950642155537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4371090293887300428103691 6556635440830950642155537)
            ·
              refine ⟨4917476580623212981616653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6556635440830950642155537 4917476580623212981616653)
              ·
                refine ⟨1844053717733704868106245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4917476580623212981616653 1844053717733704868106245)
                ·
                  refine ⟨345760072075069662769921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1844053717733704868106245 345760072075069662769921)
                  ·
                    rfl

theorem cell20_757536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_757536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757536 prefixEnd_757536 := by exact prefixLift 757536
  have htrace : WordTrace (prefixWord ++ tailWord_757536) baseStart_757536 baseEnd_757536 := by
    simpa [prefixWord, tailWord_757536, baseEnd_757536] using wordTrace_append hprefix tailTrace_757536
  have hstable : (prefixWord ++ tailWord_757536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757536).length < 2 ^ (prefixWord ++ tailWord_757536).sum := by decide
  have hdescent : baseEnd_757536 < baseStart_757536 := by decide
  rcases family_descends (prefixWord ++ tailWord_757536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757560 : List Nat := [2, 1, 2, 1, 3, 4, 3, 4]
def baseStart_757560 : Nat := 118140960795 + 757560 * 2 ^ 59
def prefixEnd_757560 : Nat := 4983230072969 + 3 ^ 40 * 757560 * 2
def baseEnd_757560 : Nat := 115257008776344081989941

theorem tailTrace_757560 : CollatzResearch.WordTrace tailWord_757560 prefixEnd_757560 115257008776344081989941 := by
  unfold tailWord_757560
  simp only [CollatzResearch.WordTrace]
  refine ⟨13815241567748487896283067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18420322090331317195044089 13815241567748487896283067)
  ·
    refine ⟨20722862351622731844424601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13815241567748487896283067 20722862351622731844424601)
    ·
      refine ⟨15542146763717048883318451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20722862351622731844424601 15542146763717048883318451)
      ·
        refine ⟨23313220145575573324977677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15542146763717048883318451 23313220145575573324977677)
        ·
          refine ⟨8742457554590839996866629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23313220145575573324977677 8742457554590839996866629)
          ·
            refine ⟨1639210791485782499412493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8742457554590839996866629 1639210791485782499412493)
            ·
              refine ⟨614704046807168437279685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1639210791485782499412493 614704046807168437279685)
              ·
                refine ⟨115257008776344081989941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 614704046807168437279685 115257008776344081989941)
                ·
                  rfl

theorem cell20_757560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_757560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757560 prefixEnd_757560 := by exact prefixLift 757560
  have htrace : WordTrace (prefixWord ++ tailWord_757560) baseStart_757560 baseEnd_757560 := by
    simpa [prefixWord, tailWord_757560, baseEnd_757560] using wordTrace_append hprefix tailTrace_757560
  have hstable : (prefixWord ++ tailWord_757560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757560).length < 2 ^ (prefixWord ++ tailWord_757560).sum := by decide
  have hdescent : baseEnd_757560 < baseStart_757560 := by decide
  rcases family_descends (prefixWord ++ tailWord_757560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757591 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 4]
def baseStart_757591 : Nat := 118140960795 + 757591 * 2 ^ 59
def prefixEnd_757591 : Nat := 4983230072969 + 3 ^ 40 * 757591 * 2
def baseEnd_757591 : Nat := 345785175573733915936363

theorem tailTrace_757591 : CollatzResearch.WordTrace tailWord_757591 prefixEnd_757591 345785175573733915936363 := by
  unfold tailWord_757591
  simp only [CollatzResearch.WordTrace]
  refine ⟨27631613798384668086944627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18421075865589778724629751 27631613798384668086944627)
  ·
    refine ⟨41447420697577002130416941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27631613798384668086944627 41447420697577002130416941)
    ·
      refine ⟨15542782761591375798906353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41447420697577002130416941 15542782761591375798906353)
      ·
        refine ⟨11657087071193531849179765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15542782761591375798906353 11657087071193531849179765)
        ·
          refine ⟨1092851912924393610860603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11657087071193531849179765 1092851912924393610860603)
          ·
            refine ⟨1639277869386590416290905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092851912924393610860603 1639277869386590416290905)
            ·
              refine ⟨1229458402039942812218179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1639277869386590416290905 1229458402039942812218179)
              ·
                refine ⟨1844187603059914218327269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229458402039942812218179 1844187603059914218327269)
                ·
                  refine ⟨345785175573733915936363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1844187603059914218327269 345785175573733915936363)
                  ·
                    rfl

theorem cell20_757591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 4].length) (baseStart_757591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757591 prefixEnd_757591 := by exact prefixLift 757591
  have htrace : WordTrace (prefixWord ++ tailWord_757591) baseStart_757591 baseEnd_757591 := by
    simpa [prefixWord, tailWord_757591, baseEnd_757591] using wordTrace_append hprefix tailTrace_757591
  have hstable : (prefixWord ++ tailWord_757591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757591).length < 2 ^ (prefixWord ++ tailWord_757591).sum := by decide
  have hdescent : baseEnd_757591 < baseStart_757591 := by decide
  rcases family_descends (prefixWord ++ tailWord_757591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757612 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 4]
def baseStart_757612 : Nat := 118140960795 + 757612 * 2 ^ 59
def prefixEnd_757612 : Nat := 4983230072969 + 3 ^ 40 * 757612 * 2
def baseEnd_757612 : Nat := 345794760545951176236277

theorem tailTrace_757612 : CollatzResearch.WordTrace tailWord_757612 prefixEnd_757612 345794760545951176236277 := by
  unfold tailWord_757612
  simp only [CollatzResearch.WordTrace]
  refine ⟨13816189865654294336729545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18421586487539059115639393 13816189865654294336729545)
  ·
    refine ⟨10362142399240720752547159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13816189865654294336729545 10362142399240720752547159)
    ·
      refine ⟨15543213598861081128820739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10362142399240720752547159 15543213598861081128820739)
      ·
        refine ⟨23314820398291621693231109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15543213598861081128820739 23314820398291621693231109)
        ·
          refine ⟨4371528824679679067480833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23314820398291621693231109 4371528824679679067480833)
          ·
            refine ⟨3278646618509759300610625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4371528824679679067480833 3278646618509759300610625)
            ·
              refine ⟨2458984963882319475457969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3278646618509759300610625 2458984963882319475457969)
              ·
                refine ⟨1844238722911739606593477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2458984963882319475457969 1844238722911739606593477)
                ·
                  refine ⟨345794760545951176236277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1844238722911739606593477 345794760545951176236277)
                  ·
                    rfl

theorem cell20_757612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_757612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757612 prefixEnd_757612 := by exact prefixLift 757612
  have htrace : WordTrace (prefixWord ++ tailWord_757612) baseStart_757612 baseEnd_757612 := by
    simpa [prefixWord, tailWord_757612, baseEnd_757612] using wordTrace_append hprefix tailTrace_757612
  have hstable : (prefixWord ++ tailWord_757612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757612).length < 2 ^ (prefixWord ++ tailWord_757612).sum := by decide
  have hdescent : baseEnd_757612 < baseStart_757612 := by decide
  rcases family_descends (prefixWord ++ tailWord_757612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757626 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_757626 : Nat := 118140960795 + 757626 * 2 ^ 59
def prefixEnd_757626 : Nat := 4983230072969 + 3 ^ 40 * 757626 * 2
def baseEnd_757626 : Nat := 345801150527429349769553

theorem tailTrace_757626 : CollatzResearch.WordTrace tailWord_757626 prefixEnd_757626 345801150527429349769553 := by
  unfold tailWord_757626
  simp only [CollatzResearch.WordTrace]
  refine ⟨6908222588314467266117183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18421926902171912709645821 6908222588314467266117183)
  ·
    refine ⟨10362333882471700899175775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6908222588314467266117183 10362333882471700899175775)
    ·
      refine ⟨15543500823707551348763663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10362333882471700899175775 15543500823707551348763663)
      ·
        refine ⟨23315251235561327023145495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15543500823707551348763663 23315251235561327023145495)
        ·
          refine ⟨34972876853341990534718243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23315251235561327023145495 34972876853341990534718243)
          ·
            refine ⟨52459315280012985802077365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34972876853341990534718243 52459315280012985802077365)
            ·
              refine ⟨4918060807501217418944753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52459315280012985802077365 4918060807501217418944753)
              ·
                refine ⟨3688545605625913064208565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4918060807501217418944753 3688545605625913064208565)
                ·
                  refine ⟨345801150527429349769553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3688545605625913064208565 345801150527429349769553)
                  ·
                    rfl

theorem cell20_757626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_757626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757626 prefixEnd_757626 := by exact prefixLift 757626
  have htrace : WordTrace (prefixWord ++ tailWord_757626) baseStart_757626 baseEnd_757626 := by
    simpa [prefixWord, tailWord_757626, baseEnd_757626] using wordTrace_append hprefix tailTrace_757626
  have hstable : (prefixWord ++ tailWord_757626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757626).length < 2 ^ (prefixWord ++ tailWord_757626).sum := by decide
  have hdescent : baseEnd_757626 < baseStart_757626 := by decide
  rcases family_descends (prefixWord ++ tailWord_757626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757656 : List Nat := [2, 1, 2, 6, 1, 2, 2, 1, 3]
def baseStart_757656 : Nat := 118140960795 + 757656 * 2 ^ 59
def prefixEnd_757656 : Nat := 4983230072969 + 3 ^ 40 * 757656 * 2
def baseEnd_757656 : Nat := 345814843344882578769431

theorem tailTrace_757656 : CollatzResearch.WordTrace tailWord_757656 prefixEnd_757656 345814843344882578769431 := by
  unfold tailWord_757656
  simp only [CollatzResearch.WordTrace]
  refine ⟨13816992271574592094030411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18422656362099456125373881 13816992271574592094030411)
  ·
    refine ⟨20725488407361888141045617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13816992271574592094030411 20725488407361888141045617)
    ·
      refine ⟨15544116305521416105784213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20725488407361888141045617 15544116305521416105784213)
      ·
        refine ⟨728630451821316379958635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15544116305521416105784213 728630451821316379958635)
        ·
          refine ⟨1092945677731974569937953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728630451821316379958635 1092945677731974569937953)
          ·
            refine ⟨819709258298980927453465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1092945677731974569937953 819709258298980927453465)
            ·
              refine ⟨614781943724235695590099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819709258298980927453465 614781943724235695590099)
              ·
                refine ⟨922172915586353543385149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614781943724235695590099 922172915586353543385149)
                ·
                  refine ⟨345814843344882578769431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 922172915586353543385149 345814843344882578769431)
                  ·
                    rfl

theorem cell20_757656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_757656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757656 prefixEnd_757656 := by exact prefixLift 757656
  have htrace : WordTrace (prefixWord ++ tailWord_757656) baseStart_757656 baseEnd_757656 := by
    simpa [prefixWord, tailWord_757656, baseEnd_757656] using wordTrace_append hprefix tailTrace_757656
  have hstable : (prefixWord ++ tailWord_757656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757656).length < 2 ^ (prefixWord ++ tailWord_757656).sum := by decide
  have hdescent : baseEnd_757656 < baseStart_757656 := by decide
  rcases family_descends (prefixWord ++ tailWord_757656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757660 : List Nat := [2, 2, 3, 3, 1, 2, 1, 3, 3]
def baseStart_757660 : Nat := 118140960795 + 757660 * 2 ^ 59
def prefixEnd_757660 : Nat := 4983230072969 + 3 ^ 40 * 757660 * 2
def baseEnd_757660 : Nat := 345816669053876342636081

theorem tailTrace_757660 : CollatzResearch.WordTrace tailWord_757660 prefixEnd_757660 345816669053876342636081 := by
  unfold tailWord_757660
  simp only [CollatzResearch.WordTrace]
  refine ⟨13817065217567346435603217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18422753623423128580804289 13817065217567346435603217)
  ·
    refine ⟨10362798913175509826702413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13817065217567346435603217 10362798913175509826702413)
    ·
      refine ⟨3886049592440816185013405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10362798913175509826702413 3886049592440816185013405)
      ·
        refine ⟨1457268597165306069380027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3886049592440816185013405 1457268597165306069380027)
        ·
          refine ⟨2185902895747959104070041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457268597165306069380027 2185902895747959104070041)
          ·
            refine ⟨1639427171810969328052531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2185902895747959104070041 1639427171810969328052531)
            ·
              refine ⟨2459140757716453992078797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1639427171810969328052531 2459140757716453992078797)
              ·
                refine ⟨922177784143670247029549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2459140757716453992078797 922177784143670247029549)
                ·
                  refine ⟨345816669053876342636081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 922177784143670247029549 345816669053876342636081)
                  ·
                    rfl

theorem cell20_757660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_757660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757660 prefixEnd_757660 := by exact prefixLift 757660
  have htrace : WordTrace (prefixWord ++ tailWord_757660) baseStart_757660 baseEnd_757660 := by
    simpa [prefixWord, tailWord_757660, baseEnd_757660] using wordTrace_append hprefix tailTrace_757660
  have hstable : (prefixWord ++ tailWord_757660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757660).length < 2 ^ (prefixWord ++ tailWord_757660).sum := by decide
  have hdescent : baseEnd_757660 < baseStart_757660 := by decide
  rcases family_descends (prefixWord ++ tailWord_757660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757743 : List Nat := [1, 1, 2, 1, 4, 2, 4, 3, 2]
def baseStart_757743 : Nat := 118140960795 + 757743 * 2 ^ 59
def prefixEnd_757743 : Nat := 4983230072969 + 3 ^ 40 * 757743 * 2
def baseEnd_757743 : Nat := 345854552515496942869075

theorem tailTrace_757743 : CollatzResearch.WordTrace tailWord_757743 prefixEnd_757743 345854552515496942869075 := by
  unfold tailWord_757743
  simp only [CollatzResearch.WordTrace]
  refine ⟨27637157693833998046477883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18424771795889332030985255 27637157693833998046477883)
  ·
    refine ⟨41455736540750997069716825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27637157693833998046477883 41455736540750997069716825)
    ·
      refine ⟨31091802405563247802287619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41455736540750997069716825 31091802405563247802287619)
      ·
        refine ⟨46637703608344871703431429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31091802405563247802287619 46637703608344871703431429)
        ·
          refine ⟨8744569426564663444393393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46637703608344871703431429 8744569426564663444393393)
          ·
            refine ⟨6558427069923497583295045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8744569426564663444393393 6558427069923497583295045)
            ·
              refine ⟨1229705075610655796867821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6558427069923497583295045 1229705075610655796867821)
              ·
                refine ⟨461139403353995923825433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1229705075610655796867821 461139403353995923825433)
                ·
                  refine ⟨345854552515496942869075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461139403353995923825433 345854552515496942869075)
                  ·
                    rfl

theorem cell20_757743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 2].length) (baseStart_757743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757743 prefixEnd_757743 := by exact prefixLift 757743
  have htrace : WordTrace (prefixWord ++ tailWord_757743) baseStart_757743 baseEnd_757743 := by
    simpa [prefixWord, tailWord_757743, baseEnd_757743] using wordTrace_append hprefix tailTrace_757743
  have hstable : (prefixWord ++ tailWord_757743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757743).length < 2 ^ (prefixWord ++ tailWord_757743).sum := by decide
  have hdescent : baseEnd_757743 < baseStart_757743 := by decide
  rcases family_descends (prefixWord ++ tailWord_757743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757750 : List Nat := [5, 1, 1, 1, 4, 1, 7]
def baseStart_757750 : Nat := 118140960795 + 757750 * 2 ^ 59
def prefixEnd_757750 : Nat := 4983230072969 + 3 ^ 40 * 757750 * 2
def baseEnd_757750 : Nat := 38428638611804003292857

theorem tailTrace_757750 : CollatzResearch.WordTrace tailWord_757750 prefixEnd_757750 38428638611804003292857 := by
  unfold tailWord_757750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1727338312800539890123919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18424942003205758827988469 1727338312800539890123919)
  ·
    refine ⟨2591007469200809835185879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1727338312800539890123919 2591007469200809835185879)
    ·
      refine ⟨3886511203801214752778819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2591007469200809835185879 3886511203801214752778819)
      ·
        refine ⟨5829766805701822129168229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3886511203801214752778819 5829766805701822129168229)
        ·
          refine ⟨1093081276069091649219043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5829766805701822129168229 1093081276069091649219043)
          ·
            refine ⟨1639621914103637473828565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093081276069091649219043 1639621914103637473828565)
            ·
              refine ⟨38428638611804003292857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1639621914103637473828565 38428638611804003292857)
              ·
                rfl

theorem cell20_757750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 7].length) (baseStart_757750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757750 prefixEnd_757750 := by exact prefixLift 757750
  have htrace : WordTrace (prefixWord ++ tailWord_757750) baseStart_757750 baseEnd_757750 := by
    simpa [prefixWord, tailWord_757750, baseEnd_757750] using wordTrace_append hprefix tailTrace_757750
  have hstable : (prefixWord ++ tailWord_757750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757750).length < 2 ^ (prefixWord ++ tailWord_757750).sum := by decide
  have hdescent : baseEnd_757750 < baseStart_757750 := by decide
  rcases family_descends (prefixWord ++ tailWord_757750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757757 : List Nat := [1, 4, 1, 1, 1, 2, 5, 2, 3]
def baseStart_757757 : Nat := 118140960795 + 757757 * 2 ^ 59
def prefixEnd_757757 : Nat := 4983230072969 + 3 ^ 40 * 757757 * 2
def baseEnd_757757 : Nat := 345860942496975116402351

theorem tailTrace_757757 : CollatzResearch.WordTrace tailWord_757757 prefixEnd_757757 345860942496975116402351 := by
  unfold tailWord_757757
  simp only [CollatzResearch.WordTrace]
  refine ⟨27637668315783278437487525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18425112210522185624991683 27637668315783278437487525)
  ·
    refine ⟨5182062809209364707028911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27637668315783278437487525 5182062809209364707028911)
    ·
      refine ⟨7773094213814047060543367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5182062809209364707028911 7773094213814047060543367)
      ·
        refine ⟨11659641320721070590815051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7773094213814047060543367 11659641320721070590815051)
        ·
          refine ⟨17489461981081605886222577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11659641320721070590815051 17489461981081605886222577)
          ·
            refine ⟨13117096485811204414666933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17489461981081605886222577 13117096485811204414666933)
            ·
              refine ⟨1229727795544800413875025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13117096485811204414666933 1229727795544800413875025)
              ·
                refine ⟨922295846658600310406269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1229727795544800413875025 922295846658600310406269)
                ·
                  refine ⟨345860942496975116402351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 922295846658600310406269 345860942496975116402351)
                  ·
                    rfl

theorem cell20_757757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_757757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757757 prefixEnd_757757 := by exact prefixLift 757757
  have htrace : WordTrace (prefixWord ++ tailWord_757757) baseStart_757757 baseEnd_757757 := by
    simpa [prefixWord, tailWord_757757, baseEnd_757757] using wordTrace_append hprefix tailTrace_757757
  have hstable : (prefixWord ++ tailWord_757757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757757).length < 2 ^ (prefixWord ++ tailWord_757757).sum := by decide
  have hdescent : baseEnd_757757 < baseStart_757757 := by decide
  rcases family_descends (prefixWord ++ tailWord_757757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757766 : List Nat := [6, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_757766 : Nat := 118140960795 + 757766 * 2 ^ 59
def prefixEnd_757766 : Nat := 4983230072969 + 3 ^ 40 * 757766 * 2
def baseEnd_757766 : Nat := 345865050342211085102315

theorem tailTrace_757766 : CollatzResearch.WordTrace tailWord_757766 prefixEnd_757766 345865050342211085102315 := by
  unfold tailWord_757766
  simp only [CollatzResearch.WordTrace]
  refine ⟨863687392898458530455161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18425331048500448649710101 863687392898458530455161)
  ·
    refine ⟨647765544673843897841371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 863687392898458530455161 647765544673843897841371)
    ·
      refine ⟨971648317010765846762057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 647765544673843897841371 971648317010765846762057)
      ·
        refine ⟨728736237758074385071543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 971648317010765846762057 728736237758074385071543)
        ·
          refine ⟨1093104356637111577607315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728736237758074385071543 1093104356637111577607315)
          ·
            refine ⟨1639656534955667366410973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093104356637111577607315 1639656534955667366410973)
            ·
              refine ⟨614871200608375262404115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1639656534955667366410973 614871200608375262404115)
              ·
                refine ⟨922306800912562893606173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614871200608375262404115 922306800912562893606173)
                ·
                  refine ⟨345865050342211085102315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 922306800912562893606173 345865050342211085102315)
                  ·
                    rfl

theorem cell20_757766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_757766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757766 prefixEnd_757766 := by exact prefixLift 757766
  have htrace : WordTrace (prefixWord ++ tailWord_757766) baseStart_757766 baseEnd_757766 := by
    simpa [prefixWord, tailWord_757766, baseEnd_757766] using wordTrace_append hprefix tailTrace_757766
  have hstable : (prefixWord ++ tailWord_757766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757766).length < 2 ^ (prefixWord ++ tailWord_757766).sum := by decide
  have hdescent : baseEnd_757766 < baseStart_757766 := by decide
  rcases family_descends (prefixWord ++ tailWord_757766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757774 : List Nat := [4, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_757774 : Nat := 118140960795 + 757774 * 2 ^ 59
def prefixEnd_757774 : Nat := 4983230072969 + 3 ^ 40 * 757774 * 2
def baseEnd_757774 : Nat := 345868701760198612835615

theorem tailTrace_757774 : CollatzResearch.WordTrace tailWord_757774 prefixEnd_757774 345868701760198612835615 := by
  unfold tailWord_757774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3454786044590211292607047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18425525571147793560570917 3454786044590211292607047)
  ·
    refine ⟨5182179066885316938910571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3454786044590211292607047 5182179066885316938910571)
    ·
      refine ⟨7773268600327975408365857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5182179066885316938910571 7773268600327975408365857)
      ·
        refine ⟨5829951450245981556274393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7773268600327975408365857 5829951450245981556274393)
        ·
          refine ⟨4372463587684486167205795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5829951450245981556274393 4372463587684486167205795)
          ·
            refine ⟨6558695381526729250808693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4372463587684486167205795 6558695381526729250808693)
            ·
              refine ⟨614877692018130867263315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6558695381526729250808693 614877692018130867263315)
              ·
                refine ⟨922316538027196300894973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614877692018130867263315 922316538027196300894973)
                ·
                  refine ⟨345868701760198612835615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 922316538027196300894973 345868701760198612835615)
                  ·
                    rfl

theorem cell20_757774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_757774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757774 prefixEnd_757774 := by exact prefixLift 757774
  have htrace : WordTrace (prefixWord ++ tailWord_757774) baseStart_757774 baseEnd_757774 := by
    simpa [prefixWord, tailWord_757774, baseEnd_757774] using wordTrace_append hprefix tailTrace_757774
  have hstable : (prefixWord ++ tailWord_757774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757774).length < 2 ^ (prefixWord ++ tailWord_757774).sum := by decide
  have hdescent : baseEnd_757774 < baseStart_757774 := by decide
  rcases family_descends (prefixWord ++ tailWord_757774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757788 : List Nat := [2, 2, 3, 1, 3, 1, 4, 4]
def baseStart_757788 : Nat := 118140960795 + 757788 * 2 ^ 59
def prefixEnd_757788 : Nat := 4983230072969 + 3 ^ 40 * 757788 * 2
def baseEnd_757788 : Nat := 115291697247225595456297

theorem tailTrace_757788 : CollatzResearch.WordTrace tailWord_757788 prefixEnd_757788 115291697247225595456297 := by
  unfold tailWord_757788
  simp only [CollatzResearch.WordTrace]
  refine ⟨13819399489335485365933009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18425865985780647154577345 13819399489335485365933009)
  ·
    refine ⟨10364549617001614024449757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13819399489335485365933009 10364549617001614024449757)
    ·
      refine ⟨3886706106375605259168659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10364549617001614024449757 3886706106375605259168659)
      ·
        refine ⟨5830059159563407888752989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3886706106375605259168659 5830059159563407888752989)
        ·
          refine ⟨2186272184836277958282371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5830059159563407888752989 2186272184836277958282371)
          ·
            refine ⟨3279408277254416937423557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186272184836277958282371 3279408277254416937423557)
            ·
              refine ⟨614889051985203175766917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3279408277254416937423557 614889051985203175766917)
              ·
                refine ⟨115291697247225595456297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 614889051985203175766917 115291697247225595456297)
                ·
                  rfl

theorem cell20_757788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_757788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757788 prefixEnd_757788 := by exact prefixLift 757788
  have htrace : WordTrace (prefixWord ++ tailWord_757788) baseStart_757788 baseEnd_757788 := by
    simpa [prefixWord, tailWord_757788, baseEnd_757788] using wordTrace_append hprefix tailTrace_757788
  have hstable : (prefixWord ++ tailWord_757788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757788).length < 2 ^ (prefixWord ++ tailWord_757788).sum := by decide
  have hdescent : baseEnd_757788 < baseStart_757788 := by decide
  rcases family_descends (prefixWord ++ tailWord_757788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757809 : List Nat := [1, 2, 2, 3, 1, 5, 6]
def baseStart_757809 : Nat := 118140960795 + 757809 * 2 ^ 59
def prefixEnd_757809 : Nat := 4983230072969 + 3 ^ 40 * 757809 * 2
def baseEnd_757809 : Nat := 38431630745988227407645

theorem tailTrace_757809 : CollatzResearch.WordTrace tailWord_757809 prefixEnd_757809 38431630745988227407645 := by
  unfold tailWord_757809
  simp only [CollatzResearch.WordTrace]
  refine ⟨27639564911594891318380481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18426376607729927545586987 27639564911594891318380481)
  ·
    refine ⟨20729673683696168488785361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27639564911594891318380481 20729673683696168488785361)
    ·
      refine ⟨15547255262772126366589021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20729673683696168488785361 15547255262772126366589021)
      ·
        refine ⟨5830220723539547387470883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15547255262772126366589021 5830220723539547387470883)
        ·
          refine ⟨8745331085309321081206325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5830220723539547387470883 8745331085309321081206325)
          ·
            refine ⟨819874789247748851363093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8745331085309321081206325 819874789247748851363093)
            ·
              refine ⟨38431630745988227407645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 819874789247748851363093 38431630745988227407645)
              ·
                rfl

theorem cell20_757809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 6].length) (baseStart_757809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757809 prefixEnd_757809 := by exact prefixLift 757809
  have htrace : WordTrace (prefixWord ++ tailWord_757809) baseStart_757809 baseEnd_757809 := by
    simpa [prefixWord, tailWord_757809, baseEnd_757809] using wordTrace_append hprefix tailTrace_757809
  have hstable : (prefixWord ++ tailWord_757809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757809).length < 2 ^ (prefixWord ++ tailWord_757809).sum := by decide
  have hdescent : baseEnd_757809 < baseStart_757809 := by decide
  rcases family_descends (prefixWord ++ tailWord_757809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757868 : List Nat := [2, 2, 1, 1, 3, 11]
def baseStart_757868 : Nat := 118140960795 + 757868 * 2 ^ 59
def prefixEnd_757868 : Nat := 4983230072969 + 3 ^ 40 * 757868 * 2
def baseEnd_757868 : Nat := 12811540960057483840811

theorem tailTrace_757868 : CollatzResearch.WordTrace tailWord_757868 prefixEnd_757868 12811540960057483840811 := by
  unfold tailWord_757868
  simp only [CollatzResearch.WordTrace]
  refine ⟨13820858409190572197389129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18427811212254096263185505 13820858409190572197389129)
  ·
    refine ⟨10365643806892929148041847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13820858409190572197389129 10365643806892929148041847)
    ·
      refine ⟨15548465710339393722062771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10365643806892929148041847 15548465710339393722062771)
      ·
        refine ⟨23322698565509090583094157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15548465710339393722062771 23322698565509090583094157)
        ·
          refine ⟨8746011962065908968660309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23322698565509090583094157 8746011962065908968660309)
          ·
            refine ⟨12811540960057483840811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8746011962065908968660309 12811540960057483840811)
            ·
              rfl

theorem cell20_757868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 11].length) (baseStart_757868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757868 prefixEnd_757868 := by exact prefixLift 757868
  have htrace : WordTrace (prefixWord ++ tailWord_757868) baseStart_757868 baseEnd_757868 := by
    simpa [prefixWord, tailWord_757868, baseEnd_757868] using wordTrace_append hprefix tailTrace_757868
  have hstable : (prefixWord ++ tailWord_757868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757868).length < 2 ^ (prefixWord ++ tailWord_757868).sum := by decide
  have hdescent : baseEnd_757868 < baseStart_757868 := by decide
  rcases family_descends (prefixWord ++ tailWord_757868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757871 : List Nat := [1, 1, 2, 1, 3, 5, 2, 2, 3]
def baseStart_757871 : Nat := 118140960795 + 757871 * 2 ^ 59
def prefixEnd_757871 : Nat := 4983230072969 + 3 ^ 40 * 757871 * 2
def baseEnd_757871 : Nat := 345912975203297386601885

theorem tailTrace_757871 : CollatzResearch.WordTrace tailWord_757871 prefixEnd_757871 345912975203297386601885 := by
  unfold tailWord_757871
  simp only [CollatzResearch.WordTrace]
  refine ⟨27641826237370275907137467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18427884158246850604758311 27641826237370275907137467)
  ·
    refine ⟨41462739356055413860706201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27641826237370275907137467 41462739356055413860706201)
    ·
      refine ⟨31097054517041560395529651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41462739356055413860706201 31097054517041560395529651)
      ·
        refine ⟨46645581775562340593294477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31097054517041560395529651 46645581775562340593294477)
        ·
          refine ⟨17492093165835877722485429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46645581775562340593294477 17492093165835877722485429)
          ·
            refine ⟨1639883734297113536483009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17492093165835877722485429 1639883734297113536483009)
            ·
              refine ⟨1229912800722835152362257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1639883734297113536483009 1229912800722835152362257)
              ·
                refine ⟨922434600542126364271693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1229912800722835152362257 922434600542126364271693)
                ·
                  refine ⟨345912975203297386601885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 922434600542126364271693 345912975203297386601885)
                  ·
                    rfl

theorem cell20_757871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 3].length) (baseStart_757871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757871 prefixEnd_757871 := by exact prefixLift 757871
  have htrace : WordTrace (prefixWord ++ tailWord_757871) baseStart_757871 baseEnd_757871 := by
    simpa [prefixWord, tailWord_757871, baseEnd_757871] using wordTrace_append hprefix tailTrace_757871
  have hstable : (prefixWord ++ tailWord_757871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757871).length < 2 ^ (prefixWord ++ tailWord_757871).sum := by decide
  have hdescent : baseEnd_757871 < baseStart_757871 := by decide
  rcases family_descends (prefixWord ++ tailWord_757871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757874 : List Nat := [3, 2, 1, 2, 2, 2, 4, 2, 2]
def baseStart_757874 : Nat := 118140960795 + 757874 * 2 ^ 59
def prefixEnd_757874 : Nat := 4983230072969 + 3 ^ 40 * 757874 * 2
def baseEnd_757874 : Nat := 345914344485042709501873

theorem tailTrace_757874 : CollatzResearch.WordTrace tailWord_757874 prefixEnd_757874 345914344485042709501873 := by
  unfold tailWord_757874
  simp only [CollatzResearch.WordTrace]
  refine ⟨6910483914089851854874169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18427957104239604946331117 6910483914089851854874169)
  ·
    refine ⟨5182862935567388891155627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6910483914089851854874169 5182862935567388891155627)
    ·
      refine ⟨7774294403351083336733441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5182862935567388891155627 7774294403351083336733441)
      ·
        refine ⟨5830720802513312502550081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7774294403351083336733441 5830720802513312502550081)
        ·
          refine ⟨4373040601884984376912561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5830720802513312502550081 4373040601884984376912561)
          ·
            refine ⟨3279780451413738282684421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4373040601884984376912561 3279780451413738282684421)
            ·
              refine ⟨614958834640075928003329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3279780451413738282684421 614958834640075928003329)
              ·
                refine ⟨461219125980056946002497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 614958834640075928003329 461219125980056946002497)
                ·
                  refine ⟨345914344485042709501873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461219125980056946002497 345914344485042709501873)
                  ·
                    rfl

theorem cell20_757874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_757874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757874 prefixEnd_757874 := by exact prefixLift 757874
  have htrace : WordTrace (prefixWord ++ tailWord_757874) baseStart_757874 baseEnd_757874 := by
    simpa [prefixWord, tailWord_757874, baseEnd_757874] using wordTrace_append hprefix tailTrace_757874
  have hstable : (prefixWord ++ tailWord_757874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757874).length < 2 ^ (prefixWord ++ tailWord_757874).sum := by decide
  have hdescent : baseEnd_757874 < baseStart_757874 := by decide
  rcases family_descends (prefixWord ++ tailWord_757874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757885 : List Nat := [1, 4, 1, 1, 3, 2, 3, 5]
def baseStart_757885 : Nat := 118140960795 + 757885 * 2 ^ 59
def prefixEnd_757885 : Nat := 4983230072969 + 3 ^ 40 * 757885 * 2
def baseEnd_757885 : Nat := 115306455061591853378387

theorem tailTrace_757885 : CollatzResearch.WordTrace tailWord_757885 prefixEnd_757885 115306455061591853378387 := by
  unfold tailWord_757885
  simp only [CollatzResearch.WordTrace]
  refine ⟨27642336859319556298147109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18428224572879704198764739 27642336859319556298147109)
  ·
    refine ⟨5182938161122416805902583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27642336859319556298147109 5182938161122416805902583)
    ·
      refine ⟨7774407241683625208853875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5182938161122416805902583 7774407241683625208853875)
      ·
        refine ⟨11661610862525437813280813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7774407241683625208853875 11661610862525437813280813)
        ·
          refine ⟨4373104073447039179980305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11661610862525437813280813 4373104073447039179980305)
          ·
            refine ⟨3279828055085279384985229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4373104073447039179980305 3279828055085279384985229)
            ·
              refine ⟨1229935520656979769369461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3279828055085279384985229 1229935520656979769369461)
              ·
                refine ⟨115306455061591853378387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1229935520656979769369461 115306455061591853378387)
                ·
                  rfl

theorem cell20_757885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 5].length) (baseStart_757885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757885 prefixEnd_757885 := by exact prefixLift 757885
  have htrace : WordTrace (prefixWord ++ tailWord_757885) baseStart_757885 baseEnd_757885 := by
    simpa [prefixWord, tailWord_757885, baseEnd_757885] using wordTrace_append hprefix tailTrace_757885
  have hstable : (prefixWord ++ tailWord_757885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757885).length < 2 ^ (prefixWord ++ tailWord_757885).sum := by decide
  have hdescent : baseEnd_757885 < baseStart_757885 := by decide
  rcases family_descends (prefixWord ++ tailWord_757885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757912 : List Nat := [2, 1, 2, 4, 3, 1, 2, 3, 2]
def baseStart_757912 : Nat := 118140960795 + 757912 * 2 ^ 59
def prefixEnd_757912 : Nat := 4983230072969 + 3 ^ 40 * 757912 * 2
def baseEnd_757912 : Nat := 345931688720483466235051

theorem tailTrace_757912 : CollatzResearch.WordTrace tailWord_757912 prefixEnd_757912 345931688720483466235051 := by
  unfold tailWord_757912
  simp only [CollatzResearch.WordTrace]
  refine ⟨13821660815110869954689995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18428881086814493272919993 13821660815110869954689995)
  ·
    refine ⟨20732491222666304932034993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13821660815110869954689995 20732491222666304932034993)
    ·
      refine ⟨15549368416999728699026245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20732491222666304932034993 15549368416999728699026245)
      ·
        refine ⟨2915506578187449131067421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15549368416999728699026245 2915506578187449131067421)
        ·
          refine ⟨1093314966820293424150283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2915506578187449131067421 1093314966820293424150283)
          ·
            refine ⟨1639972450230440136225425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093314966820293424150283 1639972450230440136225425)
            ·
              refine ⟨1229979337672830102169069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1639972450230440136225425 1229979337672830102169069)
              ·
                refine ⟨461242251627311288313401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1229979337672830102169069 461242251627311288313401)
                ·
                  refine ⟨345931688720483466235051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461242251627311288313401 345931688720483466235051)
                  ·
                    rfl

theorem cell20_757912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 2].length) (baseStart_757912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757912 prefixEnd_757912 := by exact prefixLift 757912
  have htrace : WordTrace (prefixWord ++ tailWord_757912) baseStart_757912 baseEnd_757912 := by
    simpa [prefixWord, tailWord_757912, baseEnd_757912] using wordTrace_append hprefix tailTrace_757912
  have hstable : (prefixWord ++ tailWord_757912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757912).length < 2 ^ (prefixWord ++ tailWord_757912).sum := by decide
  have hdescent : baseEnd_757912 < baseStart_757912 := by decide
  rcases family_descends (prefixWord ++ tailWord_757912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757933 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 4]
def baseStart_757933 : Nat := 118140960795 + 757933 * 2 ^ 59
def prefixEnd_757933 : Nat := 4983230072969 + 3 ^ 40 * 757933 * 2
def baseEnd_757933 : Nat := 345941273692700726534965

theorem tailTrace_757933 : CollatzResearch.WordTrace tailWord_757933 prefixEnd_757933 345941273692700726534965 := by
  unfold tailWord_757933
  simp only [CollatzResearch.WordTrace]
  refine ⟨27644087563145660495894453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18429391708763773663929635 27644087563145660495894453)
  ·
    refine ⟨2591633209044905671490105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27644087563145660495894453 2591633209044905671490105)
    ·
      refine ⟨1943724906783679253617579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2591633209044905671490105 1943724906783679253617579)
      ·
        refine ⟨2915587360175518880426369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1943724906783679253617579 2915587360175518880426369)
        ·
          refine ⟨2186690520131639160319777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2915587360175518880426369 2186690520131639160319777)
          ·
            refine ⟨1640017890098729370239833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2186690520131639160319777 1640017890098729370239833)
            ·
              refine ⟨1230013417574047027679875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1640017890098729370239833 1230013417574047027679875)
              ·
                refine ⟨1845020126361070541519813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230013417574047027679875 1845020126361070541519813)
                ·
                  refine ⟨345941273692700726534965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1845020126361070541519813 345941273692700726534965)
                  ·
                    rfl

theorem cell20_757933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_757933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757933 prefixEnd_757933 := by exact prefixLift 757933
  have htrace : WordTrace (prefixWord ++ tailWord_757933) baseStart_757933 baseEnd_757933 := by
    simpa [prefixWord, tailWord_757933, baseEnd_757933] using wordTrace_append hprefix tailTrace_757933
  have hstable : (prefixWord ++ tailWord_757933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757933).length < 2 ^ (prefixWord ++ tailWord_757933).sum := by decide
  have hdescent : baseEnd_757933 < baseStart_757933 := by decide
  rcases family_descends (prefixWord ++ tailWord_757933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757944 : List Nat := [2, 1, 2, 1, 2, 1, 4, 7]
def baseStart_757944 : Nat := 118140960795 + 757944 * 2 ^ 59
def prefixEnd_757944 : Nat := 4983230072969 + 3 ^ 40 * 757944 * 2
def baseEnd_757944 : Nat := 115315431464144525722751

theorem tailTrace_757944 : CollatzResearch.WordTrace tailWord_757944 prefixEnd_757944 115315431464144525722751 := by
  unfold tailWord_757944
  simp only [CollatzResearch.WordTrace]
  refine ⟨13822244383052904687272443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18429659177403872916363257 13822244383052904687272443)
  ·
    refine ⟨20733366574579357030908665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13822244383052904687272443 20733366574579357030908665)
    ·
      refine ⟨15550024930934517773181499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20733366574579357030908665 15550024930934517773181499)
      ·
        refine ⟨23325037396401776659772249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15550024930934517773181499 23325037396401776659772249)
        ·
          refine ⟨17493778047301332494829187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23325037396401776659772249 17493778047301332494829187)
          ·
            refine ⟨26240667070951998742243781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17493778047301332494829187 26240667070951998742243781)
            ·
              refine ⟨4920125075803499764170709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26240667070951998742243781 4920125075803499764170709)
              ·
                refine ⟨115315431464144525722751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4920125075803499764170709 115315431464144525722751)
                ·
                  rfl

theorem cell20_757944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_757944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757944 prefixEnd_757944 := by exact prefixLift 757944
  have htrace : WordTrace (prefixWord ++ tailWord_757944) baseStart_757944 baseEnd_757944 := by
    simpa [prefixWord, tailWord_757944, baseEnd_757944] using wordTrace_append hprefix tailTrace_757944
  have hstable : (prefixWord ++ tailWord_757944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757944).length < 2 ^ (prefixWord ++ tailWord_757944).sum := by decide
  have hdescent : baseEnd_757944 < baseStart_757944 := by decide
  rcases family_descends (prefixWord ++ tailWord_757944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757947 : List Nat := [1, 1, 1, 1, 1, 2, 9, 1, 3]
def baseStart_757947 : Nat := 118140960795 + 757947 * 2 ^ 59
def prefixEnd_757947 : Nat := 4983230072969 + 3 ^ 40 * 757947 * 2
def baseEnd_757947 : Nat := 345947663674178900068241

theorem tailTrace_757947 : CollatzResearch.WordTrace tailWord_757947 prefixEnd_757947 345947663674178900068241 := by
  unfold tailWord_757947
  simp only [CollatzResearch.WordTrace]
  refine ⟨27644598185094940886904095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18429732123396627257936063 27644598185094940886904095)
  ·
    refine ⟨41466897277642411330356143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27644598185094940886904095 41466897277642411330356143)
    ·
      refine ⟨62200345916463616995534215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41466897277642411330356143 62200345916463616995534215)
      ·
        refine ⟨93300518874695425493301323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62200345916463616995534215 93300518874695425493301323)
        ·
          refine ⟨139950778312043138239951985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93300518874695425493301323 139950778312043138239951985)
          ·
            refine ⟨104963083734032353679963989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139950778312043138239951985 104963083734032353679963989)
            ·
              refine ⟨615018068754095822343539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 104963083734032353679963989 615018068754095822343539)
              ·
                refine ⟨922527103131143733515309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615018068754095822343539 922527103131143733515309)
                ·
                  refine ⟨345947663674178900068241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 922527103131143733515309 345947663674178900068241)
                  ·
                    rfl

theorem cell20_757947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 3].length) (baseStart_757947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757947 prefixEnd_757947 := by exact prefixLift 757947
  have htrace : WordTrace (prefixWord ++ tailWord_757947) baseStart_757947 baseEnd_757947 := by
    simpa [prefixWord, tailWord_757947, baseEnd_757947] using wordTrace_append hprefix tailTrace_757947
  have hstable : (prefixWord ++ tailWord_757947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757947).length < 2 ^ (prefixWord ++ tailWord_757947).sum := by decide
  have hdescent : baseEnd_757947 < baseStart_757947 := by decide
  rcases family_descends (prefixWord ++ tailWord_757947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757992 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 4]
def baseStart_757992 : Nat := 118140960795 + 757992 * 2 ^ 59
def prefixEnd_757992 : Nat := 4983230072969 + 3 ^ 40 * 757992 * 2
def baseEnd_757992 : Nat := 345968202900358743568057

theorem tailTrace_757992 : CollatzResearch.WordTrace tailWord_757992 prefixEnd_757992 345968202900358743568057 := by
  unfold tailWord_757992
  simp only [CollatzResearch.WordTrace]
  refine ⟨13823119734965956786146115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18430826313287942381528153 13823119734965956786146115)
  ·
    refine ⟨20734679602448935179219173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13823119734965956786146115 20734679602448935179219173)
    ·
      refine ⟨3887752425459175346103595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20734679602448935179219173 3887752425459175346103595)
      ·
        refine ⟨5831628638188763019155393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3887752425459175346103595 5831628638188763019155393)
        ·
          refine ⟨4373721478641572264366545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5831628638188763019155393 4373721478641572264366545)
          ·
            refine ⟨3280291108981179198274909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4373721478641572264366545 3280291108981179198274909)
            ·
              refine ⟨1230109165867942199353091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3280291108981179198274909 1230109165867942199353091)
              ·
                refine ⟨1845163748801913299029637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230109165867942199353091 1845163748801913299029637)
                ·
                  refine ⟨345968202900358743568057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1845163748801913299029637 345968202900358743568057)
                  ·
                    rfl

theorem cell20_757992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_757992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757992 prefixEnd_757992 := by exact prefixLift 757992
  have htrace : WordTrace (prefixWord ++ tailWord_757992) baseStart_757992 baseEnd_757992 := by
    simpa [prefixWord, tailWord_757992, baseEnd_757992] using wordTrace_append hprefix tailTrace_757992
  have hstable : (prefixWord ++ tailWord_757992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757992).length < 2 ^ (prefixWord ++ tailWord_757992).sum := by decide
  have hdescent : baseEnd_757992 < baseStart_757992 := by decide
  rcases family_descends (prefixWord ++ tailWord_757992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757999 : List Nat := [1, 1, 2, 1, 6, 2, 2, 5]
def baseStart_757999 : Nat := 118140960795 + 757999 * 2 ^ 59
def prefixEnd_757999 : Nat := 4983230072969 + 3 ^ 40 * 757999 * 2
def baseEnd_757999 : Nat := 115323799297032610111565

theorem tailTrace_757999 : CollatzResearch.WordTrace tailWord_757999 prefixEnd_757999 115323799297032610111565 := by
  unfold tailWord_757999
  simp only [CollatzResearch.WordTrace]
  refine ⟨27646494780906553767797051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18430996520604369178531367 27646494780906553767797051)
  ·
    refine ⟨41469742171359830651695577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27646494780906553767797051 41469742171359830651695577)
    ·
      refine ⟨31102306628519872988771683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41469742171359830651695577 31102306628519872988771683)
      ·
        refine ⟨46653459942779809483157525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31102306628519872988771683 46653459942779809483157525)
        ·
          refine ⟨2186880934817803569523009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46653459942779809483157525 2186880934817803569523009)
          ·
            refine ⟨1640160701113352677142257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2186880934817803569523009 1640160701113352677142257)
            ·
              refine ⟨1230120525835014507856693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1640160701113352677142257 1230120525835014507856693)
              ·
                refine ⟨115323799297032610111565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1230120525835014507856693 115323799297032610111565)
                ·
                  rfl

theorem cell20_757999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 5].length) (baseStart_757999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_757999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_757999 prefixEnd_757999 := by exact prefixLift 757999
  have htrace : WordTrace (prefixWord ++ tailWord_757999) baseStart_757999 baseEnd_757999 := by
    simpa [prefixWord, tailWord_757999, baseEnd_757999] using wordTrace_append hprefix tailTrace_757999
  have hstable : (prefixWord ++ tailWord_757999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757999).length < 2 ^ (prefixWord ++ tailWord_757999).sum := by decide
  have hdescent : baseEnd_757999 < baseStart_757999 := by decide
  rcases family_descends (prefixWord ++ tailWord_757999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758002 : List Nat := [3, 2, 1, 3, 2, 1, 4, 1, 3]
def baseStart_758002 : Nat := 118140960795 + 758002 * 2 ^ 59
def prefixEnd_758002 : Nat := 4983230072969 + 3 ^ 40 * 758002 * 2
def baseEnd_758002 : Nat := 345972767172843153234683

theorem tailTrace_758002 : CollatzResearch.WordTrace tailWord_758002 prefixEnd_758002 345972767172843153234683 := by
  unfold tailWord_758002
  simp only [CollatzResearch.WordTrace]
  refine ⟨6911651049973921320039065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18431069466597123520104173 6911651049973921320039065)
  ·
    refine ⟨5183738287480440990029299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6911651049973921320039065 5183738287480440990029299)
    ·
      refine ⟨7775607431220661485043949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5183738287480440990029299 7775607431220661485043949)
      ·
        refine ⟨2915852786707748056891481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7775607431220661485043949 2915852786707748056891481)
        ·
          refine ⟨2186889590030811042668611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2915852786707748056891481 2186889590030811042668611)
          ·
            refine ⟨3280334385046216564002917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186889590030811042668611 3280334385046216564002917)
            ·
              refine ⟨615062697196165605750547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3280334385046216564002917 615062697196165605750547)
              ·
                refine ⟨922594045794248408625821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615062697196165605750547 922594045794248408625821)
                ·
                  refine ⟨345972767172843153234683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 922594045794248408625821 345972767172843153234683)
                  ·
                    rfl

theorem cell20_758002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_758002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758002 prefixEnd_758002 := by exact prefixLift 758002
  have htrace : WordTrace (prefixWord ++ tailWord_758002) baseStart_758002 baseEnd_758002 := by
    simpa [prefixWord, tailWord_758002, baseEnd_758002] using wordTrace_append hprefix tailTrace_758002
  have hstable : (prefixWord ++ tailWord_758002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758002).length < 2 ^ (prefixWord ++ tailWord_758002).sum := by decide
  have hdescent : baseEnd_758002 < baseStart_758002 := by decide
  rcases family_descends (prefixWord ++ tailWord_758002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758013 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 4]
def baseStart_758013 : Nat := 118140960795 + 758013 * 2 ^ 59
def prefixEnd_758013 : Nat := 4983230072969 + 3 ^ 40 * 758013 * 2
def baseEnd_758013 : Nat := 345977787872576003867971

theorem tailTrace_758013 : CollatzResearch.WordTrace tailWord_758013 prefixEnd_758013 345977787872576003867971 := by
  unfold tailWord_758013
  simp only [CollatzResearch.WordTrace]
  refine ⟨27647005402855834158806693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18431336935237222772537795 27647005402855834158806693)
  ·
    refine ⟨5183813513035468904776255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27647005402855834158806693 5183813513035468904776255)
    ·
      refine ⟨7775720269553203357164383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5183813513035468904776255 7775720269553203357164383)
      ·
        refine ⟨11663580404329805035746575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7775720269553203357164383 11663580404329805035746575)
        ·
          refine ⟨17495370606494707553619863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11663580404329805035746575 17495370606494707553619863)
          ·
            refine ⟨26243055909742061330429795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17495370606494707553619863 26243055909742061330429795)
            ·
              refine ⟨39364583864613091995644693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26243055909742061330429795 39364583864613091995644693)
              ·
                refine ⟨1845214868653738687295845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39364583864613091995644693 1845214868653738687295845)
                ·
                  refine ⟨345977787872576003867971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1845214868653738687295845 345977787872576003867971)
                  ·
                    rfl

theorem cell20_758013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_758013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758013 prefixEnd_758013 := by exact prefixLift 758013
  have htrace : WordTrace (prefixWord ++ tailWord_758013) baseStart_758013 baseEnd_758013 := by
    simpa [prefixWord, tailWord_758013, baseEnd_758013] using wordTrace_append hprefix tailTrace_758013
  have hstable : (prefixWord ++ tailWord_758013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758013).length < 2 ^ (prefixWord ++ tailWord_758013).sum := by decide
  have hdescent : baseEnd_758013 < baseStart_758013 := by decide
  rcases family_descends (prefixWord ++ tailWord_758013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758047 : List Nat := [1, 1, 2, 4, 3, 2, 1, 4, 2]
def baseStart_758047 : Nat := 118140960795 + 758047 * 2 ^ 59
def prefixEnd_758047 : Nat := 4983230072969 + 3 ^ 40 * 758047 * 2
def baseEnd_758047 : Nat := 345993306399022996734499

theorem tailTrace_758047 : CollatzResearch.WordTrace tailWord_758047 prefixEnd_758047 345993306399022996734499 := by
  unfold tailWord_758047
  simp only [CollatzResearch.WordTrace]
  refine ⟨27648245484732657965544395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18432163656488438643696263 27648245484732657965544395)
  ·
    refine ⟨41472368227098986948316593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27648245484732657965544395 41472368227098986948316593)
    ·
      refine ⟨31104276170324240211237445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41472368227098986948316593 31104276170324240211237445)
      ·
        refine ⟨5832051781935795039607021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31104276170324240211237445 5832051781935795039607021)
        ·
          refine ⟨2187019418225923139852633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5832051781935795039607021 2187019418225923139852633)
          ·
            refine ⟨1640264563669442354889475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2187019418225923139852633 1640264563669442354889475)
            ·
              refine ⟨2460396845504163532334213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1640264563669442354889475 2460396845504163532334213)
              ·
                refine ⟨461324408532030662312665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2460396845504163532334213 461324408532030662312665)
                ·
                  refine ⟨345993306399022996734499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461324408532030662312665 345993306399022996734499)
                  ·
                    rfl

theorem cell20_758047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 2].length) (baseStart_758047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758047 prefixEnd_758047 := by exact prefixLift 758047
  have htrace : WordTrace (prefixWord ++ tailWord_758047) baseStart_758047 baseEnd_758047 := by
    simpa [prefixWord, tailWord_758047, baseEnd_758047] using wordTrace_append hprefix tailTrace_758047
  have hstable : (prefixWord ++ tailWord_758047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758047).length < 2 ^ (prefixWord ++ tailWord_758047).sum := by decide
  have hdescent : baseEnd_758047 < baseStart_758047 := by decide
  rcases family_descends (prefixWord ++ tailWord_758047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758051 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 4]
def baseStart_758051 : Nat := 118140960795 + 758051 * 2 ^ 59
def prefixEnd_758051 : Nat := 4983230072969 + 3 ^ 40 * 758051 * 2
def baseEnd_758051 : Nat := 345995132108016760601149

theorem tailTrace_758051 : CollatzResearch.WordTrace tailWord_758051 prefixEnd_758051 345995132108016760601149 := by
  unfold tailWord_758051
  simp only [CollatzResearch.WordTrace]
  refine ⟨27648391376718166648690007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18432260917812111099126671 27648391376718166648690007)
  ·
    refine ⟨41472587065077249973035011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27648391376718166648690007 41472587065077249973035011)
    ·
      refine ⟨62208880597615874959552517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41472587065077249973035011 62208880597615874959552517)
      ·
        refine ⟨11664165112052976554916097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62208880597615874959552517 11664165112052976554916097)
        ·
          refine ⟨8748123834039732416187073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11664165112052976554916097 8748123834039732416187073)
          ·
            refine ⟨6561092875529799312140305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8748123834039732416187073 6561092875529799312140305)
            ·
              refine ⟨4920819656647349484105229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6561092875529799312140305 4920819656647349484105229)
              ·
                refine ⟨1845307371242756056539461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4920819656647349484105229 1845307371242756056539461)
                ·
                  refine ⟨345995132108016760601149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1845307371242756056539461 345995132108016760601149)
                  ·
                    rfl

theorem cell20_758051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_758051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758051 prefixEnd_758051 := by exact prefixLift 758051
  have htrace : WordTrace (prefixWord ++ tailWord_758051) baseStart_758051 baseEnd_758051 := by
    simpa [prefixWord, tailWord_758051, baseEnd_758051] using wordTrace_append hprefix tailTrace_758051
  have hstable : (prefixWord ++ tailWord_758051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758051).length < 2 ^ (prefixWord ++ tailWord_758051).sum := by decide
  have hdescent : baseEnd_758051 < baseStart_758051 := by decide
  rcases family_descends (prefixWord ++ tailWord_758051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758068 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 6]
def baseStart_758068 : Nat := 118140960795 + 758068 * 2 ^ 59
def prefixEnd_758068 : Nat := 4983230072969 + 3 ^ 40 * 758068 * 2
def baseEnd_758068 : Nat := 346002891371240257034413

theorem tailTrace_758068 : CollatzResearch.WordTrace tailWord_758068 prefixEnd_758068 346002891371240257034413 := by
  unfold tailWord_758068
  simp only [CollatzResearch.WordTrace]
  refine ⟨13824505708828289276029429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18432674278437719034705905 13824505708828289276029429)
  ·
    refine ⟨1296047410202652119627759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13824505708828289276029429 1296047410202652119627759)
    ·
      refine ⟨1944071115303978179441639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1296047410202652119627759 1944071115303978179441639)
      ·
        refine ⟨2916106672955967269162459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1944071115303978179441639 2916106672955967269162459)
        ·
          refine ⟨4374160009433950903743689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2916106672955967269162459 4374160009433950903743689)
          ·
            refine ⟨3280620007075463177807767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4374160009433950903743689 3280620007075463177807767)
            ·
              refine ⟨4920930010613194766711651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3280620007075463177807767 4920930010613194766711651)
              ·
                refine ⟨7381395015919792150067477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4920930010613194766711651 7381395015919792150067477)
                ·
                  refine ⟨346002891371240257034413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7381395015919792150067477 346002891371240257034413)
                  ·
                    rfl

theorem cell20_758068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_758068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758068 prefixEnd_758068 := by exact prefixLift 758068
  have htrace : WordTrace (prefixWord ++ tailWord_758068) baseStart_758068 baseEnd_758068 := by
    simpa [prefixWord, tailWord_758068, baseEnd_758068] using wordTrace_append hprefix tailTrace_758068
  have hstable : (prefixWord ++ tailWord_758068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758068).length < 2 ^ (prefixWord ++ tailWord_758068).sum := by decide
  have hdescent : baseEnd_758068 < baseStart_758068 := by decide
  rcases family_descends (prefixWord ++ tailWord_758068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758096 : List Nat := [2, 1, 1, 1, 1, 7, 7]
def baseStart_758096 : Nat := 118140960795 + 758096 * 2 ^ 59
def prefixEnd_758096 : Nat := 4983230072969 + 3 ^ 40 * 758096 * 2
def baseEnd_758096 : Nat := 38446185703799622677885

theorem tailTrace_758096 : CollatzResearch.WordTrace tailWord_758096 prefixEnd_758096 38446185703799622677885 := by
  unfold tailWord_758096
  simp only [CollatzResearch.WordTrace]
  refine ⟨13825016330777569667039071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18433355107703426222718761 13825016330777569667039071)
  ·
    refine ⟨20737524496166354500558607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13825016330777569667039071 20737524496166354500558607)
    ·
      refine ⟨31106286744249531750837911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20737524496166354500558607 31106286744249531750837911)
      ·
        refine ⟨46659430116374297626256867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31106286744249531750837911 46659430116374297626256867)
        ·
          refine ⟨69989145174561446439385301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46659430116374297626256867 69989145174561446439385301)
          ·
            refine ⟨1640370590028783900923093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 69989145174561446439385301 1640370590028783900923093)
            ·
              refine ⟨38446185703799622677885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1640370590028783900923093 38446185703799622677885)
              ·
                rfl

theorem cell20_758096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 7].length) (baseStart_758096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758096 prefixEnd_758096 := by exact prefixLift 758096
  have htrace : WordTrace (prefixWord ++ tailWord_758096) baseStart_758096 baseEnd_758096 := by
    simpa [prefixWord, tailWord_758096, baseEnd_758096] using wordTrace_append hprefix tailTrace_758096
  have hstable : (prefixWord ++ tailWord_758096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758096).length < 2 ^ (prefixWord ++ tailWord_758096).sum := by decide
  have hdescent : baseEnd_758096 < baseStart_758096 := by decide
  rcases family_descends (prefixWord ++ tailWord_758096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758130 : List Nat := [3, 2, 1, 2, 1, 5, 2, 4]
def baseStart_758130 : Nat := 118140960795 + 758130 * 2 ^ 59
def prefixEnd_758130 : Nat := 4983230072969 + 3 ^ 40 * 758130 * 2
def baseEnd_758130 : Nat := 115343729953547865655831

theorem tailTrace_758130 : CollatzResearch.WordTrace tailWord_758130 prefixEnd_758130 115343729953547865655831 := by
  unfold tailWord_758130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6912818185857990785203961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18434181828954642093877229 6912818185857990785203961)
  ·
    refine ⟨5184613639393493088902971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6912818185857990785203961 5184613639393493088902971)
    ·
      refine ⟨7776920459090239633354457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5184613639393493088902971 7776920459090239633354457)
      ·
        refine ⟨5832690344317679725015843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7776920459090239633354457 5832690344317679725015843)
        ·
          refine ⟨8749035516476519587523765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5832690344317679725015843 8749035516476519587523765)
          ·
            refine ⟨820222079669673711330353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8749035516476519587523765 820222079669673711330353)
            ·
              refine ⟨615166559752255283497765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820222079669673711330353 615166559752255283497765)
              ·
                refine ⟨115343729953547865655831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 615166559752255283497765 115343729953547865655831)
                ·
                  rfl

theorem cell20_758130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_758130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758130 prefixEnd_758130 := by exact prefixLift 758130
  have htrace : WordTrace (prefixWord ++ tailWord_758130) baseStart_758130 baseEnd_758130 := by
    simpa [prefixWord, tailWord_758130, baseEnd_758130] using wordTrace_append hprefix tailTrace_758130
  have hstable : (prefixWord ++ tailWord_758130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758130).length < 2 ^ (prefixWord ++ tailWord_758130).sum := by decide
  have hdescent : baseEnd_758130 < baseStart_758130 := by decide
  rcases family_descends (prefixWord ++ tailWord_758130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758212 : List Nat := [2, 3, 3, 2, 3, 1, 2, 2, 2]
def baseStart_758212 : Nat := 118140960795 + 758212 * 2 ^ 59
def prefixEnd_758212 : Nat := 4983230072969 + 3 ^ 40 * 758212 * 2
def baseEnd_758212 : Nat := 346068616895015756233825

theorem tailTrace_758212 : CollatzResearch.WordTrace tailWord_758212 prefixEnd_758212 346068616895015756233825 := by
  unfold tailWord_758212
  simp only [CollatzResearch.WordTrace]
  refine ⟨13827131764567445572650445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18436175686089927430200593 13827131764567445572650445)
  ·
    refine ⟨5185174411712792089743917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13827131764567445572650445 5185174411712792089743917)
    ·
      refine ⟨1944440404392297033653969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5185174411712792089743917 1944440404392297033653969)
      ·
        refine ⟨1458330303294222775240477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1944440404392297033653969 1458330303294222775240477)
        ·
          refine ⟨546873863735333540715179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1458330303294222775240477 546873863735333540715179)
          ·
            refine ⟨820310795603000311072769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546873863735333540715179 820310795603000311072769)
            ·
              refine ⟨615233096702250233304577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820310795603000311072769 615233096702250233304577)
              ·
                refine ⟨461424822526687674978433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615233096702250233304577 461424822526687674978433)
                ·
                  refine ⟨346068616895015756233825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461424822526687674978433 346068616895015756233825)
                  ·
                    rfl

theorem cell20_758212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_758212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758212 prefixEnd_758212 := by exact prefixLift 758212
  have htrace : WordTrace (prefixWord ++ tailWord_758212) baseStart_758212 baseEnd_758212 := by
    simpa [prefixWord, tailWord_758212, baseEnd_758212] using wordTrace_append hprefix tailTrace_758212
  have hstable : (prefixWord ++ tailWord_758212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758212).length < 2 ^ (prefixWord ++ tailWord_758212).sum := by decide
  have hdescent : baseEnd_758212 < baseStart_758212 := by decide
  rcases family_descends (prefixWord ++ tailWord_758212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758216 : List Nat := [2, 1, 3, 1, 3, 4, 2, 2, 2]
def baseStart_758216 : Nat := 118140960795 + 758216 * 2 ^ 59
def prefixEnd_758216 : Nat := 4983230072969 + 3 ^ 40 * 758216 * 2
def baseEnd_758216 : Nat := 346070442604009520100475

theorem tailTrace_758216 : CollatzResearch.WordTrace tailWord_758216 prefixEnd_758216 346070442604009520100475 := by
  unfold tailWord_758216
  simp only [CollatzResearch.WordTrace]
  refine ⟨13827204710560199914223251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18436272947413599885631001 13827204710560199914223251)
  ·
    refine ⟨20740807065840299871334877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13827204710560199914223251 20740807065840299871334877)
    ·
      refine ⟨7777802649690112451750579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20740807065840299871334877 7777802649690112451750579)
      ·
        refine ⟨11666703974535168677625869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7777802649690112451750579 11666703974535168677625869)
        ·
          refine ⟨4375013990450688254109701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11666703974535168677625869 4375013990450688254109701)
          ·
            refine ⟨820315123209504047645569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4375013990450688254109701 820315123209504047645569)
            ·
              refine ⟨615236342407128035734177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820315123209504047645569 615236342407128035734177)
              ·
                refine ⟨461427256805346026800633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615236342407128035734177 461427256805346026800633)
                ·
                  refine ⟨346070442604009520100475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461427256805346026800633 346070442604009520100475)
                  ·
                    rfl

theorem cell20_758216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 2].length) (baseStart_758216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758216 prefixEnd_758216 := by exact prefixLift 758216
  have htrace : WordTrace (prefixWord ++ tailWord_758216) baseStart_758216 baseEnd_758216 := by
    simpa [prefixWord, tailWord_758216, baseEnd_758216] using wordTrace_append hprefix tailTrace_758216
  have hstable : (prefixWord ++ tailWord_758216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758216).length < 2 ^ (prefixWord ++ tailWord_758216).sum := by decide
  have hdescent : baseEnd_758216 < baseStart_758216 := by decide
  rcases family_descends (prefixWord ++ tailWord_758216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758217 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 5]
def baseStart_758217 : Nat := 118140960795 + 758217 * 2 ^ 59
def prefixEnd_758217 : Nat := 4983230072969 + 3 ^ 40 * 758217 * 2
def baseEnd_758217 : Nat := 346070899031257961067137

theorem tailTrace_758217 : CollatzResearch.WordTrace tailWord_758217 prefixEnd_758217 346070899031257961067137 := by
  unfold tailWord_758217
  simp only [CollatzResearch.WordTrace]
  refine ⟨27654445894116776999232905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18436297262744517999488603 27654445894116776999232905)
  ·
    refine ⟨20740834420587582749424679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27654445894116776999232905 20740834420587582749424679)
    ·
      refine ⟨31111251630881374124137019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20740834420587582749424679 31111251630881374124137019)
      ·
        refine ⟨46666877446322061186205529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31111251630881374124137019 46666877446322061186205529)
        ·
          refine ⟨35000158084741545889654147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46666877446322061186205529 35000158084741545889654147)
          ·
            refine ⟨52500237127112318834481221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35000158084741545889654147 52500237127112318834481221)
            ·
              refine ⟨9843794461333559781465229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52500237127112318834481221 9843794461333559781465229)
              ·
                refine ⟨3691422923000084918049461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9843794461333559781465229 3691422923000084918049461)
                ·
                  refine ⟨346070899031257961067137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3691422923000084918049461 346070899031257961067137)
                  ·
                    rfl

theorem cell20_758217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_758217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758217 prefixEnd_758217 := by exact prefixLift 758217
  have htrace : WordTrace (prefixWord ++ tailWord_758217) baseStart_758217 baseEnd_758217 := by
    simpa [prefixWord, tailWord_758217, baseEnd_758217] using wordTrace_append hprefix tailTrace_758217
  have hstable : (prefixWord ++ tailWord_758217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758217).length < 2 ^ (prefixWord ++ tailWord_758217).sum := by decide
  have hdescent : baseEnd_758217 < baseStart_758217 := by decide
  rcases family_descends (prefixWord ++ tailWord_758217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758234 : List Nat := [3, 1, 1, 2, 3, 1, 1, 5, 3]
def baseStart_758234 : Nat := 118140960795 + 758234 * 2 ^ 59
def prefixEnd_758234 : Nat := 4983230072969 + 3 ^ 40 * 758234 * 2
def baseEnd_758234 : Nat := 346078658294481457500401

theorem tailTrace_758234 : CollatzResearch.WordTrace tailWord_758234 prefixEnd_758234 346078658294481457500401 := by
  unfold tailWord_758234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6913766483763797225650439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18436710623370125935067837 6913766483763797225650439)
  ·
    refine ⟨10370649725645695838475659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6913766483763797225650439 10370649725645695838475659)
    ·
      refine ⟨15555974588468543757713489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10370649725645695838475659 15555974588468543757713489)
      ·
        refine ⟨11666980941351407818285117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15555974588468543757713489 11666980941351407818285117)
        ·
          refine ⟨4375117853006777931856919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11666980941351407818285117 4375117853006777931856919)
          ·
            refine ⟨6562676779510166897785379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375117853006777931856919 6562676779510166897785379)
            ·
              refine ⟨9844015169265250346678069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562676779510166897785379 9844015169265250346678069)
              ·
                refine ⟨922876422118617220001069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9844015169265250346678069 922876422118617220001069)
                ·
                  refine ⟨346078658294481457500401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 922876422118617220001069 346078658294481457500401)
                  ·
                    rfl

theorem cell20_758234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_758234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758234 prefixEnd_758234 := by exact prefixLift 758234
  have htrace : WordTrace (prefixWord ++ tailWord_758234) baseStart_758234 baseEnd_758234 := by
    simpa [prefixWord, tailWord_758234, baseEnd_758234] using wordTrace_append hprefix tailTrace_758234
  have hstable : (prefixWord ++ tailWord_758234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758234).length < 2 ^ (prefixWord ++ tailWord_758234).sum := by decide
  have hdescent : baseEnd_758234 < baseStart_758234 := by decide
  rcases family_descends (prefixWord ++ tailWord_758234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758241 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 4]
def baseStart_758241 : Nat := 118140960795 + 758241 * 2 ^ 59
def prefixEnd_758241 : Nat := 4983230072969 + 3 ^ 40 * 758241 * 2
def baseEnd_758241 : Nat := 346081853285220544267039

theorem tailTrace_758241 : CollatzResearch.WordTrace tailWord_758241 prefixEnd_758241 346081853285220544267039 := by
  unfold tailWord_758241
  simp only [CollatzResearch.WordTrace]
  refine ⟨27655321246029829098106577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18436880830686552732071051 27655321246029829098106577)
  ·
    refine ⟨20741490934522371823579933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27655321246029829098106577 20741490934522371823579933)
    ·
      refine ⟨7778059100445889433842475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20741490934522371823579933 7778059100445889433842475)
      ·
        refine ⟨11667088650668834150763713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7778059100445889433842475 11667088650668834150763713)
        ·
          refine ⟨8750316488001625613072785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11667088650668834150763713 8750316488001625613072785)
          ·
            refine ⟨6562737366001219209804589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8750316488001625613072785 6562737366001219209804589)
            ·
              refine ⟨2461026512250457203676721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6562737366001219209804589 2461026512250457203676721)
              ·
                refine ⟨1845769884187842902757541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2461026512250457203676721 1845769884187842902757541)
                ·
                  refine ⟨346081853285220544267039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1845769884187842902757541 346081853285220544267039)
                  ·
                    rfl

theorem cell20_758241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_758241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758241 prefixEnd_758241 := by exact prefixLift 758241
  have htrace : WordTrace (prefixWord ++ tailWord_758241) baseStart_758241 baseEnd_758241 := by
    simpa [prefixWord, tailWord_758241, baseEnd_758241] using wordTrace_append hprefix tailTrace_758241
  have hstable : (prefixWord ++ tailWord_758241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758241).length < 2 ^ (prefixWord ++ tailWord_758241).sum := by decide
  have hdescent : baseEnd_758241 < baseStart_758241 := by decide
  rcases family_descends (prefixWord ++ tailWord_758241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758255 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 5]
def baseStart_758255 : Nat := 118140960795 + 758255 * 2 ^ 59
def prefixEnd_758255 : Nat := 4983230072969 + 3 ^ 40 * 758255 * 2
def baseEnd_758255 : Nat := 346088243266698717800315

theorem tailTrace_758255 : CollatzResearch.WordTrace tailWord_758255 prefixEnd_758255 346088243266698717800315 := by
  unfold tailWord_758255
  simp only [CollatzResearch.WordTrace]
  refine ⟨27655831867979109489116219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18437221245319406326077479 27655831867979109489116219)
  ·
    refine ⟨41483747801968664233674329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27655831867979109489116219 41483747801968664233674329)
    ·
      refine ⟨31112810851476498175255747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41483747801968664233674329 31112810851476498175255747)
      ·
        refine ⟨46669216277214747262883621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31112810851476498175255747 46669216277214747262883621)
        ·
          refine ⟨8750478051977765111790679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46669216277214747262883621 8750478051977765111790679)
          ·
            refine ⟨13125717077966647667686019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8750478051977765111790679 13125717077966647667686019)
            ·
              refine ⟨19688575616949971501529029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13125717077966647667686019 19688575616949971501529029)
              ·
                refine ⟨3691607928178119656536693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19688575616949971501529029 3691607928178119656536693)
                ·
                  refine ⟨346088243266698717800315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3691607928178119656536693 346088243266698717800315)
                  ·
                    rfl

theorem cell20_758255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_758255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758255 prefixEnd_758255 := by exact prefixLift 758255
  have htrace : WordTrace (prefixWord ++ tailWord_758255) baseStart_758255 baseEnd_758255 := by
    simpa [prefixWord, tailWord_758255, baseEnd_758255] using wordTrace_append hprefix tailTrace_758255
  have hstable : (prefixWord ++ tailWord_758255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758255).length < 2 ^ (prefixWord ++ tailWord_758255).sum := by decide
  have hdescent : baseEnd_758255 < baseStart_758255 := by decide
  rcases family_descends (prefixWord ++ tailWord_758255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758348 : List Nat := [2, 2, 1, 3, 1, 2, 3, 3, 3]
def baseStart_758348 : Nat := 118140960795 + 758348 * 2 ^ 59
def prefixEnd_758348 : Nat := 4983230072969 + 3 ^ 40 * 758348 * 2
def baseEnd_758348 : Nat := 346130691000803727699935

theorem tailTrace_758348 : CollatzResearch.WordTrace tailWord_758348 prefixEnd_758348 346130691000803727699935 := by
  unfold tailWord_758348
  simp only [CollatzResearch.WordTrace]
  refine ⟨13829611928321093186125849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18439482571094790914834465 13829611928321093186125849)
  ·
    refine ⟨10372208946240819889594387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13829611928321093186125849 10372208946240819889594387)
    ·
      refine ⟨15558313419361229834391581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10372208946240819889594387 15558313419361229834391581)
      ·
        refine ⟨5834367532260461187896843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15558313419361229834391581 5834367532260461187896843)
        ·
          refine ⟨8751551298390691781845265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5834367532260461187896843 8751551298390691781845265)
          ·
            refine ⟨6563663473793018836383949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8751551298390691781845265 6563663473793018836383949)
            ·
              refine ⟨2461373802672382063643981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6563663473793018836383949 2461373802672382063643981)
              ·
                refine ⟨923015176002143273866493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2461373802672382063643981 923015176002143273866493)
                ·
                  refine ⟨346130691000803727699935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923015176002143273866493 346130691000803727699935)
                  ·
                    rfl

theorem cell20_758348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_758348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758348 prefixEnd_758348 := by exact prefixLift 758348
  have htrace : WordTrace (prefixWord ++ tailWord_758348) baseStart_758348 baseEnd_758348 := by
    simpa [prefixWord, tailWord_758348, baseEnd_758348] using wordTrace_append hprefix tailTrace_758348
  have hstable : (prefixWord ++ tailWord_758348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758348).length < 2 ^ (prefixWord ++ tailWord_758348).sum := by decide
  have hdescent : baseEnd_758348 < baseStart_758348 := by decide
  rcases family_descends (prefixWord ++ tailWord_758348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758372 : List Nat := [2, 3, 1, 1, 2, 2, 2, 5, 2]
def baseStart_758372 : Nat := 118140960795 + 758372 * 2 ^ 59
def prefixEnd_758372 : Nat := 4983230072969 + 3 ^ 40 * 758372 * 2
def baseEnd_758372 : Nat := 346141645254766310899837

theorem tailTrace_758372 : CollatzResearch.WordTrace tailWord_758372 prefixEnd_758372 346141645254766310899837 := by
  unfold tailWord_758372
  simp only [CollatzResearch.WordTrace]
  refine ⟨13830049604277619235562685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18440066139036825647416913 13830049604277619235562685)
  ·
    refine ⟨5186268601604107213336007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13830049604277619235562685 5186268601604107213336007)
    ·
      refine ⟨7779402902406160820004011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5186268601604107213336007 7779402902406160820004011)
      ·
        refine ⟨11669104353609241230006017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7779402902406160820004011 11669104353609241230006017)
        ·
          refine ⟨8751828265206930922504513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11669104353609241230006017 8751828265206930922504513)
          ·
            refine ⟨6563871198905198191878385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8751828265206930922504513 6563871198905198191878385)
            ·
              refine ⟨4922903399178898643908789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6563871198905198191878385 4922903399178898643908789)
              ·
                refine ⟨461522193673021747866449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4922903399178898643908789 461522193673021747866449)
                ·
                  refine ⟨346141645254766310899837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461522193673021747866449 346141645254766310899837)
                  ·
                    rfl

theorem cell20_758372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_758372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758372 prefixEnd_758372 := by exact prefixLift 758372
  have htrace : WordTrace (prefixWord ++ tailWord_758372) baseStart_758372 baseEnd_758372 := by
    simpa [prefixWord, tailWord_758372, baseEnd_758372] using wordTrace_append hprefix tailTrace_758372
  have hstable : (prefixWord ++ tailWord_758372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758372).length < 2 ^ (prefixWord ++ tailWord_758372).sum := by decide
  have hdescent : baseEnd_758372 < baseStart_758372 := by decide
  rcases family_descends (prefixWord ++ tailWord_758372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758400 : List Nat := [2, 1, 1, 2, 1, 5, 3, 5]
def baseStart_758400 : Nat := 118140960795 + 758400 * 2 ^ 59
def prefixEnd_758400 : Nat := 4983230072969 + 3 ^ 40 * 758400 * 2
def baseEnd_758400 : Nat := 115384808405907552655463

theorem tailTrace_758400 : CollatzResearch.WordTrace tailWord_758400 prefixEnd_758400 115384808405907552655463 := by
  unfold tailWord_758400
  simp only [CollatzResearch.WordTrace]
  refine ⟨13830560226226899626572327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18440746968302532835429769 13830560226226899626572327)
  ·
    refine ⟨20745840339340349439858491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13830560226226899626572327 20745840339340349439858491)
    ·
      refine ⟨31118760509010524159787737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20745840339340349439858491 31118760509010524159787737)
      ·
        refine ⟨23339070381757893119840803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31118760509010524159787737 23339070381757893119840803)
        ·
          refine ⟨35008605572636839679761205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23339070381757893119840803 35008605572636839679761205)
          ·
            refine ⟨3282056772434703719977613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35008605572636839679761205 3282056772434703719977613)
            ·
              refine ⟨1230771289663013894991605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3282056772434703719977613 1230771289663013894991605)
              ·
                refine ⟨115384808405907552655463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1230771289663013894991605 115384808405907552655463)
                ·
                  rfl

theorem cell20_758400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_758400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758400 prefixEnd_758400 := by exact prefixLift 758400
  have htrace : WordTrace (prefixWord ++ tailWord_758400) baseStart_758400 baseEnd_758400 := by
    simpa [prefixWord, tailWord_758400, baseEnd_758400] using wordTrace_append hprefix tailTrace_758400
  have hstable : (prefixWord ++ tailWord_758400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758400).length < 2 ^ (prefixWord ++ tailWord_758400).sum := by decide
  have hdescent : baseEnd_758400 < baseStart_758400 := by decide
  rcases family_descends (prefixWord ++ tailWord_758400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758410 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 4]
def baseStart_758410 : Nat := 118140960795 + 758410 * 2 ^ 59
def prefixEnd_758410 : Nat := 4983230072969 + 3 ^ 40 * 758410 * 2
def baseEnd_758410 : Nat := 346158989490207067633015

theorem tailTrace_758410 : CollatzResearch.WordTrace tailWord_758410 prefixEnd_758410 346158989490207067633015 := by
  unfold tailWord_758410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6915371295604392740252171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18440990121611713974005789 6915371295604392740252171)
  ·
    refine ⟨10373056943406589110378257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6915371295604392740252171 10373056943406589110378257)
    ·
      refine ⟨7779792707554941832783693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10373056943406589110378257 7779792707554941832783693)
      ·
        refine ⟨2917422265333103187293885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7779792707554941832783693 2917422265333103187293885)
        ·
          refine ⟨1094033349499913695235207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2917422265333103187293885 1094033349499913695235207)
          ·
            refine ⟨1641050024249870542852811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094033349499913695235207 1641050024249870542852811)
            ·
              refine ⟨2461575036374805814279217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641050024249870542852811 2461575036374805814279217)
              ·
                refine ⟨1846181277281104360709413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2461575036374805814279217 1846181277281104360709413)
                ·
                  refine ⟨346158989490207067633015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1846181277281104360709413 346158989490207067633015)
                  ·
                    rfl

theorem cell20_758410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_758410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758410 prefixEnd_758410 := by exact prefixLift 758410
  have htrace : WordTrace (prefixWord ++ tailWord_758410) baseStart_758410 baseEnd_758410 := by
    simpa [prefixWord, tailWord_758410, baseEnd_758410] using wordTrace_append hprefix tailTrace_758410
  have hstable : (prefixWord ++ tailWord_758410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758410).length < 2 ^ (prefixWord ++ tailWord_758410).sum := by decide
  have hdescent : baseEnd_758410 < baseStart_758410 := by decide
  rcases family_descends (prefixWord ++ tailWord_758410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758482 : List Nat := [3, 2, 2, 2, 3, 2, 1, 3, 2]
def baseStart_758482 : Nat := 118140960795 + 758482 * 2 ^ 59
def prefixEnd_758482 : Nat := 4983230072969 + 3 ^ 40 * 758482 * 2
def baseEnd_758482 : Nat := 346191852252094817232721

theorem tailTrace_758482 : CollatzResearch.WordTrace tailWord_758482 prefixEnd_758482 346191852252094817232721 := by
  unfold tailWord_758482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6916027809539181814407425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18442740825437818171753133 6916027809539181814407425)
  ·
    refine ⟨5187020857154386360805569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6916027809539181814407425 5187020857154386360805569)
    ·
      refine ⟨3890265642865789770604177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5187020857154386360805569 3890265642865789770604177)
      ·
        refine ⟨2917699232149342327953133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3890265642865789770604177 2917699232149342327953133)
        ·
          refine ⟨1094137212056003372982425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2917699232149342327953133 1094137212056003372982425)
          ·
            refine ⟨820602909042002529736819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1094137212056003372982425 820602909042002529736819)
            ·
              refine ⟨1230904363563003794605229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 820602909042002529736819 1230904363563003794605229)
              ·
                refine ⟨461589136336126422976961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1230904363563003794605229 461589136336126422976961)
                ·
                  refine ⟨346191852252094817232721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461589136336126422976961 346191852252094817232721)
                  ·
                    rfl

theorem cell20_758482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_758482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758482 prefixEnd_758482 := by exact prefixLift 758482
  have htrace : WordTrace (prefixWord ++ tailWord_758482) baseStart_758482 baseEnd_758482 := by
    simpa [prefixWord, tailWord_758482, baseEnd_758482] using wordTrace_append hprefix tailTrace_758482
  have hstable : (prefixWord ++ tailWord_758482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758482).length < 2 ^ (prefixWord ++ tailWord_758482).sum := by decide
  have hdescent : baseEnd_758482 < baseStart_758482 := by decide
  rcases family_descends (prefixWord ++ tailWord_758482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758514 : List Nat := [3, 2, 1, 3, 1, 2, 1, 7]
def baseStart_758514 : Nat := 118140960795 + 758514 * 2 ^ 59
def prefixEnd_758514 : Nat := 4983230072969 + 3 ^ 40 * 758514 * 2
def baseEnd_758514 : Nat := 115402152641348309388641

theorem tailTrace_758514 : CollatzResearch.WordTrace tailWord_758514 prefixEnd_758514 115402152641348309388641 := by
  unfold tailWord_758514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6916319593510199180698649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18443518916027197815196397 6916319593510199180698649)
  ·
    refine ⟨5187239695132649385523987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6916319593510199180698649 5187239695132649385523987)
    ·
      refine ⟨7780859542698974078285981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5187239695132649385523987 7780859542698974078285981)
      ·
        refine ⟨2917822328512115279357243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7780859542698974078285981 2917822328512115279357243)
        ·
          refine ⟨4376733492768172919035865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2917822328512115279357243 4376733492768172919035865)
          ·
            refine ⟨3282550119576129689276899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4376733492768172919035865 3282550119576129689276899)
            ·
              refine ⟨4923825179364194533915349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282550119576129689276899 4923825179364194533915349)
              ·
                refine ⟨115402152641348309388641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4923825179364194533915349 115402152641348309388641)
                ·
                  rfl

theorem cell20_758514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_758514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758514 prefixEnd_758514 := by exact prefixLift 758514
  have htrace : WordTrace (prefixWord ++ tailWord_758514) baseStart_758514 baseEnd_758514 := by
    simpa [prefixWord, tailWord_758514, baseEnd_758514] using wordTrace_append hprefix tailTrace_758514
  have hstable : (prefixWord ++ tailWord_758514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758514).length < 2 ^ (prefixWord ++ tailWord_758514).sum := by decide
  have hdescent : baseEnd_758514 < baseStart_758514 := by decide
  rcases family_descends (prefixWord ++ tailWord_758514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758600 : List Nat := [2, 1, 3, 1, 1, 3, 4, 3, 2]
def baseStart_758600 : Nat := 118140960795 + 758600 * 2 ^ 59
def prefixEnd_758600 : Nat := 4983230072969 + 3 ^ 40 * 758600 * 2
def baseEnd_758600 : Nat := 346245710667410851298905

theorem tailTrace_758600 : CollatzResearch.WordTrace tailWord_758600 prefixEnd_758600 346245710667410851298905 := by
  unfold tailWord_758600
  simp only [CollatzResearch.WordTrace]
  refine ⟨13834207525864616705212627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18445610034486155606950169 13834207525864616705212627)
  ·
    refine ⟨20751311288796925057818941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13834207525864616705212627 20751311288796925057818941)
    ·
      refine ⟨7781741733298846896682103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20751311288796925057818941 7781741733298846896682103)
      ·
        refine ⟨11672612599948270345023155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7781741733298846896682103 11672612599948270345023155)
        ·
          refine ⟨17508918899922405517534733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11672612599948270345023155 17508918899922405517534733)
          ·
            refine ⟨6565844587470902069075525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17508918899922405517534733 6565844587470902069075525)
            ·
              refine ⟨1231095860150794137951661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6565844587470902069075525 1231095860150794137951661)
              ·
                refine ⟨461660947556547801731873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1231095860150794137951661 461660947556547801731873)
                ·
                  refine ⟨346245710667410851298905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461660947556547801731873 346245710667410851298905)
                  ·
                    rfl

theorem cell20_758600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 2].length) (baseStart_758600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758600 prefixEnd_758600 := by exact prefixLift 758600
  have htrace : WordTrace (prefixWord ++ tailWord_758600) baseStart_758600 baseEnd_758600 := by
    simpa [prefixWord, tailWord_758600, baseEnd_758600] using wordTrace_append hprefix tailTrace_758600
  have hstable : (prefixWord ++ tailWord_758600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758600).length < 2 ^ (prefixWord ++ tailWord_758600).sum := by decide
  have hdescent : baseEnd_758600 < baseStart_758600 := by decide
  rcases family_descends (prefixWord ++ tailWord_758600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758631 : List Nat := [1, 1, 5, 1, 2, 3, 3, 1, 3]
def baseStart_758631 : Nat := 118140960795 + 758631 * 2 ^ 59
def prefixEnd_758631 : Nat := 4983230072969 + 3 ^ 40 * 758631 * 2
def baseEnd_758631 : Nat := 346259859912112521265445

theorem tailTrace_758631 : CollatzResearch.WordTrace tailWord_758631 prefixEnd_758631 346259859912112521265445 := by
  unfold tailWord_758631
  simp only [CollatzResearch.WordTrace]
  refine ⟨27669545714616925704803747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18446363809744617136535831 27669545714616925704803747)
  ·
    refine ⟨41504318571925388557205621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27669545714616925704803747 41504318571925388557205621)
    ·
      refine ⟨3891029866118005177238027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41504318571925388557205621 3891029866118005177238027)
      ·
        refine ⟨5836544799177007765857041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3891029866118005177238027 5836544799177007765857041)
        ·
          refine ⟨4377408599382755824392781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5836544799177007765857041 4377408599382755824392781)
          ·
            refine ⟨1641528224768533434147293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4377408599382755824392781 1641528224768533434147293)
            ·
              refine ⟨615573084288200037805235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1641528224768533434147293 615573084288200037805235)
              ·
                refine ⟨923359626432300056707853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615573084288200037805235 923359626432300056707853)
                ·
                  refine ⟨346259859912112521265445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923359626432300056707853 346259859912112521265445)
                  ·
                    rfl

theorem cell20_758631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 3].length) (baseStart_758631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758631 prefixEnd_758631 := by exact prefixLift 758631
  have htrace : WordTrace (prefixWord ++ tailWord_758631) baseStart_758631 baseEnd_758631 := by
    simpa [prefixWord, tailWord_758631, baseEnd_758631] using wordTrace_append hprefix tailTrace_758631
  have hstable : (prefixWord ++ tailWord_758631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758631).length < 2 ^ (prefixWord ++ tailWord_758631).sum := by decide
  have hdescent : baseEnd_758631 < baseStart_758631 := by decide
  rcases family_descends (prefixWord ++ tailWord_758631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758635 : List Nat := [1, 1, 1, 1, 2, 2, 4, 5, 3]
def baseStart_758635 : Nat := 118140960795 + 758635 * 2 ^ 59
def prefixEnd_758635 : Nat := 4983230072969 + 3 ^ 40 * 758635 * 2
def baseEnd_758635 : Nat := 346261685621106285132095

theorem tailTrace_758635 : CollatzResearch.WordTrace tailWord_758635 prefixEnd_758635 346261685621106285132095 := by
  unfold tailWord_758635
  simp only [CollatzResearch.WordTrace]
  refine ⟨27669691606602434387949359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18446461071068289591966239 27669691606602434387949359)
  ·
    refine ⟨41504537409903651581924039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27669691606602434387949359 41504537409903651581924039)
    ·
      refine ⟨62256806114855477372886059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41504537409903651581924039 62256806114855477372886059)
      ·
        refine ⟨93385209172283216059329089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62256806114855477372886059 93385209172283216059329089)
        ·
          refine ⟨70038906879212412044496817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93385209172283216059329089 70038906879212412044496817)
          ·
            refine ⟨52529180159409309033372613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70038906879212412044496817 52529180159409309033372613)
            ·
              refine ⟨9849221279889245443757365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52529180159409309033372613 9849221279889245443757365)
              ·
                refine ⟨923364494989616760352253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9849221279889245443757365 923364494989616760352253)
                ·
                  refine ⟨346261685621106285132095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923364494989616760352253 346261685621106285132095)
                  ·
                    rfl

theorem cell20_758635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 3].length) (baseStart_758635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758635 prefixEnd_758635 := by exact prefixLift 758635
  have htrace : WordTrace (prefixWord ++ tailWord_758635) baseStart_758635 baseEnd_758635 := by
    simpa [prefixWord, tailWord_758635, baseEnd_758635] using wordTrace_append hprefix tailTrace_758635
  have hstable : (prefixWord ++ tailWord_758635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758635).length < 2 ^ (prefixWord ++ tailWord_758635).sum := by decide
  have hdescent : baseEnd_758635 < baseStart_758635 := by decide
  rcases family_descends (prefixWord ++ tailWord_758635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758645 : List Nat := [1, 3, 4, 1, 1, 2, 4, 4]
def baseStart_758645 : Nat := 118140960795 + 758645 * 2 ^ 59
def prefixEnd_758645 : Nat := 4983230072969 + 3 ^ 40 * 758645 * 2
def baseEnd_758645 : Nat := 115422083297863564932907

theorem tailTrace_758645 : CollatzResearch.WordTrace tailWord_758645 prefixEnd_758645 115422083297863564932907 := by
  unfold tailWord_758645
  simp only [CollatzResearch.WordTrace]
  refine ⟨27670056336566206095813389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18446704224377470730542259 27670056336566206095813389)
  ·
    refine ⟨10376271126212327285930021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27670056336566206095813389 10376271126212327285930021)
    ·
      refine ⟨1945550836164811366111879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10376271126212327285930021 1945550836164811366111879)
      ·
        refine ⟨2918326254247217049167819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1945550836164811366111879 2918326254247217049167819)
        ·
          refine ⟨4377489381370825573751729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2918326254247217049167819 4377489381370825573751729)
          ·
            refine ⟨3283117036028119180313797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4377489381370825573751729 3283117036028119180313797)
            ·
              refine ⟨615584444255272346308837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3283117036028119180313797 615584444255272346308837)
              ·
                refine ⟨115422083297863564932907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 615584444255272346308837 115422083297863564932907)
                ·
                  rfl

theorem cell20_758645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 4].length) (baseStart_758645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758645 prefixEnd_758645 := by exact prefixLift 758645
  have htrace : WordTrace (prefixWord ++ tailWord_758645) baseStart_758645 baseEnd_758645 := by
    simpa [prefixWord, tailWord_758645, baseEnd_758645] using wordTrace_append hprefix tailTrace_758645
  have hstable : (prefixWord ++ tailWord_758645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758645).length < 2 ^ (prefixWord ++ tailWord_758645).sum := by decide
  have hdescent : baseEnd_758645 < baseStart_758645 := by decide
  rcases family_descends (prefixWord ++ tailWord_758645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758666 : List Nat := [3, 1, 2, 4, 1, 1, 8]
def baseStart_758666 : Nat := 118140960795 + 758666 * 2 ^ 59
def prefixEnd_758666 : Nat := 4983230072969 + 3 ^ 40 * 758666 * 2
def baseEnd_758666 : Nat := 38475092762867550566515

theorem tailTrace_758666 : CollatzResearch.WordTrace tailWord_758666 prefixEnd_758666 38475092762867550566515 := by
  unfold tailWord_758666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6917705567372531670581963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18447214846326751121551901 6917705567372531670581963)
  ·
    refine ⟨10376558351058797505872945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6917705567372531670581963 10376558351058797505872945)
    ·
      refine ⟨7782418763294098129404709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10376558351058797505872945 7782418763294098129404709)
      ·
        refine ⟨1459203518117643399263383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7782418763294098129404709 1459203518117643399263383)
        ·
          refine ⟨2188805277176465098895075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459203518117643399263383 2188805277176465098895075)
          ·
            refine ⟨3283207915764697648342613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188805277176465098895075 3283207915764697648342613)
            ·
              refine ⟨38475092762867550566515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3283207915764697648342613 38475092762867550566515)
              ·
                rfl

theorem cell20_758666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 8].length) (baseStart_758666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758666 prefixEnd_758666 := by exact prefixLift 758666
  have htrace : WordTrace (prefixWord ++ tailWord_758666) baseStart_758666 baseEnd_758666 := by
    simpa [prefixWord, tailWord_758666, baseEnd_758666] using wordTrace_append hprefix tailTrace_758666
  have hstable : (prefixWord ++ tailWord_758666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758666).length < 2 ^ (prefixWord ++ tailWord_758666).sum := by decide
  have hdescent : baseEnd_758666 < baseStart_758666 := by decide
  rcases family_descends (prefixWord ++ tailWord_758666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758673 : List Nat := [1, 2, 2, 1, 1, 1, 3, 6, 3]
def baseStart_758673 : Nat := 118140960795 + 758673 * 2 ^ 59
def prefixEnd_758673 : Nat := 4983230072969 + 3 ^ 40 * 758673 * 2
def baseEnd_758673 : Nat := 346279029856547041865273

theorem tailTrace_758673 : CollatzResearch.WordTrace tailWord_758673 prefixEnd_758673 346279029856547041865273 := by
  unfold tailWord_758673
  simp only [CollatzResearch.WordTrace]
  refine ⟨27671077580464766877832673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18447385053643177918555115 27671077580464766877832673)
  ·
    refine ⟨20753308185348575158374505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27671077580464766877832673 20753308185348575158374505)
    ·
      refine ⟨15564981139011431368780879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20753308185348575158374505 15564981139011431368780879)
      ·
        refine ⟨23347471708517147053171319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15564981139011431368780879 23347471708517147053171319)
        ·
          refine ⟨35021207562775720579756979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23347471708517147053171319 35021207562775720579756979)
          ·
            refine ⟨52531811344163580869635469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35021207562775720579756979 52531811344163580869635469)
            ·
              refine ⟨19699429254061342826113301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52531811344163580869635469 19699429254061342826113301)
              ·
                refine ⟨923410746284125444974061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19699429254061342826113301 923410746284125444974061)
                ·
                  refine ⟨346279029856547041865273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923410746284125444974061 346279029856547041865273)
                  ·
                    rfl

theorem cell20_758673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_758673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758673 prefixEnd_758673 := by exact prefixLift 758673
  have htrace : WordTrace (prefixWord ++ tailWord_758673) baseStart_758673 baseEnd_758673 := by
    simpa [prefixWord, tailWord_758673, baseEnd_758673] using wordTrace_append hprefix tailTrace_758673
  have hstable : (prefixWord ++ tailWord_758673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758673).length < 2 ^ (prefixWord ++ tailWord_758673).sum := by decide
  have hdescent : baseEnd_758673 < baseStart_758673 := by decide
  rcases family_descends (prefixWord ++ tailWord_758673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758724 : List Nat := [2, 3, 3, 3, 1, 1, 2, 2, 3]
def baseStart_758724 : Nat := 118140960795 + 758724 * 2 ^ 59
def prefixEnd_758724 : Nat := 4983230072969 + 3 ^ 40 * 758724 * 2
def baseEnd_758724 : Nat := 346302307646217531165065

theorem tailTrace_758724 : CollatzResearch.WordTrace tailWord_758724 prefixEnd_758724 346302307646217531165065 := by
  unfold tailWord_758724
  simp only [CollatzResearch.WordTrace]
  refine ⟨13836468851640001293969613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18448625135520001725292817 13836468851640001293969613)
  ·
    refine ⟨5188675819365000485238605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13836468851640001293969613 5188675819365000485238605)
    ·
      refine ⟨1945753432261875181964477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5188675819365000485238605 1945753432261875181964477)
      ·
        refine ⟨729657537098203193236679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1945753432261875181964477 729657537098203193236679)
        ·
          refine ⟨1094486305647304789855019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729657537098203193236679 1094486305647304789855019)
          ·
            refine ⟨1641729458470957184782529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094486305647304789855019 1641729458470957184782529)
            ·
              refine ⟨1231297093853217888586897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1641729458470957184782529 1231297093853217888586897)
              ·
                refine ⟨923472820389913416440173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1231297093853217888586897 923472820389913416440173)
                ·
                  refine ⟨346302307646217531165065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923472820389913416440173 346302307646217531165065)
                  ·
                    rfl

theorem cell20_758724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_758724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758724 prefixEnd_758724 := by exact prefixLift 758724
  have htrace : WordTrace (prefixWord ++ tailWord_758724) baseStart_758724 baseEnd_758724 := by
    simpa [prefixWord, tailWord_758724, baseEnd_758724] using wordTrace_append hprefix tailTrace_758724
  have hstable : (prefixWord ++ tailWord_758724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758724).length < 2 ^ (prefixWord ++ tailWord_758724).sum := by decide
  have hdescent : baseEnd_758724 < baseStart_758724 := by decide
  rcases family_descends (prefixWord ++ tailWord_758724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758731 : List Nat := [1, 1, 1, 1, 3, 7, 2, 2, 2]
def baseStart_758731 : Nat := 118140960795 + 758731 * 2 ^ 59
def prefixEnd_758731 : Nat := 4983230072969 + 3 ^ 40 * 758731 * 2
def baseEnd_758731 : Nat := 346305502636956617931703

theorem tailTrace_758731 : CollatzResearch.WordTrace tailWord_758731 prefixEnd_758731 346305502636956617931703 := by
  unfold tailWord_758731
  simp only [CollatzResearch.WordTrace]
  refine ⟨27673193014254642783444047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18448795342836428522296031 27673193014254642783444047)
  ·
    refine ⟨41509789521381964175166071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27673193014254642783444047 41509789521381964175166071)
    ·
      refine ⟨62264684282072946262749107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41509789521381964175166071 62264684282072946262749107)
      ·
        refine ⟨93397026423109419394123661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62264684282072946262749107 93397026423109419394123661)
        ·
          refine ⟨35023884908666032272796373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93397026423109419394123661 35023884908666032272796373)
          ·
            refine ⟨820872302546860131393665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35023884908666032272796373 820872302546860131393665)
            ·
              refine ⟨615654226910145098545249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820872302546860131393665 615654226910145098545249)
              ·
                refine ⟨461740670182608823908937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615654226910145098545249 461740670182608823908937)
                ·
                  refine ⟨346305502636956617931703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461740670182608823908937 346305502636956617931703)
                  ·
                    rfl

theorem cell20_758731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 2].length) (baseStart_758731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758731 prefixEnd_758731 := by exact prefixLift 758731
  have htrace : WordTrace (prefixWord ++ tailWord_758731) baseStart_758731 baseEnd_758731 := by
    simpa [prefixWord, tailWord_758731, baseEnd_758731] using wordTrace_append hprefix tailTrace_758731
  have hstable : (prefixWord ++ tailWord_758731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758731).length < 2 ^ (prefixWord ++ tailWord_758731).sum := by decide
  have hdescent : baseEnd_758731 < baseStart_758731 := by decide
  rcases family_descends (prefixWord ++ tailWord_758731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758759 : List Nat := [1, 1, 5, 2, 2, 2, 3, 4]
def baseStart_758759 : Nat := 118140960795 + 758759 * 2 ^ 59
def prefixEnd_758759 : Nat := 4983230072969 + 3 ^ 40 * 758759 * 2
def baseEnd_758759 : Nat := 115439427533304321666085

theorem tailTrace_758759 : CollatzResearch.WordTrace tailWord_758759 prefixEnd_758759 115439427533304321666085 := by
  unfold tailWord_758759
  simp only [CollatzResearch.WordTrace]
  refine ⟨27674214258153203565463331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18449476172102135710308887 27674214258153203565463331)
  ·
    refine ⟨41511321387229805348194997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27674214258153203565463331 41511321387229805348194997)
    ·
      refine ⟨3891686380052794251393281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41511321387229805348194997 3891686380052794251393281)
      ·
        refine ⟨2918764785039595688544961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3891686380052794251393281 2918764785039595688544961)
        ·
          refine ⟨2189073588779696766408721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2918764785039595688544961 2189073588779696766408721)
          ·
            refine ⟨1641805191584772574806541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2189073588779696766408721 1641805191584772574806541)
            ·
              refine ⟨615676946844289715552453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1641805191584772574806541 615676946844289715552453)
              ·
                refine ⟨115439427533304321666085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 615676946844289715552453 115439427533304321666085)
                ·
                  rfl

theorem cell20_758759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 4].length) (baseStart_758759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758759 prefixEnd_758759 := by exact prefixLift 758759
  have htrace : WordTrace (prefixWord ++ tailWord_758759) baseStart_758759 baseEnd_758759 := by
    simpa [prefixWord, tailWord_758759, baseEnd_758759] using wordTrace_append hprefix tailTrace_758759
  have hstable : (prefixWord ++ tailWord_758759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758759).length < 2 ^ (prefixWord ++ tailWord_758759).sum := by decide
  have hdescent : baseEnd_758759 < baseStart_758759 := by decide
  rcases family_descends (prefixWord ++ tailWord_758759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758818 : List Nat := [3, 3, 1, 1, 1, 4, 1, 6]
def baseStart_758818 : Nat := 118140960795 + 758818 * 2 ^ 59
def prefixEnd_758818 : Nat := 4983230072969 + 3 ^ 40 * 758818 * 2
def baseEnd_758818 : Nat := 115448403935856994010449

theorem tailTrace_758818 : CollatzResearch.WordTrace tailWord_758818 prefixEnd_758818 115448403935856994010449 := by
  unfold tailWord_758818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6919091541234864160465277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18450910776626304427907405 6919091541234864160465277)
  ·
    refine ⟨2594659327963074060174479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6919091541234864160465277 2594659327963074060174479)
    ·
      refine ⟨3891988991944611090261719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2594659327963074060174479 3891988991944611090261719)
      ·
        refine ⟨5837983487916916635392579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3891988991944611090261719 5837983487916916635392579)
        ·
          refine ⟨8756975231875374953088869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5837983487916916635392579 8756975231875374953088869)
          ·
            refine ⟨1641932855976632803704163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8756975231875374953088869 1641932855976632803704163)
            ·
              refine ⟨2462899283964949205556245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641932855976632803704163 2462899283964949205556245)
              ·
                refine ⟨115448403935856994010449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2462899283964949205556245 115448403935856994010449)
                ·
                  rfl

theorem cell20_758818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_758818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758818 prefixEnd_758818 := by exact prefixLift 758818
  have htrace : WordTrace (prefixWord ++ tailWord_758818) baseStart_758818 baseEnd_758818 := by
    simpa [prefixWord, tailWord_758818, baseEnd_758818] using wordTrace_append hprefix tailTrace_758818
  have hstable : (prefixWord ++ tailWord_758818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758818).length < 2 ^ (prefixWord ++ tailWord_758818).sum := by decide
  have hdescent : baseEnd_758818 < baseStart_758818 := by decide
  rcases family_descends (prefixWord ++ tailWord_758818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758845 : List Nat := [1, 4, 1, 3, 1, 3, 3, 2, 2]
def baseStart_758845 : Nat := 118140960795 + 758845 * 2 ^ 59
def prefixEnd_758845 : Nat := 4983230072969 + 3 ^ 40 * 758845 * 2
def baseEnd_758845 : Nat := 346357535343278888131237

theorem tailTrace_758845 : CollatzResearch.WordTrace tailWord_758845 prefixEnd_758845 346357535343278888131237 := by
  unfold tailWord_758845
  simp only [CollatzResearch.WordTrace]
  refine ⟨27677350935841640253093989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18451567290561093502062659 27677350935841640253093989)
  ·
    refine ⟨5189503300470307547455123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27677350935841640253093989 5189503300470307547455123)
    ·
      refine ⟨7784254950705461321182685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5189503300470307547455123 7784254950705461321182685)
      ·
        refine ⟨2919095606514547995443507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7784254950705461321182685 2919095606514547995443507)
        ·
          refine ⟨4378643409771821993165261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2919095606514547995443507 4378643409771821993165261)
          ·
            refine ⟨1641991278664433247436973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4378643409771821993165261 1641991278664433247436973)
            ·
              refine ⟨615746729499162467788865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1641991278664433247436973 615746729499162467788865)
              ·
                refine ⟨461810047124371850841649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615746729499162467788865 461810047124371850841649)
                ·
                  refine ⟨346357535343278888131237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461810047124371850841649 346357535343278888131237)
                  ·
                    rfl

theorem cell20_758845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_758845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758845 prefixEnd_758845 := by exact prefixLift 758845
  have htrace : WordTrace (prefixWord ++ tailWord_758845) baseStart_758845 baseEnd_758845 := by
    simpa [prefixWord, tailWord_758845, baseEnd_758845] using wordTrace_append hprefix tailTrace_758845
  have hstable : (prefixWord ++ tailWord_758845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758845).length < 2 ^ (prefixWord ++ tailWord_758845).sum := by decide
  have hdescent : baseEnd_758845 < baseStart_758845 := by decide
  rcases family_descends (prefixWord ++ tailWord_758845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758904 : List Nat := [2, 1, 2, 1, 1, 1, 8, 2, 2]
def baseStart_758904 : Nat := 118140960795 + 758904 * 2 ^ 59
def prefixEnd_758904 : Nat := 4983230072969 + 3 ^ 40 * 758904 * 2
def baseEnd_758904 : Nat := 346384464550936905164329

theorem tailTrace_758904 : CollatzResearch.WordTrace tailWord_758904 prefixEnd_758904 346384464550936905164329 := by
  unfold tailWord_758904
  simp only [CollatzResearch.WordTrace]
  refine ⟨13839751421313946664745883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18453001895085262219661177 13839751421313946664745883)
  ·
    refine ⟨20759627131970919997118825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13839751421313946664745883 20759627131970919997118825)
    ·
      refine ⟨15569720348978189997839119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20759627131970919997118825 15569720348978189997839119)
      ·
        refine ⟨23354580523467284996758679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15569720348978189997839119 23354580523467284996758679)
        ·
          refine ⟨35031870785200927495138019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23354580523467284996758679 35031870785200927495138019)
          ·
            refine ⟨52547806177801391242707029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35031870785200927495138019 52547806177801391242707029)
            ·
              refine ⟨615794603646110053625473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 52547806177801391242707029 615794603646110053625473)
              ·
                refine ⟨461845952734582540219105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615794603646110053625473 461845952734582540219105)
                ·
                  refine ⟨346384464550936905164329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461845952734582540219105 346384464550936905164329)
                  ·
                    rfl

theorem cell20_758904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 2].length) (baseStart_758904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758904 prefixEnd_758904 := by exact prefixLift 758904
  have htrace : WordTrace (prefixWord ++ tailWord_758904) baseStart_758904 baseEnd_758904 := by
    simpa [prefixWord, tailWord_758904, baseEnd_758904] using wordTrace_append hprefix tailTrace_758904
  have hstable : (prefixWord ++ tailWord_758904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758904).length < 2 ^ (prefixWord ++ tailWord_758904).sum := by decide
  have hdescent : baseEnd_758904 < baseStart_758904 := by decide
  rcases family_descends (prefixWord ++ tailWord_758904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758908 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 4]
def baseStart_758908 : Nat := 118140960795 + 758908 * 2 ^ 59
def prefixEnd_758908 : Nat := 4983230072969 + 3 ^ 40 * 758908 * 2
def baseEnd_758908 : Nat := 346386290259930669030979

theorem tailTrace_758908 : CollatzResearch.WordTrace tailWord_758908 prefixEnd_758908 346386290259930669030979 := by
  unfold tailWord_758908
  simp only [CollatzResearch.WordTrace]
  refine ⟨13839824367306701006318689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18453099156408934675091585 13839824367306701006318689)
  ·
    refine ⟨10379868275480025754739017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13839824367306701006318689 10379868275480025754739017)
    ·
      refine ⟨7784901206610019316054263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10379868275480025754739017 7784901206610019316054263)
      ·
        refine ⟨11677351809915028974081395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7784901206610019316054263 11677351809915028974081395)
        ·
          refine ⟨17516027714872543461122093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11677351809915028974081395 17516027714872543461122093)
          ·
            refine ⟨6568510393077203797920785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17516027714872543461122093 6568510393077203797920785)
            ·
              refine ⟨4926382794807902848440589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6568510393077203797920785 4926382794807902848440589)
              ·
                refine ⟨1847393548052963568165221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4926382794807902848440589 1847393548052963568165221)
                ·
                  refine ⟨346386290259930669030979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1847393548052963568165221 346386290259930669030979)
                  ·
                    rfl

theorem cell20_758908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_758908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758908 prefixEnd_758908 := by exact prefixLift 758908
  have htrace : WordTrace (prefixWord ++ tailWord_758908) baseStart_758908 baseEnd_758908 := by
    simpa [prefixWord, tailWord_758908, baseEnd_758908] using wordTrace_append hprefix tailTrace_758908
  have hstable : (prefixWord ++ tailWord_758908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758908).length < 2 ^ (prefixWord ++ tailWord_758908).sum := by decide
  have hdescent : baseEnd_758908 < baseStart_758908 := by decide
  rcases family_descends (prefixWord ++ tailWord_758908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758960 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_758960 : Nat := 118140960795 + 758960 * 2 ^ 59
def prefixEnd_758960 : Nat := 4983230072969 + 3 ^ 40 * 758960 * 2
def baseEnd_758960 : Nat := 346410024476849599297433

theorem tailTrace_758960 : CollatzResearch.WordTrace tailWord_758960 prefixEnd_758960 346410024476849599297433 := by
  unfold tailWord_758960
  simp only [CollatzResearch.WordTrace]
  refine ⟨13840772665212507446765167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18454363553616676595686889 13840772665212507446765167)
  ·
    refine ⟨20761158997818761170147751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13840772665212507446765167 20761158997818761170147751)
    ·
      refine ⟨31141738496728141755221627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20761158997818761170147751 31141738496728141755221627)
      ·
        refine ⟨46712607745092212632832441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31141738496728141755221627 46712607745092212632832441)
        ·
          refine ⟨35034455808819159474624331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46712607745092212632832441 35034455808819159474624331)
          ·
            refine ⟨52551683713228739211936497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35034455808819159474624331 52551683713228739211936497)
            ·
              refine ⟨39413762784921554408952373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52551683713228739211936497 39413762784921554408952373)
              ·
                refine ⟨3695040261086395725839285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39413762784921554408952373 3695040261086395725839285)
                ·
                  refine ⟨346410024476849599297433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3695040261086395725839285 346410024476849599297433)
                  ·
                    rfl

theorem cell20_758960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_758960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758960 prefixEnd_758960 := by exact prefixLift 758960
  have htrace : WordTrace (prefixWord ++ tailWord_758960) baseStart_758960 baseEnd_758960 := by
    simpa [prefixWord, tailWord_758960, baseEnd_758960] using wordTrace_append hprefix tailTrace_758960
  have hstable : (prefixWord ++ tailWord_758960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758960).length < 2 ^ (prefixWord ++ tailWord_758960).sum := by decide
  have hdescent : baseEnd_758960 < baseStart_758960 := by decide
  rcases family_descends (prefixWord ++ tailWord_758960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758963 : List Nat := [1, 1, 1, 2, 3, 2, 4, 4, 2]
def baseStart_758963 : Nat := 118140960795 + 758963 * 2 ^ 59
def prefixEnd_758963 : Nat := 4983230072969 + 3 ^ 40 * 758963 * 2
def baseEnd_758963 : Nat := 346411393758594922197421

theorem tailTrace_758963 : CollatzResearch.WordTrace tailWord_758963 prefixEnd_758963 346411393758594922197421 := by
  unfold tailWord_758963
  simp only [CollatzResearch.WordTrace]
  refine ⟨27681654749414146405889543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18454436499609430937259695 27681654749414146405889543)
  ·
    refine ⟨41522482124121219608834315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27681654749414146405889543 41522482124121219608834315)
    ·
      refine ⟨62283723186181829413251473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41522482124121219608834315 62283723186181829413251473)
      ·
        refine ⟨46712792389636372059938605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62283723186181829413251473 46712792389636372059938605)
        ·
          refine ⟨17517297146113639522476977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46712792389636372059938605 17517297146113639522476977)
          ·
            refine ⟨13137972859585229641857733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17517297146113639522476977 13137972859585229641857733)
            ·
              refine ⟨2463369911172230557848325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13137972859585229641857733 2463369911172230557848325)
              ·
                refine ⟨461881858344793229596561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2463369911172230557848325 461881858344793229596561)
                ·
                  refine ⟨346411393758594922197421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461881858344793229596561 346411393758594922197421)
                  ·
                    rfl

theorem cell20_758963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 2].length) (baseStart_758963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758963 prefixEnd_758963 := by exact prefixLift 758963
  have htrace : WordTrace (prefixWord ++ tailWord_758963) baseStart_758963 baseEnd_758963 := by
    simpa [prefixWord, tailWord_758963, baseEnd_758963] using wordTrace_append hprefix tailTrace_758963
  have hstable : (prefixWord ++ tailWord_758963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758963).length < 2 ^ (prefixWord ++ tailWord_758963).sum := by decide
  have hdescent : baseEnd_758963 < baseStart_758963 := by decide
  rcases family_descends (prefixWord ++ tailWord_758963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758984 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 4]
def baseStart_758984 : Nat := 118140960795 + 758984 * 2 ^ 59
def prefixEnd_758984 : Nat := 4983230072969 + 3 ^ 40 * 758984 * 2
def baseEnd_758984 : Nat := 346420978730812182497335

theorem tailTrace_758984 : CollatzResearch.WordTrace tailWord_758984 prefixEnd_758984 346420978730812182497335 := by
  unfold tailWord_758984
  simp only [CollatzResearch.WordTrace]
  refine ⟨13841210341169033496202003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18454947121558711328269337 13841210341169033496202003)
  ·
    refine ⟨20761815511753550244303005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13841210341169033496202003 20761815511753550244303005)
    ·
      refine ⟨7785680816907581341613627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20761815511753550244303005 7785680816907581341613627)
      ·
        refine ⟨11678521225361372012420441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7785680816907581341613627 11678521225361372012420441)
        ·
          refine ⟨8758890919021029009315331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11678521225361372012420441 8758890919021029009315331)
          ·
            refine ⟨13138336378531543513972997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8758890919021029009315331 13138336378531543513972997)
            ·
              refine ⟨2463438070974664408869937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13138336378531543513972997 2463438070974664408869937)
              ·
                refine ⟨1847578553230998306652453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2463438070974664408869937 1847578553230998306652453)
                ·
                  refine ⟨346420978730812182497335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1847578553230998306652453 346420978730812182497335)
                  ·
                    rfl

theorem cell20_758984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_758984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758984 prefixEnd_758984 := by exact prefixLift 758984
  have htrace : WordTrace (prefixWord ++ tailWord_758984) baseStart_758984 baseEnd_758984 := by
    simpa [prefixWord, tailWord_758984, baseEnd_758984] using wordTrace_append hprefix tailTrace_758984
  have hstable : (prefixWord ++ tailWord_758984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758984).length < 2 ^ (prefixWord ++ tailWord_758984).sum := by decide
  have hdescent : baseEnd_758984 < baseStart_758984 := by decide
  rcases family_descends (prefixWord ++ tailWord_758984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758997 : List Nat := [1, 3, 2, 4, 1, 3, 1, 3, 2]
def baseStart_758997 : Nat := 118140960795 + 758997 * 2 ^ 59
def prefixEnd_758997 : Nat := 4983230072969 + 3 ^ 40 * 758997 * 2
def baseEnd_758997 : Nat := 346426912285041915063949

theorem tailTrace_758997 : CollatzResearch.WordTrace tailWord_758997 prefixEnd_758997 346426912285041915063949 := by
  unfold tailWord_758997
  simp only [CollatzResearch.WordTrace]
  refine ⟨27682894831290970212627245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18455263220860646808418163 27682894831290970212627245)
  ·
    refine ⟨10381085561734113829735217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27682894831290970212627245 10381085561734113829735217)
    ·
      refine ⟨7785814171300585372301413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10381085561734113829735217 7785814171300585372301413)
      ·
        refine ⟨1459840157118859757306515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7785814171300585372301413 1459840157118859757306515)
        ·
          refine ⟨2189760235678289635959773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459840157118859757306515 2189760235678289635959773)
          ·
            refine ⟨821160088379358613484915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2189760235678289635959773 821160088379358613484915)
            ·
              refine ⟨1231740132569037920227373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821160088379358613484915 1231740132569037920227373)
              ·
                refine ⟨461902549713389220085265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1231740132569037920227373 461902549713389220085265)
                ·
                  refine ⟨346426912285041915063949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461902549713389220085265 346426912285041915063949)
                  ·
                    rfl

theorem cell20_758997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_758997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_758997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_758997 prefixEnd_758997 := by exact prefixLift 758997
  have htrace : WordTrace (prefixWord ++ tailWord_758997) baseStart_758997 baseEnd_758997 := by
    simpa [prefixWord, tailWord_758997, baseEnd_758997] using wordTrace_append hprefix tailTrace_758997
  have hstable : (prefixWord ++ tailWord_758997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758997).length < 2 ^ (prefixWord ++ tailWord_758997).sum := by decide
  have hdescent : baseEnd_758997 < baseStart_758997 := by decide
  rcases family_descends (prefixWord ++ tailWord_758997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759091 : List Nat := [1, 1, 1, 2, 5, 2, 2, 3, 3]
def baseStart_759091 : Nat := 118140960795 + 759091 * 2 ^ 59
def prefixEnd_759091 : Nat := 4983230072969 + 3 ^ 40 * 759091 * 2
def baseEnd_759091 : Nat := 346469816446395365930231

theorem tailTrace_759091 : CollatzResearch.WordTrace tailWord_759091 prefixEnd_759091 346469816446395365930231 := by
  unfold tailWord_759091
  simp only [CollatzResearch.WordTrace]
  refine ⟨27686323292950424266549127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18457548861966949511032751 27686323292950424266549127)
  ·
    refine ⟨41529484939425636399823691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27686323292950424266549127 41529484939425636399823691)
    ·
      refine ⟨62294227409138454599735537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41529484939425636399823691 62294227409138454599735537)
      ·
        refine ⟨46720670556853840949801653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62294227409138454599735537 46720670556853840949801653)
        ·
          refine ⟨4380062864705047589043905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46720670556853840949801653 4380062864705047589043905)
          ·
            refine ⟨3285047148528785691782929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4380062864705047589043905 3285047148528785691782929)
            ·
              refine ⟨2463785361396589268837197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3285047148528785691782929 2463785361396589268837197)
              ·
                refine ⟨923919510523720975813949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2463785361396589268837197 923919510523720975813949)
                ·
                  refine ⟨346469816446395365930231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923919510523720975813949 346469816446395365930231)
                  ·
                    rfl

theorem cell20_759091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 3].length) (baseStart_759091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759091 prefixEnd_759091 := by exact prefixLift 759091
  have htrace : WordTrace (prefixWord ++ tailWord_759091) baseStart_759091 baseEnd_759091 := by
    simpa [prefixWord, tailWord_759091, baseEnd_759091] using wordTrace_append hprefix tailTrace_759091
  have hstable : (prefixWord ++ tailWord_759091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759091).length < 2 ^ (prefixWord ++ tailWord_759091).sum := by decide
  have hdescent : baseEnd_759091 < baseStart_759091 := by decide
  rcases family_descends (prefixWord ++ tailWord_759091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759098 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_759098 : Nat := 118140960795 + 759098 * 2 ^ 59
def prefixEnd_759098 : Nat := 4983230072969 + 3 ^ 40 * 759098 * 2
def baseEnd_759098 : Nat := 346473011437134452696869

theorem tailTrace_759098 : CollatzResearch.WordTrace tailWord_759098 prefixEnd_759098 346473011437134452696869 := by
  unfold tailWord_759098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6921644650981266115513487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18457719069283376308035965 6921644650981266115513487)
  ·
    refine ⟨10382466976471899173270231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6921644650981266115513487 10382466976471899173270231)
    ·
      refine ⟨15573700464707848759905347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10382466976471899173270231 15573700464707848759905347)
      ·
        refine ⟨23360550697061773139858021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15573700464707848759905347 23360550697061773139858021)
        ·
          refine ⟨4380103255699082463723379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23360550697061773139858021 4380103255699082463723379)
          ·
            refine ⟨6570154883548623695585069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4380103255699082463723379 6570154883548623695585069)
            ·
              refine ⟨2463808081330733885844401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6570154883548623695585069 2463808081330733885844401)
              ·
                refine ⟨1847856060998050414383301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2463808081330733885844401 1847856060998050414383301)
                ·
                  refine ⟨346473011437134452696869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1847856060998050414383301 346473011437134452696869)
                  ·
                    rfl

theorem cell20_759098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_759098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759098 prefixEnd_759098 := by exact prefixLift 759098
  have htrace : WordTrace (prefixWord ++ tailWord_759098) baseStart_759098 baseEnd_759098 := by
    simpa [prefixWord, tailWord_759098, baseEnd_759098] using wordTrace_append hprefix tailTrace_759098
  have hstable : (prefixWord ++ tailWord_759098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759098).length < 2 ^ (prefixWord ++ tailWord_759098).sum := by decide
  have hdescent : baseEnd_759098 < baseStart_759098 := by decide
  rcases family_descends (prefixWord ++ tailWord_759098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759112 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_759112 : Nat := 118140960795 + 759112 * 2 ^ 59
def prefixEnd_759112 : Nat := 4983230072969 + 3 ^ 40 * 759112 * 2
def baseEnd_759112 : Nat := 346479401418612626230145

theorem tailTrace_759112 : CollatzResearch.WordTrace tailWord_759112 prefixEnd_759112 346479401418612626230145 := by
  unfold tailWord_759112
  simp only [CollatzResearch.WordTrace]
  refine ⟨13843544612937172426531795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18458059483916229902042393 13843544612937172426531795)
  ·
    refine ⟨20765316919405758639797693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13843544612937172426531795 20765316919405758639797693)
    ·
      refine ⟨7786993844777159489924135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20765316919405758639797693 7786993844777159489924135)
      ·
        refine ⟨11680490767165739234886203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7786993844777159489924135 11680490767165739234886203)
        ·
          refine ⟨17520736150748608852329305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11680490767165739234886203 17520736150748608852329305)
          ·
            refine ⟨13140552113061456639246979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17520736150748608852329305 13140552113061456639246979)
            ·
              refine ⟨19710828169592184958870469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13140552113061456639246979 19710828169592184958870469)
              ·
                refine ⟨3695780281798534679788213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19710828169592184958870469 3695780281798534679788213)
                ·
                  refine ⟨346479401418612626230145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3695780281798534679788213 346479401418612626230145)
                  ·
                    rfl

theorem cell20_759112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_759112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759112 prefixEnd_759112 := by exact prefixLift 759112
  have htrace : WordTrace (prefixWord ++ tailWord_759112) baseStart_759112 baseEnd_759112 := by
    simpa [prefixWord, tailWord_759112, baseEnd_759112] using wordTrace_append hprefix tailTrace_759112
  have hstable : (prefixWord ++ tailWord_759112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759112).length < 2 ^ (prefixWord ++ tailWord_759112).sum := by decide
  have hdescent : baseEnd_759112 < baseStart_759112 := by decide
  rcases family_descends (prefixWord ++ tailWord_759112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759129 : List Nat := [1, 2, 1, 2, 2, 2, 5, 2, 3]
def baseStart_759129 : Nat := 118140960795 + 759129 * 2 ^ 59
def prefixEnd_759129 : Nat := 4983230072969 + 3 ^ 40 * 759129 * 2
def baseEnd_759129 : Nat := 346487160681836122663409

theorem tailTrace_759129 : CollatzResearch.WordTrace tailWord_759129 prefixEnd_759129 346487160681836122663409 := by
  unfold tailWord_759129
  simp only [CollatzResearch.WordTrace]
  refine ⟨27687709266812756756432441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18458472844541837837621627 27687709266812756756432441)
  ·
    refine ⟨20765781950109567567324331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27687709266812756756432441 20765781950109567567324331)
    ·
      refine ⟨31148672925164351350986497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20765781950109567567324331 31148672925164351350986497)
      ·
        refine ⟨23361504693873263513239873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31148672925164351350986497 23361504693873263513239873)
        ·
          refine ⟨17521128520404947634929905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23361504693873263513239873 17521128520404947634929905)
          ·
            refine ⟨13140846390303710726197429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17521128520404947634929905 13140846390303710726197429)
            ·
              refine ⟨1231954349090972880581009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13140846390303710726197429 1231954349090972880581009)
              ·
                refine ⟨923965761818229660435757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1231954349090972880581009 923965761818229660435757)
                ·
                  refine ⟨346487160681836122663409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923965761818229660435757 346487160681836122663409)
                  ·
                    rfl

theorem cell20_759129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_759129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759129 prefixEnd_759129 := by exact prefixLift 759129
  have htrace : WordTrace (prefixWord ++ tailWord_759129) baseStart_759129 baseEnd_759129 := by
    simpa [prefixWord, tailWord_759129, baseEnd_759129] using wordTrace_append hprefix tailTrace_759129
  have hstable : (prefixWord ++ tailWord_759129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759129).length < 2 ^ (prefixWord ++ tailWord_759129).sum := by decide
  have hdescent : baseEnd_759129 < baseStart_759129 := by decide
  rcases family_descends (prefixWord ++ tailWord_759129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759136 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 4]
def baseStart_759136 : Nat := 118140960795 + 759136 * 2 ^ 59
def prefixEnd_759136 : Nat := 4983230072969 + 3 ^ 40 * 759136 * 2
def baseEnd_759136 : Nat := 346490355672575209430047

theorem tailTrace_759136 : CollatzResearch.WordTrace tailWord_759136 prefixEnd_759136 346490355672575209430047 := by
  unfold tailWord_759136
  simp only [CollatzResearch.WordTrace]
  refine ⟨13843982288893698475968631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18458643051858264634624841 13843982288893698475968631)
  ·
    refine ⟨20765973433340547713952947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13843982288893698475968631 20765973433340547713952947)
    ·
      refine ⟨31148960150010821570929421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20765973433340547713952947 31148960150010821570929421)
      ·
        refine ⟨11680860056254058089098533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31148960150010821570929421 11680860056254058089098533)
        ·
          refine ⟨2190161260547635891705975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11680860056254058089098533 2190161260547635891705975)
          ·
            refine ⟨3285241890821453837558963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2190161260547635891705975 3285241890821453837558963)
            ·
              refine ⟨4927862836232180756338445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3285241890821453837558963 4927862836232180756338445)
              ·
                refine ⟨1847948563587067783626917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4927862836232180756338445 1847948563587067783626917)
                ·
                  refine ⟨346490355672575209430047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1847948563587067783626917 346490355672575209430047)
                  ·
                    rfl

theorem cell20_759136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_759136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759136 prefixEnd_759136 := by exact prefixLift 759136
  have htrace : WordTrace (prefixWord ++ tailWord_759136) baseStart_759136 baseEnd_759136 := by
    simpa [prefixWord, tailWord_759136, baseEnd_759136] using wordTrace_append hprefix tailTrace_759136
  have hstable : (prefixWord ++ tailWord_759136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759136).length < 2 ^ (prefixWord ++ tailWord_759136).sum := by decide
  have hdescent : baseEnd_759136 < baseStart_759136 := by decide
  rcases family_descends (prefixWord ++ tailWord_759136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759229 : List Nat := [1, 4, 1, 2, 2, 1, 2, 5, 2]
def baseStart_759229 : Nat := 118140960795 + 759229 * 2 ^ 59
def prefixEnd_759229 : Nat := 4983230072969 + 3 ^ 40 * 759229 * 2
def baseEnd_759229 : Nat := 346532803406680219329667

theorem tailTrace_759229 : CollatzResearch.WordTrace tailWord_759229 prefixEnd_759229 346532803406680219329667 := by
  unfold tailWord_759229
  simp only [CollatzResearch.WordTrace]
  refine ⟨27691356566450473835072741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18460904377633649223381827 27691356566450473835072741)
  ·
    refine ⟨5192129356209463844076139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27691356566450473835072741 5192129356209463844076139)
    ·
      refine ⟨7788194034314195766114209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5192129356209463844076139 7788194034314195766114209)
      ·
        refine ⟨5841145525735646824585657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7788194034314195766114209 5841145525735646824585657)
        ·
          refine ⟨4380859144301735118439243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5841145525735646824585657 4380859144301735118439243)
          ·
            refine ⟨6571288716452602677658865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4380859144301735118439243 6571288716452602677658865)
            ·
              refine ⟨4928466537339452008244149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6571288716452602677658865 4928466537339452008244149)
              ·
                refine ⟨462043737875573625772889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4928466537339452008244149 462043737875573625772889)
                ·
                  refine ⟨346532803406680219329667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462043737875573625772889 346532803406680219329667)
                  ·
                    rfl

theorem cell20_759229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_759229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759229 prefixEnd_759229 := by exact prefixLift 759229
  have htrace : WordTrace (prefixWord ++ tailWord_759229) baseStart_759229 baseEnd_759229 := by
    simpa [prefixWord, tailWord_759229, baseEnd_759229] using wordTrace_append hprefix tailTrace_759229
  have hstable : (prefixWord ++ tailWord_759229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759229).length < 2 ^ (prefixWord ++ tailWord_759229).sum := by decide
  have hdescent : baseEnd_759229 < baseStart_759229 := by decide
  rcases family_descends (prefixWord ++ tailWord_759229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759246 : List Nat := [4, 1, 1, 1, 2, 1, 6, 2, 2]
def baseStart_759246 : Nat := 118140960795 + 759246 * 2 ^ 59
def prefixEnd_759246 : Nat := 4983230072969 + 3 ^ 40 * 759246 * 2
def baseEnd_759246 : Nat := 346540562669903715762931

theorem tailTrace_759246 : CollatzResearch.WordTrace tailWord_759246 prefixEnd_759246 346540562669903715762931 := by
  unfold tailWord_759246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3461497075923610717305199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18461317738259257158961061 3461497075923610717305199)
  ·
    refine ⟨5192245613885416075957799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3461497075923610717305199 5192245613885416075957799)
    ·
      refine ⟨7788368420828124113936699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5192245613885416075957799 7788368420828124113936699)
      ·
        refine ⟨11682552631242186170905049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7788368420828124113936699 11682552631242186170905049)
        ·
          refine ⟨8761914473431639628178787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11682552631242186170905049 8761914473431639628178787)
          ·
            refine ⟨13142871710147459442268181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8761914473431639628178787 13142871710147459442268181)
            ·
              refine ⟨616072111413162161356321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13142871710147459442268181 616072111413162161356321)
              ·
                refine ⟨462054083559871621017241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616072111413162161356321 462054083559871621017241)
                ·
                  refine ⟨346540562669903715762931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462054083559871621017241 346540562669903715762931)
                  ·
                    rfl

theorem cell20_759246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_759246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759246 prefixEnd_759246 := by exact prefixLift 759246
  have htrace : WordTrace (prefixWord ++ tailWord_759246) baseStart_759246 baseEnd_759246 := by
    simpa [prefixWord, tailWord_759246, baseEnd_759246] using wordTrace_append hprefix tailTrace_759246
  have hstable : (prefixWord ++ tailWord_759246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759246).length < 2 ^ (prefixWord ++ tailWord_759246).sum := by decide
  have hdescent : baseEnd_759246 < baseStart_759246 := by decide
  rcases family_descends (prefixWord ++ tailWord_759246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759257 : List Nat := [1, 2, 1, 2, 4, 2, 3, 5]
def baseStart_759257 : Nat := 118140960795 + 759257 * 2 ^ 59
def prefixEnd_759257 : Nat := 4983230072969 + 3 ^ 40 * 759257 * 2
def baseEnd_759257 : Nat := 115515194456545522132073

theorem tailTrace_759257 : CollatzResearch.WordTrace tailWord_759257 prefixEnd_759257 115515194456545522132073 := by
  unfold tailWord_759257
  simp only [CollatzResearch.WordTrace]
  refine ⟨27692377810349034617092025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18461585206899356411394683 27692377810349034617092025)
  ·
    refine ⟨20769283357761775962819019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27692377810349034617092025 20769283357761775962819019)
    ·
      refine ⟨31153925036642663944228529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20769283357761775962819019 31153925036642663944228529)
      ·
        refine ⟨23365443777481997958171397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31153925036642663944228529 23365443777481997958171397)
        ·
          refine ⟨4381020708277874617157137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23365443777481997958171397 4381020708277874617157137)
          ·
            refine ⟨3285765531208405962867853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4381020708277874617157137 3285765531208405962867853)
            ·
              refine ⟨1232162074203152236075445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3285765531208405962867853 1232162074203152236075445)
              ·
                refine ⟨115515194456545522132073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1232162074203152236075445 115515194456545522132073)
                ·
                  rfl

theorem cell20_759257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 5].length) (baseStart_759257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759257 prefixEnd_759257 := by exact prefixLift 759257
  have htrace : WordTrace (prefixWord ++ tailWord_759257) baseStart_759257 baseEnd_759257 := by
    simpa [prefixWord, tailWord_759257, baseEnd_759257] using wordTrace_append hprefix tailTrace_759257
  have hstable : (prefixWord ++ tailWord_759257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759257).length < 2 ^ (prefixWord ++ tailWord_759257).sum := by decide
  have hdescent : baseEnd_759257 < baseStart_759257 := by decide
  rcases family_descends (prefixWord ++ tailWord_759257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759294 : List Nat := [4, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_759294 : Nat := 118140960795 + 759294 * 2 ^ 59
def prefixEnd_759294 : Nat := 4983230072969 + 3 ^ 40 * 759294 * 2
def baseEnd_759294 : Nat := 346562471177828882162735

theorem tailTrace_759294 : CollatzResearch.WordTrace tailWord_759294 prefixEnd_759294 346562471177828882162735 := by
  unfold tailWord_759294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3461715913901873742023617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18462484874143326624125957 3461715913901873742023617)
  ·
    refine ⟨2596286935426405306517713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3461715913901873742023617 2596286935426405306517713)
    ·
      refine ⟨1947215201569803979888285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2596286935426405306517713 1947215201569803979888285)
      ·
        refine ⟨730205700588676492458107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1947215201569803979888285 730205700588676492458107)
        ·
          refine ⟨1095308550883014738687161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730205700588676492458107 1095308550883014738687161)
          ·
            refine ⟨821481413162261054015371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1095308550883014738687161 821481413162261054015371)
            ·
              refine ⟨1232222119743391581023057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821481413162261054015371 1232222119743391581023057)
              ·
                refine ⟨924166589807543685767293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1232222119743391581023057 924166589807543685767293)
                ·
                  refine ⟨346562471177828882162735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 924166589807543685767293 346562471177828882162735)
                  ·
                    rfl

theorem cell20_759294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_759294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759294 prefixEnd_759294 := by exact prefixLift 759294
  have htrace : WordTrace (prefixWord ++ tailWord_759294) baseStart_759294 baseEnd_759294 := by
    simpa [prefixWord, tailWord_759294, baseEnd_759294] using wordTrace_append hprefix tailTrace_759294
  have hstable : (prefixWord ++ tailWord_759294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759294).length < 2 ^ (prefixWord ++ tailWord_759294).sum := by decide
  have hdescent : baseEnd_759294 < baseStart_759294 := by decide
  rcases family_descends (prefixWord ++ tailWord_759294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759298 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_759298 : Nat := 118140960795 + 759298 * 2 ^ 59
def prefixEnd_759298 : Nat := 4983230072969 + 3 ^ 40 * 759298 * 2
def baseEnd_759298 : Nat := 346564296886822646029385

theorem tailTrace_759298 : CollatzResearch.WordTrace tailWord_759298 prefixEnd_759298 346564296886822646029385 := by
  unfold tailWord_759298
  simp only [CollatzResearch.WordTrace]
  refine ⟨6923468300800124654833637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18462582135466999079556365 6923468300800124654833637)
  ·
    refine ⟨1298150306400023372781307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6923468300800124654833637 1298150306400023372781307)
    ·
      refine ⟨1947225459600035059171961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1298150306400023372781307 1947225459600035059171961)
      ·
        refine ⟨1460419094700026294378971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1947225459600035059171961 1460419094700026294378971)
        ·
          refine ⟨2190628642050039441568457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1460419094700026294378971 2190628642050039441568457)
          ·
            refine ⟨1642971481537529581176343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2190628642050039441568457 1642971481537529581176343)
            ·
              refine ⟨2464457222306294371764515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1642971481537529581176343 2464457222306294371764515)
              ·
                refine ⟨3696685833459441557646773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2464457222306294371764515 3696685833459441557646773)
                ·
                  refine ⟨346564296886822646029385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3696685833459441557646773 346564296886822646029385)
                  ·
                    rfl

theorem cell20_759298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_759298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759298 prefixEnd_759298 := by exact prefixLift 759298
  have htrace : WordTrace (prefixWord ++ tailWord_759298) baseStart_759298 baseEnd_759298 := by
    simpa [prefixWord, tailWord_759298, baseEnd_759298] using wordTrace_append hprefix tailTrace_759298
  have hstable : (prefixWord ++ tailWord_759298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759298).length < 2 ^ (prefixWord ++ tailWord_759298).sum := by decide
  have hdescent : baseEnd_759298 < baseStart_759298 := by decide
  rcases family_descends (prefixWord ++ tailWord_759298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759385 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 4]
def baseStart_759385 : Nat := 118140960795 + 759385 * 2 ^ 59
def prefixEnd_759385 : Nat := 4983230072969 + 3 ^ 40 * 759385 * 2
def baseEnd_759385 : Nat := 346604006057437010129029

theorem tailTrace_759385 : CollatzResearch.WordTrace tailWord_759385 prefixEnd_759385 346604006057437010129029 := by
  unfold tailWord_759385
  simp only [CollatzResearch.WordTrace]
  refine ⟨27697046353885312477751609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18464697569256874985167739 27697046353885312477751609)
  ·
    refine ⟨20772784765413984358313707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27697046353885312477751609 20772784765413984358313707)
    ·
      refine ⟨31159177148120976537470561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20772784765413984358313707 31159177148120976537470561)
      ·
        refine ⟨23369382861090732403102921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31159177148120976537470561 23369382861090732403102921)
        ·
          refine ⟨17527037145818049302327191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23369382861090732403102921 17527037145818049302327191)
          ·
            refine ⟨26290555718727073953490787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17527037145818049302327191 26290555718727073953490787)
            ·
              refine ⟨39435833578090610930236181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26290555718727073953490787 39435833578090610930236181)
              ·
                refine ⟨1848554698972997387354821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39435833578090610930236181 1848554698972997387354821)
                ·
                  refine ⟨346604006057437010129029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1848554698972997387354821 346604006057437010129029)
                  ·
                    rfl

theorem cell20_759385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_759385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759385 prefixEnd_759385 := by exact prefixLift 759385
  have htrace : WordTrace (prefixWord ++ tailWord_759385) baseStart_759385 baseEnd_759385 := by
    simpa [prefixWord, tailWord_759385, baseEnd_759385] using wordTrace_append hprefix tailTrace_759385
  have hstable : (prefixWord ++ tailWord_759385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759385).length < 2 ^ (prefixWord ++ tailWord_759385).sum := by decide
  have hdescent : baseEnd_759385 < baseStart_759385 := by decide
  rcases family_descends (prefixWord ++ tailWord_759385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759457 : List Nat := [1, 2, 3, 3, 2, 1, 1, 5, 2]
def baseStart_759457 : Nat := 118140960795 + 759457 * 2 ^ 59
def prefixEnd_759457 : Nat := 4983230072969 + 3 ^ 40 * 759457 * 2
def baseEnd_759457 : Nat := 346636868819324759728735

theorem tailTrace_759457 : CollatzResearch.WordTrace tailWord_759457 prefixEnd_759457 346636868819324759728735 := by
  unfold tailWord_759457
  simp only [CollatzResearch.WordTrace]
  refine ⟨27699672409624468774372625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18466448273082979182915083 27699672409624468774372625)
  ·
    refine ⟨20774754307218351580779469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27699672409624468774372625 20774754307218351580779469)
    ·
      refine ⟨7790532865206881842792301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20774754307218351580779469 7790532865206881842792301)
      ·
        refine ⟨2921449824452580691047113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7790532865206881842792301 2921449824452580691047113)
        ·
          refine ⟨2191087368339435518285335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2921449824452580691047113 2191087368339435518285335)
          ·
            refine ⟨3286631052509153277428003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191087368339435518285335 3286631052509153277428003)
            ·
              refine ⟨4929946578763729916142005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3286631052509153277428003 4929946578763729916142005)
              ·
                refine ⟨462182491759099679638313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4929946578763729916142005 462182491759099679638313)
                ·
                  refine ⟨346636868819324759728735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462182491759099679638313 346636868819324759728735)
                  ·
                    rfl

theorem cell20_759457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 2].length) (baseStart_759457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759457 prefixEnd_759457 := by exact prefixLift 759457
  have htrace : WordTrace (prefixWord ++ tailWord_759457) baseStart_759457 baseEnd_759457 := by
    simpa [prefixWord, tailWord_759457, baseEnd_759457] using wordTrace_append hprefix tailTrace_759457
  have hstable : (prefixWord ++ tailWord_759457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759457).length < 2 ^ (prefixWord ++ tailWord_759457).sum := by decide
  have hdescent : baseEnd_759457 < baseStart_759457 := by decide
  rcases family_descends (prefixWord ++ tailWord_759457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759530 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_759530 : Nat := 118140960795 + 759530 * 2 ^ 59
def prefixEnd_759530 : Nat := 4983230072969 + 3 ^ 40 * 759530 * 2
def baseEnd_759530 : Nat := 346670188008460950295103

theorem tailTrace_759530 : CollatzResearch.WordTrace tailWord_759530 prefixEnd_759530 346670188008460950295103 := by
  unfold tailWord_759530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6925583734590000560445011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18468223292240001494520029 6925583734590000560445011)
  ·
    refine ⟨10388375601885000840667517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6925583734590000560445011 10388375601885000840667517)
    ·
      refine ⟨3895640850706875315250319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10388375601885000840667517 3895640850706875315250319)
      ·
        refine ⟨5843461276060312972875479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3895640850706875315250319 5843461276060312972875479)
        ·
          refine ⟨8765191914090469459313219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5843461276060312972875479 8765191914090469459313219)
          ·
            refine ⟨13147787871135704188969829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8765191914090469459313219 13147787871135704188969829)
            ·
              refine ⟨2465210225837944535431843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13147787871135704188969829 2465210225837944535431843)
              ·
                refine ⟨3697815338756916803147765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2465210225837944535431843 3697815338756916803147765)
                ·
                  refine ⟨346670188008460950295103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3697815338756916803147765 346670188008460950295103)
                  ·
                    rfl

theorem cell20_759530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_759530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759530 prefixEnd_759530 := by exact prefixLift 759530
  have htrace : WordTrace (prefixWord ++ tailWord_759530) baseStart_759530 baseEnd_759530 := by
    simpa [prefixWord, tailWord_759530, baseEnd_759530] using wordTrace_append hprefix tailTrace_759530
  have hstable : (prefixWord ++ tailWord_759530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759530).length < 2 ^ (prefixWord ++ tailWord_759530).sum := by decide
  have hdescent : baseEnd_759530 < baseStart_759530 := by decide
  rcases family_descends (prefixWord ++ tailWord_759530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759533 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 4]
def baseStart_759533 : Nat := 118140960795 + 759533 * 2 ^ 59
def prefixEnd_759533 : Nat := 4983230072969 + 3 ^ 40 * 759533 * 2
def baseEnd_759533 : Nat := 346671557290206273195091

theorem tailTrace_759533 : CollatzResearch.WordTrace tailWord_759533 prefixEnd_759533 346671557290206273195091 := by
  unfold tailWord_759533
  simp only [CollatzResearch.WordTrace]
  refine ⟨27702444357349133754139253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18468296238232755836092835 27702444357349133754139253)
  ·
    refine ⟨2597104158501481289450555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27702444357349133754139253 2597104158501481289450555)
    ·
      refine ⟨3895656237752221934175833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2597104158501481289450555 3895656237752221934175833)
      ·
        refine ⟨2921742178314166450631875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3895656237752221934175833 2921742178314166450631875)
        ·
          refine ⟨4382613267471249675947813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2921742178314166450631875 4382613267471249675947813)
          ·
            refine ⟨821739987650859314240215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4382613267471249675947813 821739987650859314240215)
            ·
              refine ⟨1232609981476288971360323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821739987650859314240215 1232609981476288971360323)
              ·
                refine ⟨1848914972214433457040485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232609981476288971360323 1848914972214433457040485)
                ·
                  refine ⟨346671557290206273195091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1848914972214433457040485 346671557290206273195091)
                  ·
                    rfl

theorem cell20_759533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_759533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759533 prefixEnd_759533 := by exact prefixLift 759533
  have htrace : WordTrace (prefixWord ++ tailWord_759533) baseStart_759533 baseEnd_759533 := by
    simpa [prefixWord, tailWord_759533, baseEnd_759533] using wordTrace_append hprefix tailTrace_759533
  have hstable : (prefixWord ++ tailWord_759533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759533).length < 2 ^ (prefixWord ++ tailWord_759533).sum := by decide
  have hdescent : baseEnd_759533 < baseStart_759533 := by decide
  rcases family_descends (prefixWord ++ tailWord_759533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759554 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_759554 : Nat := 118140960795 + 759554 * 2 ^ 59
def prefixEnd_759554 : Nat := 4983230072969 + 3 ^ 40 * 759554 * 2
def baseEnd_759554 : Nat := 346681142262423533495005

theorem tailTrace_759554 : CollatzResearch.WordTrace tailWord_759554 prefixEnd_759554 346681142262423533495005 := by
  unfold tailWord_759554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6925802572568263585163429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18468806860182036227102477 6925802572568263585163429)
  ·
    refine ⟨1298587982356549422218143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6925802572568263585163429 1298587982356549422218143)
    ·
      refine ⟨1947881973534824133327215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1298587982356549422218143 1947881973534824133327215)
      ·
        refine ⟨2921822960302236199990823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1947881973534824133327215 2921822960302236199990823)
        ·
          refine ⟨4382734440453354299986235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2921822960302236199990823 4382734440453354299986235)
          ·
            refine ⟨6574101660680031449979353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4382734440453354299986235 6574101660680031449979353)
            ·
              refine ⟨4930576245510023587484515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6574101660680031449979353 4930576245510023587484515)
              ·
                refine ⟨7395864368265035381226773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4930576245510023587484515 7395864368265035381226773)
                ·
                  refine ⟨346681142262423533495005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7395864368265035381226773 346681142262423533495005)
                  ·
                    rfl

theorem cell20_759554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_759554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759554 prefixEnd_759554 := by exact prefixLift 759554
  have htrace : WordTrace (prefixWord ++ tailWord_759554) baseStart_759554 baseEnd_759554 := by
    simpa [prefixWord, tailWord_759554, baseEnd_759554] using wordTrace_append hprefix tailTrace_759554
  have hstable : (prefixWord ++ tailWord_759554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759554).length < 2 ^ (prefixWord ++ tailWord_759554).sum := by decide
  have hdescent : baseEnd_759554 < baseStart_759554 := by decide
  rcases family_descends (prefixWord ++ tailWord_759554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759585 : List Nat := [1, 2, 3, 2, 1, 4, 2, 2, 3]
def baseStart_759585 : Nat := 118140960795 + 759585 * 2 ^ 59
def prefixEnd_759585 : Nat := 4983230072969 + 3 ^ 40 * 759585 * 2
def baseEnd_759585 : Nat := 346695291507125203461545

theorem tailTrace_759585 : CollatzResearch.WordTrace tailWord_759585 prefixEnd_759585 346695291507125203461545 := by
  unfold tailWord_759585
  simp only [CollatzResearch.WordTrace]
  refine ⟨27704340953160746635032209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18469560635440497756688139 27704340953160746635032209)
  ·
    refine ⟨20778255714870559976274157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27704340953160746635032209 20778255714870559976274157)
    ·
      refine ⟨7791845893076459991102809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20778255714870559976274157 7791845893076459991102809)
      ·
        refine ⟨5843884419807344993327107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7791845893076459991102809 5843884419807344993327107)
        ·
          refine ⟨8765826629711017489990661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5843884419807344993327107 8765826629711017489990661)
          ·
            refine ⟨1643592493070815779373249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8765826629711017489990661 1643592493070815779373249)
            ·
              refine ⟨1232694369803111834529937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1643592493070815779373249 1232694369803111834529937)
              ·
                refine ⟨924520777352333875897453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1232694369803111834529937 924520777352333875897453)
                ·
                  refine ⟨346695291507125203461545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 924520777352333875897453 346695291507125203461545)
                  ·
                    rfl

theorem cell20_759585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_759585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759585 prefixEnd_759585 := by exact prefixLift 759585
  have htrace : WordTrace (prefixWord ++ tailWord_759585) baseStart_759585 baseEnd_759585 := by
    simpa [prefixWord, tailWord_759585, baseEnd_759585] using wordTrace_append hprefix tailTrace_759585
  have hstable : (prefixWord ++ tailWord_759585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759585).length < 2 ^ (prefixWord ++ tailWord_759585).sum := by decide
  have hdescent : baseEnd_759585 < baseStart_759585 := by decide
  rcases family_descends (prefixWord ++ tailWord_759585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759588 : List Nat := [2, 3, 1, 3, 2, 1, 4, 2, 2]
def baseStart_759588 : Nat := 118140960795 + 759588 * 2 ^ 59
def prefixEnd_759588 : Nat := 4983230072969 + 3 ^ 40 * 759588 * 2
def baseEnd_759588 : Nat := 346696660788870526361533

theorem tailTrace_759588 : CollatzResearch.WordTrace tailWord_759588 prefixEnd_759588 346696660788870526361533 := by
  unfold tailWord_759588
  simp only [CollatzResearch.WordTrace]
  refine ⟨13852225186074939073695709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18469633581433252098260945 13852225186074939073695709)
  ·
    refine ⟨5194584444778102152635891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13852225186074939073695709 5194584444778102152635891)
    ·
      refine ⟨7791876667167153228953837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5194584444778102152635891 7791876667167153228953837)
      ·
        refine ⟨2921953750187682460857689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7791876667167153228953837 2921953750187682460857689)
        ·
          refine ⟨2191465312640761845643267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2921953750187682460857689 2191465312640761845643267)
          ·
            refine ⟨3287197968961142768464901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191465312640761845643267 3287197968961142768464901)
            ·
              refine ⟨616349619180214269087169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3287197968961142768464901 616349619180214269087169)
              ·
                refine ⟨462262214385160701815377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616349619180214269087169 462262214385160701815377)
                ·
                  refine ⟨346696660788870526361533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462262214385160701815377 346696660788870526361533)
                  ·
                    rfl

theorem cell20_759588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_759588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759588 prefixEnd_759588 := by exact prefixLift 759588
  have htrace : WordTrace (prefixWord ++ tailWord_759588) baseStart_759588 baseEnd_759588 := by
    simpa [prefixWord, tailWord_759588, baseEnd_759588] using wordTrace_append hprefix tailTrace_759588
  have hstable : (prefixWord ++ tailWord_759588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759588).length < 2 ^ (prefixWord ++ tailWord_759588).sum := by decide
  have hdescent : baseEnd_759588 < baseStart_759588 := by decide
  rcases family_descends (prefixWord ++ tailWord_759588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759609 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 4]
def baseStart_759609 : Nat := 118140960795 + 759609 * 2 ^ 59
def prefixEnd_759609 : Nat := 4983230072969 + 3 ^ 40 * 759609 * 2
def baseEnd_759609 : Nat := 346706245761087786661447

theorem tailTrace_759609 : CollatzResearch.WordTrace tailWord_759609 prefixEnd_759609 346706245761087786661447 := by
  unfold tailWord_759609
  simp only [CollatzResearch.WordTrace]
  refine ⟨27705216305073798733905881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18470144203382532489270587 27705216305073798733905881)
  ·
    refine ⟨20778912228805349050429411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27705216305073798733905881 20778912228805349050429411)
    ·
      refine ⟨31168368343208023575644117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20778912228805349050429411 31168368343208023575644117)
      ·
        refine ⟨730508633043938052554159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 31168368343208023575644117 730508633043938052554159)
        ·
          refine ⟨1095762949565907078831239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730508633043938052554159 1095762949565907078831239)
          ·
            refine ⟨1643644424348860618246859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095762949565907078831239 1643644424348860618246859)
            ·
              refine ⟨2465466636523290927370289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1643644424348860618246859 2465466636523290927370289)
              ·
                refine ⟨1849099977392468195527717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2465466636523290927370289 1849099977392468195527717)
                ·
                  refine ⟨346706245761087786661447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1849099977392468195527717 346706245761087786661447)
                  ·
                    rfl

theorem cell20_759609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_759609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759609 prefixEnd_759609 := by exact prefixLift 759609
  have htrace : WordTrace (prefixWord ++ tailWord_759609) baseStart_759609 baseEnd_759609 := by
    simpa [prefixWord, tailWord_759609, baseEnd_759609] using wordTrace_append hprefix tailTrace_759609
  have hstable : (prefixWord ++ tailWord_759609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759609).length < 2 ^ (prefixWord ++ tailWord_759609).sum := by decide
  have hdescent : baseEnd_759609 < baseStart_759609 := by decide
  rcases family_descends (prefixWord ++ tailWord_759609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759681 : List Nat := [1, 2, 4, 4, 1, 2, 1, 3, 2]
def baseStart_759681 : Nat := 118140960795 + 759681 * 2 ^ 59
def prefixEnd_759681 : Nat := 4983230072969 + 3 ^ 40 * 759681 * 2
def baseEnd_759681 : Nat := 346739108522975536261153

theorem tailTrace_759681 : CollatzResearch.WordTrace tailWord_759681 prefixEnd_759681 346739108522975536261153 := by
  unfold tailWord_759681
  simp only [CollatzResearch.WordTrace]
  refine ⟨27707842360812955030526897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18471894907208636687017931 27707842360812955030526897)
  ·
    refine ⟨20780881770609716272895173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27707842360812955030526897 20780881770609716272895173)
    ·
      refine ⟨3896415331989321801167845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20780881770609716272895173 3896415331989321801167845)
      ·
        refine ⟨730577874747997837718971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3896415331989321801167845 730577874747997837718971)
        ·
          refine ⟨1095866812121996756578457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730577874747997837718971 1095866812121996756578457)
          ·
            refine ⟨821900109091497567433843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1095866812121996756578457 821900109091497567433843)
            ·
              refine ⟨1232850163637246351150765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821900109091497567433843 1232850163637246351150765)
              ·
                refine ⟨462318811363967381681537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1232850163637246351150765 462318811363967381681537)
                ·
                  refine ⟨346739108522975536261153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462318811363967381681537 346739108522975536261153)
                  ·
                    rfl

theorem cell20_759681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 2].length) (baseStart_759681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759681 prefixEnd_759681 := by exact prefixLift 759681
  have htrace : WordTrace (prefixWord ++ tailWord_759681) baseStart_759681 baseEnd_759681 := by
    simpa [prefixWord, tailWord_759681, baseEnd_759681] using wordTrace_append hprefix tailTrace_759681
  have hstable : (prefixWord ++ tailWord_759681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759681).length < 2 ^ (prefixWord ++ tailWord_759681).sum := by decide
  have hdescent : baseEnd_759681 < baseStart_759681 := by decide
  rcases family_descends (prefixWord ++ tailWord_759681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759706 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_759706 : Nat := 118140960795 + 759706 * 2 ^ 59
def prefixEnd_759706 : Nat := 4983230072969 + 3 ^ 40 * 759706 * 2
def baseEnd_759706 : Nat := 346750519204186560427717

theorem tailTrace_759706 : CollatzResearch.WordTrace tailWord_759706 prefixEnd_759706 346750519204186560427717 := by
  unfold tailWord_759706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6927188546430596075046743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18472502790481589533457981 6927188546430596075046743)
  ·
    refine ⟨10390782819645894112570115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6927188546430596075046743 10390782819645894112570115)
    ·
      refine ⟨15586174229468841168855173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10390782819645894112570115 15586174229468841168855173)
      ·
        refine ⟨2922407668025407719160345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15586174229468841168855173 2922407668025407719160345)
        ·
          refine ⟨2191805751019055789370259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2922407668025407719160345 2191805751019055789370259)
          ·
            refine ⟨3287708626528583684055389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191805751019055789370259 3287708626528583684055389)
            ·
              refine ⟨1232890734948218881520771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3287708626528583684055389 1232890734948218881520771)
              ·
                refine ⟨1849336102422328322281157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232890734948218881520771 1849336102422328322281157)
                ·
                  refine ⟨346750519204186560427717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1849336102422328322281157 346750519204186560427717)
                  ·
                    rfl

theorem cell20_759706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_759706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759706 prefixEnd_759706 := by exact prefixLift 759706
  have htrace : WordTrace (prefixWord ++ tailWord_759706) baseStart_759706 baseEnd_759706 := by
    simpa [prefixWord, tailWord_759706, baseEnd_759706] using wordTrace_append hprefix tailTrace_759706
  have hstable : (prefixWord ++ tailWord_759706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759706).length < 2 ^ (prefixWord ++ tailWord_759706).sum := by decide
  have hdescent : baseEnd_759706 < baseStart_759706 := by decide
  rcases family_descends (prefixWord ++ tailWord_759706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759716 : List Nat := [2, 3, 1, 2, 1, 5, 2, 1, 3]
def baseStart_759716 : Nat := 118140960795 + 759716 * 2 ^ 59
def prefixEnd_759716 : Nat := 4983230072969 + 3 ^ 40 * 759716 * 2
def baseEnd_759716 : Nat := 346755083476670970094343

theorem tailTrace_759716 : CollatzResearch.WordTrace tailWord_759716 prefixEnd_759716 346755083476670970094343 := by
  unfold tailWord_759716
  simp only [CollatzResearch.WordTrace]
  refine ⟨13854559457843078004025501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18472745943790770672034001 13854559457843078004025501)
  ·
    refine ⟨5195459796691154251509563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13854559457843078004025501 5195459796691154251509563)
    ·
      refine ⟨7793189695036731377264345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5195459796691154251509563 7793189695036731377264345)
      ·
        refine ⟨5844892271277548532948259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7793189695036731377264345 5844892271277548532948259)
        ·
          refine ⟨8767338406916322799422389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5844892271277548532948259 8767338406916322799422389)
          ·
            refine ⟨821937975648405262445849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8767338406916322799422389 821937975648405262445849)
            ·
              refine ⟨616453481736303946834387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821937975648405262445849 616453481736303946834387)
              ·
                refine ⟨924680222604455920251581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616453481736303946834387 924680222604455920251581)
                ·
                  refine ⟨346755083476670970094343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 924680222604455920251581 346755083476670970094343)
                  ·
                    rfl

theorem cell20_759716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_759716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759716 prefixEnd_759716 := by exact prefixLift 759716
  have htrace : WordTrace (prefixWord ++ tailWord_759716) baseStart_759716 baseEnd_759716 := by
    simpa [prefixWord, tailWord_759716, baseEnd_759716] using wordTrace_append hprefix tailTrace_759716
  have hstable : (prefixWord ++ tailWord_759716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759716).length < 2 ^ (prefixWord ++ tailWord_759716).sum := by decide
  have hdescent : baseEnd_759716 < baseStart_759716 := by decide
  rcases family_descends (prefixWord ++ tailWord_759716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759744 : List Nat := [2, 1, 1, 2, 3, 2, 2, 5, 2]
def baseStart_759744 : Nat := 118140960795 + 759744 * 2 ^ 59
def prefixEnd_759744 : Nat := 4983230072969 + 3 ^ 40 * 759744 * 2
def baseEnd_759744 : Nat := 346767863439627317160895

theorem tailTrace_759744 : CollatzResearch.WordTrace tailWord_759744 prefixEnd_759744 346767863439627317160895 := by
  unfold tailWord_759744
  simp only [CollatzResearch.WordTrace]
  refine ⟨13855070079792358395035143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18473426773056477860046857 13855070079792358395035143)
  ·
    refine ⟨20782605119688537592552715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13855070079792358395035143 20782605119688537592552715)
    ·
      refine ⟨31173907679532806388829073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20782605119688537592552715 31173907679532806388829073)
      ·
        refine ⟨23380430759649604791621805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31173907679532806388829073 23380430759649604791621805)
        ·
          refine ⟨8767661534868601796858177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23380430759649604791621805 8767661534868601796858177)
          ·
            refine ⟨6575746151151451347643633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8767661534868601796858177 6575746151151451347643633)
            ·
              refine ⟨4931809613363588510732725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6575746151151451347643633 4931809613363588510732725)
              ·
                refine ⟨462357151252836422881193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4931809613363588510732725 462357151252836422881193)
                ·
                  refine ⟨346767863439627317160895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462357151252836422881193 346767863439627317160895)
                  ·
                    rfl

theorem cell20_759744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 2].length) (baseStart_759744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759744 prefixEnd_759744 := by exact prefixLift 759744
  have htrace : WordTrace (prefixWord ++ tailWord_759744) baseStart_759744 baseEnd_759744 := by
    simpa [prefixWord, tailWord_759744, baseEnd_759744] using wordTrace_append hprefix tailTrace_759744
  have hstable : (prefixWord ++ tailWord_759744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759744).length < 2 ^ (prefixWord ++ tailWord_759744).sum := by decide
  have hdescent : baseEnd_759744 < baseStart_759744 := by decide
  rcases family_descends (prefixWord ++ tailWord_759744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759813 : List Nat := [1, 3, 1, 1, 2, 6, 1, 2, 3]
def baseStart_759813 : Nat := 118140960795 + 759813 * 2 ^ 59
def prefixEnd_759813 : Nat := 4983230072969 + 3 ^ 40 * 759813 * 2
def baseEnd_759813 : Nat := 346799356919769743860613

theorem tailTrace_759813 : CollatzResearch.WordTrace tailWord_759813 prefixEnd_759813 346799356919769743860613 := by
  unfold tailWord_759813
  simp only [CollatzResearch.WordTrace]
  refine ⟨27712656796334741574332093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18475104530889827716221395 27712656796334741574332093)
  ·
    refine ⟨10392246298625528090374535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27712656796334741574332093 10392246298625528090374535)
    ·
      refine ⟨15588369447938292135561803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10392246298625528090374535 15588369447938292135561803)
      ·
        refine ⟨23382554171907438203342705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15588369447938292135561803 23382554171907438203342705)
        ·
          refine ⟨17536915628930578652507029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23382554171907438203342705 17536915628930578652507029)
          ·
            refine ⟨822042920106120874336267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17536915628930578652507029 822042920106120874336267)
            ·
              refine ⟨1233064380159181311504401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822042920106120874336267 1233064380159181311504401)
              ·
                refine ⟨924798285119385983628301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1233064380159181311504401 924798285119385983628301)
                ·
                  refine ⟨346799356919769743860613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 924798285119385983628301 346799356919769743860613)
                  ·
                    rfl

theorem cell20_759813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_759813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759813 prefixEnd_759813 := by exact prefixLift 759813
  have htrace : WordTrace (prefixWord ++ tailWord_759813) baseStart_759813 baseEnd_759813 := by
    simpa [prefixWord, tailWord_759813, baseEnd_759813] using wordTrace_append hprefix tailTrace_759813
  have hstable : (prefixWord ++ tailWord_759813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759813).length < 2 ^ (prefixWord ++ tailWord_759813).sum := by decide
  have hdescent : baseEnd_759813 < baseStart_759813 := by decide
  rcases family_descends (prefixWord ++ tailWord_759813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759820 : List Nat := [2, 2, 1, 2, 3, 1, 1, 6, 2]
def baseStart_759820 : Nat := 118140960795 + 759820 * 2 ^ 59
def prefixEnd_759820 : Nat := 4983230072969 + 3 ^ 40 * 759820 * 2
def baseEnd_759820 : Nat := 346802551910508830627251

theorem tailTrace_759820 : CollatzResearch.WordTrace tailWord_759820 prefixEnd_759820 346802551910508830627251 := by
  unfold tailWord_759820
  simp only [CollatzResearch.WordTrace]
  refine ⟨13856456053654690884918457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18475274738206254513224609 13856456053654690884918457)
  ·
    refine ⟨10392342040241018163688843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13856456053654690884918457 10392342040241018163688843)
    ·
      refine ⟨15588513060361527245533265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10392342040241018163688843 15588513060361527245533265)
      ·
        refine ⟨11691384795271145434149949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15588513060361527245533265 11691384795271145434149949)
        ·
          refine ⟨4384269298226679537806231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11691384795271145434149949 4384269298226679537806231)
          ·
            refine ⟨6576403947340019306709347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384269298226679537806231 6576403947340019306709347)
            ·
              refine ⟨9864605921010028960064021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6576403947340019306709347 9864605921010028960064021)
              ·
                refine ⟨462403402547345107503001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9864605921010028960064021 462403402547345107503001)
                ·
                  refine ⟨346802551910508830627251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462403402547345107503001 346802551910508830627251)
                  ·
                    rfl

theorem cell20_759820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_759820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759820 prefixEnd_759820 := by exact prefixLift 759820
  have htrace : WordTrace (prefixWord ++ tailWord_759820) baseStart_759820 baseEnd_759820 := by
    simpa [prefixWord, tailWord_759820, baseEnd_759820] using wordTrace_append hprefix tailTrace_759820
  have hstable : (prefixWord ++ tailWord_759820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759820).length < 2 ^ (prefixWord ++ tailWord_759820).sum := by decide
  have hdescent : baseEnd_759820 < baseStart_759820 := by decide
  rcases family_descends (prefixWord ++ tailWord_759820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
