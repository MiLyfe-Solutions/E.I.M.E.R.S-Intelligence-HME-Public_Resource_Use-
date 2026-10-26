import V185TrunkScan22Chunk458

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4090472 : List Nat := [2, 1, 4, 3, 2, 10]
def baseStart_4090472 : Nat := 118140960795 + 4090472 * 2 ^ 59
def prefixEnd_4090472 : Nat := 4983230072969 + 3 ^ 40 * 4090472 * 2
def baseEnd_4090472 : Nat := 17287063701712141919245

theorem tailTrace_4090472 : CollatzResearch.WordTrace tailWord_4090472 prefixEnd_4090472 17287063701712141919245 := by
  unfold tailWord_4090472
  simp only [CollatzResearch.WordTrace]
  refine ⟨74595885218463007922280835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99461180291284010563041113 74595885218463007922280835)
  ·
    refine ⟨111893827827694511883421253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74595885218463007922280835 111893827827694511883421253)
    ·
      refine ⟨20980092717692720978141485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111893827827694511883421253 20980092717692720978141485)
      ·
        refine ⟨7867534769134770366803057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20980092717692720978141485 7867534769134770366803057)
        ·
          refine ⟨5900651076851077775102293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7867534769134770366803057 5900651076851077775102293)
          ·
            refine ⟨17287063701712141919245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5900651076851077775102293 17287063701712141919245)
            ·
              rfl

theorem cell22_4090472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 10].length) (baseStart_4090472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090472 prefixEnd_4090472 := by exact prefixLift 4090472
  have htrace : WordTrace (prefixWord ++ tailWord_4090472) baseStart_4090472 baseEnd_4090472 := by
    simpa [prefixWord, tailWord_4090472, baseEnd_4090472] using wordTrace_append hprefix tailTrace_4090472
  have hstable : (prefixWord ++ tailWord_4090472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090472).length < 2 ^ (prefixWord ++ tailWord_4090472).sum := by decide
  have hdescent : baseEnd_4090472 < baseStart_4090472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090478 : List Nat := [4, 1, 2, 2, 2, 3, 2, 2, 4]
def baseStart_4090478 : Nat := 118140960795 + 4090478 * 2 ^ 59
def prefixEnd_4090478 : Nat := 4983230072969 + 3 ^ 40 * 4090478 * 2
def baseEnd_4090478 : Nat := 466751404587100493269609

theorem tailTrace_4090478 : CollatzResearch.WordTrace tailWord_4090478 prefixEnd_4090478 466751404587100493269609 := by
  unfold tailWord_4090478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18648998659363034858660011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99461326183269519246186725 18648998659363034858660011)
  ·
    refine ⟨27973497989044552287990017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18648998659363034858660011 27973497989044552287990017)
    ·
      refine ⟨20980123491783414215992513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27973497989044552287990017 20980123491783414215992513)
      ·
        refine ⟨15735092618837560661994385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20980123491783414215992513 15735092618837560661994385)
        ·
          refine ⟨11801319464128170496495789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15735092618837560661994385 11801319464128170496495789)
          ·
            refine ⟨4425494799048063936185921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11801319464128170496495789 4425494799048063936185921)
            ·
              refine ⟨3319121099286047952139441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4425494799048063936185921 3319121099286047952139441)
              ·
                refine ⟨2489340824464535964104581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3319121099286047952139441 2489340824464535964104581)
                ·
                  refine ⟨466751404587100493269609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2489340824464535964104581 466751404587100493269609)
                  ·
                    rfl

theorem cell22_4090478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_4090478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090478 prefixEnd_4090478 := by exact prefixLift 4090478
  have htrace : WordTrace (prefixWord ++ tailWord_4090478) baseStart_4090478 baseEnd_4090478 := by
    simpa [prefixWord, tailWord_4090478, baseEnd_4090478] using wordTrace_append hprefix tailTrace_4090478
  have hstable : (prefixWord ++ tailWord_4090478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090478).length < 2 ^ (prefixWord ++ tailWord_4090478).sum := by decide
  have hdescent : baseEnd_4090478 < baseStart_4090478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090521 : List Nat := [1, 2, 1, 2, 1, 2, 6, 3, 1, 3]
def baseStart_4090521 : Nat := 118140960795 + 4090521 * 2 ^ 59
def prefixEnd_4090521 : Nat := 4983230072969 + 3 ^ 40 * 4090521 * 2
def baseEnd_4090521 : Nat := 1400268933540063700983695

theorem tailTrace_4090521 : CollatzResearch.WordTrace tailWord_4090521 prefixEnd_4090521 1400268933540063700983695 := by
  unfold tailWord_4090521
  simp only [CollatzResearch.WordTrace]
  refine ⟨149193557613748497213095417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99462371742498998142063611 149193557613748497213095417)
  ·
    refine ⟨111895168210311372909821563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149193557613748497213095417 111895168210311372909821563)
    ·
      refine ⟨167842752315467059364732345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111895168210311372909821563 167842752315467059364732345)
      ·
        refine ⟨125882064236600294523549259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167842752315467059364732345 125882064236600294523549259)
        ·
          refine ⟨188823096354900441785323889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125882064236600294523549259 188823096354900441785323889)
          ·
            refine ⟨141617322266175331338992917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188823096354900441785323889 141617322266175331338992917)
            ·
              refine ⟨6638311981226968656515293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141617322266175331338992917 6638311981226968656515293)
              ·
                refine ⟨2489366992960113246193235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6638311981226968656515293 2489366992960113246193235)
                ·
                  refine ⟨3734050489440169869289853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2489366992960113246193235 3734050489440169869289853)
                  ·
                    refine ⟨1400268933540063700983695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3734050489440169869289853 1400268933540063700983695)
                    ·
                      rfl

theorem cell22_4090521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 1, 3].length) (baseStart_4090521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090521 prefixEnd_4090521 := by exact prefixLift 4090521
  have htrace : WordTrace (prefixWord ++ tailWord_4090521) baseStart_4090521 baseEnd_4090521 := by
    simpa [prefixWord, tailWord_4090521, baseEnd_4090521] using wordTrace_append hprefix tailTrace_4090521
  have hstable : (prefixWord ++ tailWord_4090521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090521).length < 2 ^ (prefixWord ++ tailWord_4090521).sum := by decide
  have hdescent : baseEnd_4090521 < baseStart_4090521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090532 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_4090532 : Nat := 118140960795 + 4090532 * 2 ^ 59
def prefixEnd_4090532 : Nat := 4983230072969 + 3 ^ 40 * 4090532 * 2
def baseEnd_4090532 : Nat := 1400272699064863338958661

theorem tailTrace_4090532 : CollatzResearch.WordTrace tailWord_4090532 prefixEnd_4090532 1400272699064863338958661 := by
  unfold tailWord_4090532
  simp only [CollatzResearch.WordTrace]
  refine ⟨74596979408354323045872925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99462639211139097394497233 74596979408354323045872925)
  ·
    refine ⟨27973867278132871142202347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74596979408354323045872925 27973867278132871142202347)
    ·
      refine ⟨41960800917199306713303521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27973867278132871142202347 41960800917199306713303521)
      ·
        refine ⟨31470600687899480034977641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41960800917199306713303521 31470600687899480034977641)
        ·
          refine ⟨23602950515924610026233231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31470600687899480034977641 23602950515924610026233231)
          ·
            refine ⟨35404425773886915039349847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23602950515924610026233231 35404425773886915039349847)
            ·
              refine ⟨53106638660830372559024771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35404425773886915039349847 53106638660830372559024771)
              ·
                refine ⟨79659957991245558838537157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53106638660830372559024771 79659957991245558838537157)
                ·
                  refine ⟨14936242123358542282225717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79659957991245558838537157 14936242123358542282225717)
                  ·
                    refine ⟨1400272699064863338958661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14936242123358542282225717 1400272699064863338958661)
                    ·
                      rfl

theorem cell22_4090532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_4090532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090532 prefixEnd_4090532 := by exact prefixLift 4090532
  have htrace : WordTrace (prefixWord ++ tailWord_4090532) baseStart_4090532 baseEnd_4090532 := by
    simpa [prefixWord, tailWord_4090532, baseEnd_4090532] using wordTrace_append hprefix tailTrace_4090532
  have hstable : (prefixWord ++ tailWord_4090532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090532).length < 2 ^ (prefixWord ++ tailWord_4090532).sum := by decide
  have hdescent : baseEnd_4090532 < baseStart_4090532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090549 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 2, 5]
def baseStart_4090549 : Nat := 118140960795 + 4090549 * 2 ^ 59
def prefixEnd_4090549 : Nat := 4983230072969 + 3 ^ 40 * 4090549 * 2
def baseEnd_4090549 : Nat := 1400278518512280961283609

theorem tailTrace_4090549 : CollatzResearch.WordTrace tailWord_4090549 prefixEnd_4090549 1400278518512280961283609 := by
  unfold tailWord_4090549
  simp only [CollatzResearch.WordTrace]
  refine ⟨149194578857647057995114701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99463052571764705330076467 149194578857647057995114701)
  ·
    refine ⟨55947967071617646748168013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149194578857647057995114701 55947967071617646748168013)
    ·
      refine ⟨20980487651856617530563005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55947967071617646748168013 20980487651856617530563005)
      ·
        refine ⟨7867682869446231573961127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20980487651856617530563005 7867682869446231573961127)
        ·
          refine ⟨11801524304169347360941691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7867682869446231573961127 11801524304169347360941691)
          ·
            refine ⟨17702286456254021041412537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11801524304169347360941691 17702286456254021041412537)
            ·
              refine ⟨13276714842190515781059403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17702286456254021041412537 13276714842190515781059403)
              ·
                refine ⟨19915072263285773671589105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13276714842190515781059403 19915072263285773671589105)
                ·
                  refine ⟨14936304197464330253691829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19915072263285773671589105 14936304197464330253691829)
                  ·
                    refine ⟨1400278518512280961283609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14936304197464330253691829 1400278518512280961283609)
                    ·
                      rfl

theorem cell22_4090549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_4090549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090549 prefixEnd_4090549 := by exact prefixLift 4090549
  have htrace : WordTrace (prefixWord ++ tailWord_4090549) baseStart_4090549 baseEnd_4090549 := by
    simpa [prefixWord, tailWord_4090549, baseEnd_4090549] using wordTrace_append hprefix tailTrace_4090549
  have hstable : (prefixWord ++ tailWord_4090549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090549).length < 2 ^ (prefixWord ++ tailWord_4090549).sum := by decide
  have hdescent : baseEnd_4090549 < baseStart_4090549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090551 : List Nat := [1, 1, 3, 1, 6, 1, 3, 1, 5]
def baseStart_4090551 : Nat := 118140960795 + 4090551 * 2 ^ 59
def prefixEnd_4090551 : Nat := 4983230072969 + 3 ^ 40 * 4090551 * 2
def baseEnd_4090551 : Nat := 466759734384384540911201

theorem tailTrace_4090551 : CollatzResearch.WordTrace tailWord_4090551 prefixEnd_4090551 466759734384384540911201 := by
  unfold tailWord_4090551
  simp only [CollatzResearch.WordTrace]
  refine ⟨149194651803639812336687507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99463101202426541557791671 149194651803639812336687507)
  ·
    refine ⟨223791977705459718505031261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149194651803639812336687507 223791977705459718505031261)
    ·
      refine ⟨83921991639547394439386723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223791977705459718505031261 83921991639547394439386723)
      ·
        refine ⟨125882987459321091659080085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83921991639547394439386723 125882987459321091659080085)
        ·
          refine ⟨5900765037155676171519379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125882987459321091659080085 5900765037155676171519379)
          ·
            refine ⟨8851147555733514257279069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5900765037155676171519379 8851147555733514257279069)
            ·
              refine ⟨3319180333400067846479651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8851147555733514257279069 3319180333400067846479651)
              ·
                refine ⟨4978770500100101769719477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3319180333400067846479651 4978770500100101769719477)
                ·
                  refine ⟨466759734384384540911201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4978770500100101769719477 466759734384384540911201)
                  ·
                    rfl

theorem cell22_4090551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 5].length) (baseStart_4090551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090551 prefixEnd_4090551 := by exact prefixLift 4090551
  have htrace : WordTrace (prefixWord ++ tailWord_4090551) baseStart_4090551 baseEnd_4090551 := by
    simpa [prefixWord, tailWord_4090551, baseEnd_4090551] using wordTrace_append hprefix tailTrace_4090551
  have hstable : (prefixWord ++ tailWord_4090551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090551).length < 2 ^ (prefixWord ++ tailWord_4090551).sum := by decide
  have hdescent : baseEnd_4090551 < baseStart_4090551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090577 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 3, 5]
def baseStart_4090577 : Nat := 118140960795 + 4090577 * 2 ^ 59
def prefixEnd_4090577 : Nat := 4983230072969 + 3 ^ 40 * 4090577 * 2
def baseEnd_4090577 : Nat := 1400288103484498221583523

theorem tailTrace_4090577 : CollatzResearch.WordTrace tailWord_4090577 prefixEnd_4090577 1400288103484498221583523 := by
  unfold tailWord_4090577
  simp only [CollatzResearch.WordTrace]
  refine ⟨149195600101545618777133985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99463733401030412518089323 149195600101545618777133985)
  ·
    refine ⟨111896700076159214082850489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149195600101545618777133985 111896700076159214082850489)
    ·
      refine ⟨83922525057119410562137867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111896700076159214082850489 83922525057119410562137867)
      ·
        refine ⟨125883787585679115843206801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83922525057119410562137867 125883787585679115843206801)
        ·
          refine ⟨94412840689259336882405101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125883787585679115843206801 94412840689259336882405101)
          ·
            refine ⟨35404815258472251330901913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94412840689259336882405101 35404815258472251330901913)
            ·
              refine ⟨26553611443854188498176435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35404815258472251330901913 26553611443854188498176435)
              ·
                refine ⟨39830417165781282747264653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26553611443854188498176435 39830417165781282747264653)
                ·
                  refine ⟨14936406437167981030224245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39830417165781282747264653 14936406437167981030224245)
                  ·
                    refine ⟨1400288103484498221583523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14936406437167981030224245 1400288103484498221583523)
                    ·
                      rfl

theorem cell22_4090577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_4090577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090577 prefixEnd_4090577 := by exact prefixLift 4090577
  have htrace : WordTrace (prefixWord ++ tailWord_4090577) baseStart_4090577 baseEnd_4090577 := by
    simpa [prefixWord, tailWord_4090577, baseEnd_4090577] using wordTrace_append hprefix tailTrace_4090577
  have hstable : (prefixWord ++ tailWord_4090577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090577).length < 2 ^ (prefixWord ++ tailWord_4090577).sum := by decide
  have hdescent : baseEnd_4090577 < baseStart_4090577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090607 : List Nat := [1, 1, 2, 1, 5, 2, 1, 9]
def baseStart_4090607 : Nat := 118140960795 + 4090607 * 2 ^ 59
def prefixEnd_4090607 : Nat := 4983230072969 + 3 ^ 40 * 4090607 * 2
def baseEnd_4090607 : Nat := 155588708121954238148159

theorem tailTrace_4090607 : CollatzResearch.WordTrace tailWord_4090607 prefixEnd_4090607 155588708121954238148159 := by
  unfold tailWord_4090607
  simp only [CollatzResearch.WordTrace]
  refine ⟨149196694291436933900726075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99464462860957955933817383 149196694291436933900726075)
  ·
    refine ⟨223795041437155400851089113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149196694291436933900726075 223795041437155400851089113)
    ·
      refine ⟨167846281077866550638316835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223795041437155400851089113 167846281077866550638316835)
      ·
        refine ⟨251769421616799825957475253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167846281077866550638316835 251769421616799825957475253)
        ·
          refine ⟨23603383276574983683513305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251769421616799825957475253 23603383276574983683513305)
          ·
            refine ⟨17702537457431237762634979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23603383276574983683513305 17702537457431237762634979)
            ·
              refine ⟨26553806186146856643952469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17702537457431237762634979 26553806186146856643952469)
              ·
                refine ⟨155588708121954238148159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26553806186146856643952469 155588708121954238148159)
                ·
                  rfl

theorem cell22_4090607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 9].length) (baseStart_4090607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090607 prefixEnd_4090607 := by exact prefixLift 4090607
  have htrace : WordTrace (prefixWord ++ tailWord_4090607) baseStart_4090607 baseEnd_4090607 := by
    simpa [prefixWord, tailWord_4090607, baseEnd_4090607] using wordTrace_append hprefix tailTrace_4090607
  have hstable : (prefixWord ++ tailWord_4090607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090607).length < 2 ^ (prefixWord ++ tailWord_4090607).sum := by decide
  have hdescent : baseEnd_4090607 < baseStart_4090607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090626 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_4090626 : Nat := 118140960795 + 4090626 * 2 ^ 59
def prefixEnd_4090626 : Nat := 4983230072969 + 3 ^ 40 * 4090626 * 2
def baseEnd_4090626 : Nat := 1400304877185878427108373

theorem tailTrace_4090626 : CollatzResearch.WordTrace tailWord_4090626 prefixEnd_4090626 1400304877185878427108373 := by
  unfold tailWord_4090626
  simp only [CollatzResearch.WordTrace]
  refine ⟨37299346819592025036416933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99464924852245400097111821 37299346819592025036416933)
  ·
    refine ⟨6993627528673504694328175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37299346819592025036416933 6993627528673504694328175)
    ·
      refine ⟨10490441293010257041492263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6993627528673504694328175 10490441293010257041492263)
      ·
        refine ⟨15735661939515385562238395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10490441293010257041492263 15735661939515385562238395)
        ·
          refine ⟨23603492909273078343357593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15735661939515385562238395 23603492909273078343357593)
          ·
            refine ⟨17702619681954808757518195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23603492909273078343357593 17702619681954808757518195)
            ·
              refine ⟨26553929522932213136277293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17702619681954808757518195 26553929522932213136277293)
              ·
                refine ⟨9957723571099579926103985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26553929522932213136277293 9957723571099579926103985)
                ·
                  refine ⟨7468292678324684944577989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9957723571099579926103985 7468292678324684944577989)
                  ·
                    refine ⟨1400304877185878427108373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7468292678324684944577989 1400304877185878427108373)
                    ·
                      rfl

theorem cell22_4090626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_4090626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090626 prefixEnd_4090626 := by exact prefixLift 4090626
  have htrace : WordTrace (prefixWord ++ tailWord_4090626) baseStart_4090626 baseEnd_4090626 := by
    simpa [prefixWord, tailWord_4090626, baseEnd_4090626] using wordTrace_append hprefix tailTrace_4090626
  have hstable : (prefixWord ++ tailWord_4090626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090626).length < 2 ^ (prefixWord ++ tailWord_4090626).sum := by decide
  have hdescent : baseEnd_4090626 < baseStart_4090626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090667 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 1, 7]
def baseStart_4090667 : Nat := 118140960795 + 4090667 * 2 ^ 59
def prefixEnd_4090667 : Nat := 4983230072969 + 3 ^ 40 * 4090667 * 2
def baseEnd_4090667 : Nat := 1400318912323767986833247

theorem tailTrace_4090667 : CollatzResearch.WordTrace tailWord_4090667 prefixEnd_4090667 1400318912323767986833247 := by
  unfold tailWord_4090667
  simp only [CollatzResearch.WordTrace]
  refine ⟨149198882671219564147910255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99465921780813042765273503 149198882671219564147910255)
  ·
    refine ⟨223798324006829346221865383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149198882671219564147910255 223798324006829346221865383)
    ·
      refine ⟨335697486010244019332798075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223798324006829346221865383 335697486010244019332798075)
      ·
        refine ⟨503546229015366028999197113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335697486010244019332798075 503546229015366028999197113)
        ·
          refine ⟨377659671761524521749397835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503546229015366028999197113 377659671761524521749397835)
          ·
            refine ⟨566489507642286782624096753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377659671761524521749397835 566489507642286782624096753)
            ·
              refine ⟨424867130731715086968072565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566489507642286782624096753 424867130731715086968072565)
              ·
                refine ⟨39831293506098289403256803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 424867130731715086968072565 39831293506098289403256803)
                ·
                  refine ⟨59746940259147434104885205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39831293506098289403256803 59746940259147434104885205)
                  ·
                    refine ⟨1400318912323767986833247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59746940259147434104885205 1400318912323767986833247)
                    ·
                      rfl

theorem cell22_4090667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 7].length) (baseStart_4090667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090667 prefixEnd_4090667 := by exact prefixLift 4090667
  have htrace : WordTrace (prefixWord ++ tailWord_4090667) baseStart_4090667 baseEnd_4090667 := by
    simpa [prefixWord, tailWord_4090667, baseEnd_4090667] using wordTrace_append hprefix tailTrace_4090667
  have hstable : (prefixWord ++ tailWord_4090667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090667).length < 2 ^ (prefixWord ++ tailWord_4090667).sum := by decide
  have hdescent : baseEnd_4090667 < baseStart_4090667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090714 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 6]
def baseStart_4090714 : Nat := 118140960795 + 4090714 * 2 ^ 59
def prefixEnd_4090714 : Nat := 4983230072969 + 3 ^ 40 * 4090714 * 2
def baseEnd_4090714 : Nat := 466778333794758510302701

theorem tailTrace_4090714 : CollatzResearch.WordTrace tailWord_4090714 prefixEnd_4090714 466778333794758510302701 := by
  unfold tailWord_4090714
  simp only [CollatzResearch.WordTrace]
  refine ⟨37300149225512322793717799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99467064601366194116580797 37300149225512322793717799)
  ·
    refine ⟨55950223838268484190576699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37300149225512322793717799 55950223838268484190576699)
    ·
      refine ⟨83925335757402726285865049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55950223838268484190576699 83925335757402726285865049)
      ·
        refine ⟨62944001818052044714398787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83925335757402726285865049 62944001818052044714398787)
        ·
          refine ⟨94416002727078067071598181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62944001818052044714398787 94416002727078067071598181)
          ·
            refine ⟨17703000511327137575924659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94416002727078067071598181 17703000511327137575924659)
            ·
              refine ⟨26554500766990706363886989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17703000511327137575924659 26554500766990706363886989)
              ·
                refine ⟨9957937787621514886457621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26554500766990706363886989 9957937787621514886457621)
                ·
                  refine ⟨466778333794758510302701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9957937787621514886457621 466778333794758510302701)
                  ·
                    rfl

theorem cell22_4090714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_4090714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090714 prefixEnd_4090714 := by exact prefixLift 4090714
  have htrace : WordTrace (prefixWord ++ tailWord_4090714) baseStart_4090714 baseEnd_4090714 := by
    simpa [prefixWord, tailWord_4090714, baseEnd_4090714] using wordTrace_append hprefix tailTrace_4090714
  have hstable : (prefixWord ++ tailWord_4090714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090714).length < 2 ^ (prefixWord ++ tailWord_4090714).sum := by decide
  have hdescent : baseEnd_4090714 < baseStart_4090714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090759 : List Nat := [1, 1, 4, 2, 3, 1, 10]
def baseStart_4090759 : Nat := 118140960795 + 4090759 * 2 ^ 59
def prefixEnd_4090759 : Nat := 4983230072969 + 3 ^ 40 * 4090759 * 2
def baseEnd_4090759 : Nat := 51864829844589274575295

theorem tailTrace_4090759 : CollatzResearch.WordTrace tailWord_4090759 prefixEnd_4090759 51864829844589274575295 := by
  unfold tailWord_4090759
  simp only [CollatzResearch.WordTrace]
  refine ⟨149202238186886263860259331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99468158791257509240172887 149202238186886263860259331)
  ·
    refine ⟨223803357280329395790388997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149202238186886263860259331 223803357280329395790388997)
    ·
      refine ⟨41963129490061761710697937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223803357280329395790388997 41963129490061761710697937)
      ·
        refine ⟨31472347117546321283023453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41963129490061761710697937 31472347117546321283023453)
        ·
          refine ⟨11802130169079870481133795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31472347117546321283023453 11802130169079870481133795)
          ·
            refine ⟨17703195253619805721700693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11802130169079870481133795 17703195253619805721700693)
            ·
              refine ⟨51864829844589274575295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17703195253619805721700693 51864829844589274575295)
              ·
                rfl

theorem cell22_4090759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 10].length) (baseStart_4090759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090759 prefixEnd_4090759 := by exact prefixLift 4090759
  have htrace : WordTrace (prefixWord ++ tailWord_4090759) baseStart_4090759 baseEnd_4090759 := by
    simpa [prefixWord, tailWord_4090759, baseEnd_4090759] using wordTrace_append hprefix tailTrace_4090759
  have hstable : (prefixWord ++ tailWord_4090759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090759).length < 2 ^ (prefixWord ++ tailWord_4090759).sum := by decide
  have hdescent : baseEnd_4090759 < baseStart_4090759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090761 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 2, 4]
def baseStart_4090761 : Nat := 118140960795 + 4090761 * 2 ^ 59
def prefixEnd_4090761 : Nat := 4983230072969 + 3 ^ 40 * 4090761 * 2
def baseEnd_4090761 : Nat := 1400351090444783074982959

theorem tailTrace_4090761 : CollatzResearch.WordTrace tailWord_4090761 prefixEnd_4090761 1400351090444783074982959 := by
  unfold tailWord_4090761
  simp only [CollatzResearch.WordTrace]
  refine ⟨149202311132879018201832137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99468207421919345467888091 149202311132879018201832137)
  ·
    refine ⟨111901733349659263651374103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149202311132879018201832137 111901733349659263651374103)
    ·
      refine ⟨167852600024488895477061155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111901733349659263651374103 167852600024488895477061155)
      ·
        refine ⟨251778900036733343215591733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167852600024488895477061155 251778900036733343215591733)
        ·
          refine ⟨23604271878443750926461725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251778900036733343215591733 23604271878443750926461725)
          ·
            refine ⟨8851601954416406597423147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23604271878443750926461725 8851601954416406597423147)
            ·
              refine ⟨13277402931624609896134721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8851601954416406597423147 13277402931624609896134721)
              ·
                refine ⟨9958052198718457422101041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13277402931624609896134721 9958052198718457422101041)
                ·
                  refine ⟨7468539149038843066575781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9958052198718457422101041 7468539149038843066575781)
                  ·
                    refine ⟨1400351090444783074982959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7468539149038843066575781 1400351090444783074982959)
                    ·
                      rfl

theorem cell22_4090761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_4090761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090761 prefixEnd_4090761 := by exact prefixLift 4090761
  have htrace : WordTrace (prefixWord ++ tailWord_4090761) baseStart_4090761 baseEnd_4090761 := by
    simpa [prefixWord, tailWord_4090761, baseEnd_4090761] using wordTrace_append hprefix tailTrace_4090761
  have hstable : (prefixWord ++ tailWord_4090761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090761).length < 2 ^ (prefixWord ++ tailWord_4090761).sum := by decide
  have hdescent : baseEnd_4090761 < baseStart_4090761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090780 : List Nat := [2, 2, 3, 3, 2, 1, 1, 3, 2, 3]
def baseStart_4090780 : Nat := 118140960795 + 4090780 * 2 ^ 59
def prefixEnd_4090780 : Nat := 4983230072969 + 3 ^ 40 * 4090780 * 2
def baseEnd_4090780 : Nat := 1400357594533073358757901

theorem tailTrace_4090780 : CollatzResearch.WordTrace tailWord_4090780 prefixEnd_4090780 1400357594533073358757901 := by
  unfold tailWord_4090780
  simp only [CollatzResearch.WordTrace]
  refine ⟨74601502059905092223386897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99468669413206789631182529 74601502059905092223386897)
  ·
    refine ⟨55951126544928819167540173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74601502059905092223386897 55951126544928819167540173)
    ·
      refine ⟨20981672454348307187827565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55951126544928819167540173 20981672454348307187827565)
      ·
        refine ⟨7868127170380615195435337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20981672454348307187827565 7868127170380615195435337)
        ·
          refine ⟨5901095377785461396576503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7868127170380615195435337 5901095377785461396576503)
          ·
            refine ⟨8851643066678192094864755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5901095377785461396576503 8851643066678192094864755)
            ·
              refine ⟨13277464600017288142297133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8851643066678192094864755 13277464600017288142297133)
              ·
                refine ⟨4979049225006483053361425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13277464600017288142297133 4979049225006483053361425)
                ·
                  refine ⟨3734286918754862290021069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4979049225006483053361425 3734286918754862290021069)
                  ·
                    refine ⟨1400357594533073358757901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3734286918754862290021069 1400357594533073358757901)
                    ·
                      rfl

theorem cell22_4090780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_4090780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090780 prefixEnd_4090780 := by exact prefixLift 4090780
  have htrace : WordTrace (prefixWord ++ tailWord_4090780) baseStart_4090780 baseEnd_4090780 := by
    simpa [prefixWord, tailWord_4090780, baseEnd_4090780] using wordTrace_append hprefix tailTrace_4090780
  have hstable : (prefixWord ++ tailWord_4090780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090780).length < 2 ^ (prefixWord ++ tailWord_4090780).sum := by decide
  have hdescent : baseEnd_4090780 < baseStart_4090780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090819 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 4, 5]
def baseStart_4090819 : Nat := 118140960795 + 4090819 * 2 ^ 59
def prefixEnd_4090819 : Nat := 4983230072969 + 3 ^ 40 * 4090819 * 2
def baseEnd_4090819 : Nat := 1400370945030090257032781

theorem tailTrace_4090819 : CollatzResearch.WordTrace tailWord_4090819 prefixEnd_4090819 1400370945030090257032781 := by
  unfold tailWord_4090819
  simp only [CollatzResearch.WordTrace]
  refine ⟨149204426566668894107443511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99469617711112596071629007 149204426566668894107443511)
  ·
    refine ⟨223806639850003341161165267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149204426566668894107443511 223806639850003341161165267)
    ·
      refine ⟨335709959775005011741747901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223806639850003341161165267 335709959775005011741747901)
      ·
        refine ⟨125891234915626879403155463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335709959775005011741747901 125891234915626879403155463)
        ·
          refine ⟨188836852373440319104733195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125891234915626879403155463 188836852373440319104733195)
          ·
            refine ⟨283255278560160478657099793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188836852373440319104733195 283255278560160478657099793)
            ·
              refine ⟨212441458920120358992824845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283255278560160478657099793 212441458920120358992824845)
              ·
                refine ⟨79665547095045134622309317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212441458920120358992824845 79665547095045134622309317)
                ·
                  refine ⟨14937290080320962741682997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79665547095045134622309317 14937290080320962741682997)
                  ·
                    refine ⟨1400370945030090257032781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14937290080320962741682997 1400370945030090257032781)
                    ·
                      rfl

theorem cell22_4090819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 5].length) (baseStart_4090819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090819 prefixEnd_4090819 := by exact prefixLift 4090819
  have htrace : WordTrace (prefixWord ++ tailWord_4090819) baseStart_4090819 baseEnd_4090819 := by
    simpa [prefixWord, tailWord_4090819, baseEnd_4090819] using wordTrace_append hprefix tailTrace_4090819
  have hstable : (prefixWord ++ tailWord_4090819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090819).length < 2 ^ (prefixWord ++ tailWord_4090819).sum := by decide
  have hdescent : baseEnd_4090819 < baseStart_4090819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090836 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_4090836 : Nat := 118140960795 + 4090836 * 2 ^ 59
def prefixEnd_4090836 : Nat := 4983230072969 + 3 ^ 40 * 4090836 * 2
def baseEnd_4090836 : Nat := 1400376764477507879357729

theorem tailTrace_4090836 : CollatzResearch.WordTrace tailWord_4090836 prefixEnd_4090836 1400376764477507879357729 := by
  unfold tailWord_4090836
  simp only [CollatzResearch.WordTrace]
  refine ⟨74602523303803653005406181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99470031071738204007208241 74602523303803653005406181)
  ·
    refine ⟨13987973119463184938513659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74602523303803653005406181 13987973119463184938513659)
    ·
      refine ⟨20981959679194777407770489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13987973119463184938513659 20981959679194777407770489)
      ·
        refine ⟨15736469759396083055827867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20981959679194777407770489 15736469759396083055827867)
        ·
          refine ⟨23604704639094124583741801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15736469759396083055827867 23604704639094124583741801)
          ·
            refine ⟨17703528479320593437806351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23604704639094124583741801 17703528479320593437806351)
            ·
              refine ⟨26555292718980890156709527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17703528479320593437806351 26555292718980890156709527)
              ·
                refine ⟨39832939078471335235064291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26555292718980890156709527 39832939078471335235064291)
                ·
                  refine ⟨59749408617707002852596437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39832939078471335235064291 59749408617707002852596437)
                  ·
                    refine ⟨1400376764477507879357729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59749408617707002852596437 1400376764477507879357729)
                    ·
                      rfl

theorem cell22_4090836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_4090836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090836 prefixEnd_4090836 := by exact prefixLift 4090836
  have htrace : WordTrace (prefixWord ++ tailWord_4090836) baseStart_4090836 baseEnd_4090836 := by
    simpa [prefixWord, tailWord_4090836, baseEnd_4090836] using wordTrace_append hprefix tailTrace_4090836
  have hstable : (prefixWord ++ tailWord_4090836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090836).length < 2 ^ (prefixWord ++ tailWord_4090836).sum := by decide
  have hdescent : baseEnd_4090836 < baseStart_4090836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090851 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 3, 4]
def baseStart_4090851 : Nat := 118140960795 + 4090851 * 2 ^ 59
def prefixEnd_4090851 : Nat := 4983230072969 + 3 ^ 40 * 4090851 * 2
def baseEnd_4090851 : Nat := 1400381899284052840232683

theorem tailTrace_4090851 : CollatzResearch.WordTrace tailWord_4090851 prefixEnd_4090851 1400381899284052840232683 := by
  unfold tailWord_4090851
  simp only [CollatzResearch.WordTrace]
  refine ⟨149205593702552963572608407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99470395801701975715072271 149205593702552963572608407)
  ·
    refine ⟨223808390553829445358912611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149205593702552963572608407 223808390553829445358912611)
    ·
      refine ⟨335712585830744168038368917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223808390553829445358912611 335712585830744168038368917)
      ·
        refine ⟨15736527460816132876798543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 335712585830744168038368917 15736527460816132876798543)
        ·
          refine ⟨23604791191224199315197815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15736527460816132876798543 23604791191224199315197815)
          ·
            refine ⟨35407186786836298972796723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23604791191224199315197815 35407186786836298972796723)
            ·
              refine ⟨53110780180254448459195085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35407186786836298972796723 53110780180254448459195085)
              ·
                refine ⟨19916542567595418172198157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53110780180254448459195085 19916542567595418172198157)
                ·
                  refine ⟨7468703462848281814574309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19916542567595418172198157 7468703462848281814574309)
                  ·
                    refine ⟨1400381899284052840232683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7468703462848281814574309 1400381899284052840232683)
                    ·
                      rfl

theorem cell22_4090851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 4].length) (baseStart_4090851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090851 prefixEnd_4090851 := by exact prefixLift 4090851
  have htrace : WordTrace (prefixWord ++ tailWord_4090851) baseStart_4090851 baseEnd_4090851 := by
    simpa [prefixWord, tailWord_4090851, baseEnd_4090851] using wordTrace_append hprefix tailTrace_4090851
  have hstable : (prefixWord ++ tailWord_4090851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090851).length < 2 ^ (prefixWord ++ tailWord_4090851).sum := by decide
  have hdescent : baseEnd_4090851 < baseStart_4090851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090911 : List Nat := [1, 1, 2, 4, 1, 4, 1, 8]
def baseStart_4090911 : Nat := 118140960795 + 4090911 * 2 ^ 59
def prefixEnd_4090911 : Nat := 4983230072969 + 3 ^ 40 * 4090911 * 2
def baseEnd_4090911 : Nat := 155600270945581409303611

theorem tailTrace_4090911 : CollatzResearch.WordTrace tailWord_4090911 prefixEnd_4090911 155600270945581409303611 := by
  unfold tailWord_4090911
  simp only [CollatzResearch.WordTrace]
  refine ⟨149207782082335593819792587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99471854721557062546528391 149207782082335593819792587)
  ·
    refine ⟨223811673123503390729688881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149207782082335593819792587 223811673123503390729688881)
    ·
      refine ⟨167858754842627543047266661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223811673123503390729688881 167858754842627543047266661)
      ·
        refine ⟨31473516532992664321362499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167858754842627543047266661 31473516532992664321362499)
        ·
          refine ⟨47210274799488996482043749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31473516532992664321362499 47210274799488996482043749)
          ·
            refine ⟨8851926524904186840383203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47210274799488996482043749 8851926524904186840383203)
            ·
              refine ⟨13277889787356280260574805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8851926524904186840383203 13277889787356280260574805)
              ·
                refine ⟨155600270945581409303611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13277889787356280260574805 155600270945581409303611)
                ·
                  rfl

theorem cell22_4090911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 8].length) (baseStart_4090911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090911 prefixEnd_4090911 := by exact prefixLift 4090911
  have htrace : WordTrace (prefixWord ++ tailWord_4090911) baseStart_4090911 baseEnd_4090911 := by
    simpa [prefixWord, tailWord_4090911, baseEnd_4090911] using wordTrace_append hprefix tailTrace_4090911
  have hstable : (prefixWord ++ tailWord_4090911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090911).length < 2 ^ (prefixWord ++ tailWord_4090911).sum := by decide
  have hdescent : baseEnd_4090911 < baseStart_4090911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090990 : List Nat := [4, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_4090990 : Nat := 118140960795 + 4090990 * 2 ^ 59
def prefixEnd_4090990 : Nat := 4983230072969 + 3 ^ 40 * 4090990 * 2
def baseEnd_4090990 : Nat := 466809827274900937002419

theorem tailTrace_4090990 : CollatzResearch.WordTrace tailWord_4090990 prefixEnd_4090990 466809827274900937002419 := by
  unfold tailWord_4090990
  simp only [CollatzResearch.WordTrace]
  refine ⟨18651332931131173788989803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99473775632699593541278949 18651332931131173788989803)
  ·
    refine ⟨27976999396696760683484705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18651332931131173788989803 27976999396696760683484705)
    ·
      refine ⟨20982749547522570512613529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27976999396696760683484705 20982749547522570512613529)
      ·
        refine ⟨15737062160641927884460147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20982749547522570512613529 15737062160641927884460147)
        ·
          refine ⟨23605593240962891826690221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15737062160641927884460147 23605593240962891826690221)
          ·
            refine ⟨8852097465361084435008833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23605593240962891826690221 8852097465361084435008833)
            ·
              refine ⟨6639073099020813326256625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8852097465361084435008833 6639073099020813326256625)
              ·
                refine ⟨4979304824265609994692469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6639073099020813326256625 4979304824265609994692469)
                ·
                  refine ⟨466809827274900937002419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4979304824265609994692469 466809827274900937002419)
                  ·
                    rfl

theorem cell22_4090990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_4090990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090990 prefixEnd_4090990 := by exact prefixLift 4090990
  have htrace : WordTrace (prefixWord ++ tailWord_4090990) baseStart_4090990 baseEnd_4090990 := by
    simpa [prefixWord, tailWord_4090990, baseEnd_4090990] using wordTrace_append hprefix tailTrace_4090990
  have hstable : (prefixWord ++ tailWord_4090990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090990).length < 2 ^ (prefixWord ++ tailWord_4090990).sum := by decide
  have hdescent : baseEnd_4090990 < baseStart_4090990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091018 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 6]
def baseStart_4091018 : Nat := 118140960795 + 4091018 * 2 ^ 59
def prefixEnd_4091018 : Nat := 4983230072969 + 3 ^ 40 * 4091018 * 2
def baseEnd_4091018 : Nat := 466813022265640023769057

theorem tailTrace_4091018 : CollatzResearch.WordTrace tailWord_4091018 prefixEnd_4091018 466813022265640023769057 := by
  unfold tailWord_4091018
  simp only [CollatzResearch.WordTrace]
  refine ⟨37302921173236987773484427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99474456461965300729291805 37302921173236987773484427)
  ·
    refine ⟨55954381759855481660226641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37302921173236987773484427 55954381759855481660226641)
    ·
      refine ⟨41965786319891611245169981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55954381759855481660226641 41965786319891611245169981)
      ·
        refine ⟨15737169869959354216938743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41965786319891611245169981 15737169869959354216938743)
        ·
          refine ⟨23605754804939031325408115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15737169869959354216938743 23605754804939031325408115)
          ·
            refine ⟨35408632207408546988112173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23605754804939031325408115 35408632207408546988112173)
            ·
              refine ⟨13278237077778205120542065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35408632207408546988112173 13278237077778205120542065)
              ·
                refine ⟨9958677808333653840406549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13278237077778205120542065 9958677808333653840406549)
                ·
                  refine ⟨466813022265640023769057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9958677808333653840406549 466813022265640023769057)
                  ·
                    rfl

theorem cell22_4091018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_4091018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091018 prefixEnd_4091018 := by exact prefixLift 4091018
  have htrace : WordTrace (prefixWord ++ tailWord_4091018) baseStart_4091018 baseEnd_4091018 := by
    simpa [prefixWord, tailWord_4091018, baseEnd_4091018] using wordTrace_append hprefix tailTrace_4091018
  have hstable : (prefixWord ++ tailWord_4091018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091018).length < 2 ^ (prefixWord ++ tailWord_4091018).sum := by decide
  have hdescent : baseEnd_4091018 < baseStart_4091018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091108 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 7]
def baseStart_4091108 : Nat := 118140960795 + 4091108 * 2 ^ 59
def prefixEnd_4091108 : Nat := 4983230072969 + 3 ^ 40 * 4091108 * 2
def baseEnd_4091108 : Nat := 466823291878729945518965

theorem tailTrace_4091108 : CollatzResearch.WordTrace tailWord_4091108 prefixEnd_4091108 466823291878729945518965 := by
  unfold tailWord_4091108
  simp only [CollatzResearch.WordTrace]
  refine ⟨74607483631310948232356989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99476644841747930976475985 74607483631310948232356989)
  ·
    refine ⟨27977806361741605587133871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74607483631310948232356989 27977806361741605587133871)
    ·
      refine ⟨41966709542612408380700807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27977806361741605587133871 41966709542612408380700807)
      ·
        refine ⟨62950064313918612571051211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41966709542612408380700807 62950064313918612571051211)
        ·
          refine ⟨94425096470877918856576817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62950064313918612571051211 94425096470877918856576817)
          ·
            refine ⟨70818822353158439142432613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94425096470877918856576817 70818822353158439142432613)
            ·
              refine ⟨13278529191217207339206115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70818822353158439142432613 13278529191217207339206115)
              ·
                refine ⟨19917793786825811008809173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13278529191217207339206115 19917793786825811008809173)
                ·
                  refine ⟨466823291878729945518965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19917793786825811008809173 466823291878729945518965)
                  ·
                    rfl

theorem cell22_4091108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_4091108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091108 prefixEnd_4091108 := by exact prefixLift 4091108
  have htrace : WordTrace (prefixWord ++ tailWord_4091108) baseStart_4091108 baseEnd_4091108 := by
    simpa [prefixWord, tailWord_4091108, baseEnd_4091108] using wordTrace_append hprefix tailTrace_4091108
  have hstable : (prefixWord ++ tailWord_4091108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091108).length < 2 ^ (prefixWord ++ tailWord_4091108).sum := by decide
  have hdescent : baseEnd_4091108 < baseStart_4091108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091183 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 1, 6]
def baseStart_4091183 : Nat := 118140960795 + 4091183 * 2 ^ 59
def prefixEnd_4091183 : Nat := 4983230072969 + 3 ^ 40 * 4091183 * 2
def baseEnd_4091183 : Nat := 1400495549668914640931665

theorem tailTrace_4091183 : CollatzResearch.WordTrace tailWord_4091183 prefixEnd_4091183 1400495549668914640931665 := by
  unfold tailWord_4091183
  simp only [CollatzResearch.WordTrace]
  refine ⟨149217702737350184273694203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99478468491566789515796135 149217702737350184273694203)
  ·
    refine ⟨223826554106025276410541305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149217702737350184273694203 223826554106025276410541305)
    ·
      refine ⟨167869915579518957307905979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223826554106025276410541305 167869915579518957307905979)
      ·
        refine ⟨251804873369278435961858969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167869915579518957307905979 251804873369278435961858969)
        ·
          refine ⟨188853655026958826971394227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251804873369278435961858969 188853655026958826971394227)
          ·
            refine ⟨283280482540438240457091341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188853655026958826971394227 283280482540438240457091341)
            ·
              refine ⟨106230180952664340171409253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283280482540438240457091341 106230180952664340171409253)
              ·
                refine ⟨19918158928624563782139235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106230180952664340171409253 19918158928624563782139235)
                ·
                  refine ⟨29877238392936845673208853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19918158928624563782139235 29877238392936845673208853)
                  ·
                    refine ⟨1400495549668914640931665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29877238392936845673208853 1400495549668914640931665)
                    ·
                      rfl

theorem cell22_4091183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_4091183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091183 prefixEnd_4091183 := by exact prefixLift 4091183
  have htrace : WordTrace (prefixWord ++ tailWord_4091183) baseStart_4091183 baseEnd_4091183 := by
    simpa [prefixWord, tailWord_4091183, baseEnd_4091183] using wordTrace_append hprefix tailTrace_4091183
  have hstable : (prefixWord ++ tailWord_4091183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091183).length < 2 ^ (prefixWord ++ tailWord_4091183).sum := by decide
  have hdescent : baseEnd_4091183 < baseStart_4091183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091185 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 1, 5]
def baseStart_4091185 : Nat := 118140960795 + 4091185 * 2 ^ 59
def prefixEnd_4091185 : Nat := 4983230072969 + 3 ^ 40 * 4091185 * 2
def baseEnd_4091185 : Nat := 1400496234309787302381659

theorem tailTrace_4091185 : CollatzResearch.WordTrace tailWord_4091185 prefixEnd_4091185 1400496234309787302381659 := by
  unfold tailWord_4091185
  simp only [CollatzResearch.WordTrace]
  refine ⟨149217775683342938615267009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99478517122228625743511339 149217775683342938615267009)
  ·
    refine ⟨111913331762507203961450257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149217775683342938615267009 111913331762507203961450257)
    ·
      refine ⟨83934998821880402971087693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111913331762507203961450257 83934998821880402971087693)
      ·
        refine ⟨31475624558205151114157885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83934998821880402971087693 31475624558205151114157885)
        ·
          refine ⟨11803359209326931667809207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31475624558205151114157885 11803359209326931667809207)
          ·
            refine ⟨17705038813990397501713811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11803359209326931667809207 17705038813990397501713811)
            ·
              refine ⟨26557558220985596252570717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17705038813990397501713811 26557558220985596252570717)
              ·
                refine ⟨9959084332869598594714019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26557558220985596252570717 9959084332869598594714019)
                ·
                  refine ⟨14938626499304397892071029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9959084332869598594714019 14938626499304397892071029)
                  ·
                    refine ⟨1400496234309787302381659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14938626499304397892071029 1400496234309787302381659)
                    ·
                      rfl

theorem cell22_4091185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_4091185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091185 prefixEnd_4091185 := by exact prefixLift 4091185
  have htrace : WordTrace (prefixWord ++ tailWord_4091185) baseStart_4091185 baseEnd_4091185 := by
    simpa [prefixWord, tailWord_4091185, baseEnd_4091185] using wordTrace_append hprefix tailTrace_4091185
  have hstable : (prefixWord ++ tailWord_4091185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091185).length < 2 ^ (prefixWord ++ tailWord_4091185).sum := by decide
  have hdescent : baseEnd_4091185 < baseStart_4091185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091204 : List Nat := [2, 3, 4, 1, 1, 1, 1, 5, 4]
def baseStart_4091204 : Nat := 118140960795 + 4091204 * 2 ^ 59
def prefixEnd_4091204 : Nat := 4983230072969 + 3 ^ 40 * 4091204 * 2
def baseEnd_4091204 : Nat := 466834246132692528718867

theorem tailTrace_4091204 : CollatzResearch.WordTrace tailWord_4091204 prefixEnd_4091204 466834246132692528718867 := by
  unfold tailWord_4091204
  simp only [CollatzResearch.WordTrace]
  refine ⟨74609234335137052430104333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99478979113516069906805777 74609234335137052430104333)
  ·
    refine ⟨27978462875676394661289125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74609234335137052430104333 27978462875676394661289125)
    ·
      refine ⟨5245961789189323998991711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27978462875676394661289125 5245961789189323998991711)
      ·
        refine ⟨7868942683783985998487567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5245961789189323998991711 7868942683783985998487567)
        ·
          refine ⟨11803414025675978997731351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7868942683783985998487567 11803414025675978997731351)
          ·
            refine ⟨17705121038513968496597027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11803414025675978997731351 17705121038513968496597027)
            ·
              refine ⟨26557681557770952744895541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17705121038513968496597027 26557681557770952744895541)
              ·
                refine ⟨2489782646041026819833957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26557681557770952744895541 2489782646041026819833957)
                ·
                  refine ⟨466834246132692528718867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2489782646041026819833957 466834246132692528718867)
                  ·
                    rfl

theorem cell22_4091204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_4091204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091204 prefixEnd_4091204 := by exact prefixLift 4091204
  have htrace : WordTrace (prefixWord ++ tailWord_4091204) baseStart_4091204 baseEnd_4091204 := by
    simpa [prefixWord, tailWord_4091204, baseEnd_4091204] using wordTrace_append hprefix tailTrace_4091204
  have hstable : (prefixWord ++ tailWord_4091204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091204).length < 2 ^ (prefixWord ++ tailWord_4091204).sum := by decide
  have hdescent : baseEnd_4091204 < baseStart_4091204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091243 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 11]
def baseStart_4091243 : Nat := 118140960795 + 4091243 * 2 ^ 59
def prefixEnd_4091243 : Nat := 4983230072969 + 3 ^ 40 * 4091243 * 2
def baseEnd_4091243 : Nat := 466838696298364828143827

theorem tailTrace_4091243 : CollatzResearch.WordTrace tailWord_4091243 prefixEnd_4091243 466838696298364828143827 := by
  unfold tailWord_4091243
  simp only [CollatzResearch.WordTrace]
  refine ⟨149219891117132814520878383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99479927411421876347252255 149219891117132814520878383)
  ·
    refine ⟨223829836675699221781317575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149219891117132814520878383 223829836675699221781317575)
    ·
      refine ⟨335744755013548832671976363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223829836675699221781317575 335744755013548832671976363)
      ·
        refine ⟨503617132520323249007964545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335744755013548832671976363 503617132520323249007964545)
        ·
          refine ⟨377712849390242436755973409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503617132520323249007964545 377712849390242436755973409)
          ·
            refine ⟨283284637042681827566980057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377712849390242436755973409 283284637042681827566980057)
            ·
              refine ⟨212463477782011370675235043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283284637042681827566980057 212463477782011370675235043)
              ·
                refine ⟨318695216673017056012852565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212463477782011370675235043 318695216673017056012852565)
                ·
                  refine ⟨466838696298364828143827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 318695216673017056012852565 466838696298364828143827)
                  ·
                    rfl

theorem cell22_4091243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 11].length) (baseStart_4091243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091243 prefixEnd_4091243 := by exact prefixLift 4091243
  have htrace : WordTrace (prefixWord ++ tailWord_4091243) baseStart_4091243 baseEnd_4091243 := by
    simpa [prefixWord, tailWord_4091243, baseEnd_4091243] using wordTrace_append hprefix tailTrace_4091243
  have hstable : (prefixWord ++ tailWord_4091243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091243).length < 2 ^ (prefixWord ++ tailWord_4091243).sum := by decide
  have hdescent : baseEnd_4091243 < baseStart_4091243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091320 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 3, 5]
def baseStart_4091320 : Nat := 118140960795 + 4091320 * 2 ^ 59
def prefixEnd_4091320 : Nat := 4983230072969 + 3 ^ 40 * 4091320 * 2
def baseEnd_4091320 : Nat := 1400542447568691950256245

theorem tailTrace_4091320 : CollatzResearch.WordTrace tailWord_4091320 prefixEnd_4091320 1400542447568691950256245 := by
  unfold tailWord_4091320
  simp only [CollatzResearch.WordTrace]
  refine ⟨74611349768926928335715707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99481799691902571114287609 74611349768926928335715707)
  ·
    refine ⟨111917024653390392503573561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74611349768926928335715707 111917024653390392503573561)
    ·
      refine ⟨83937768490042794377680171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111917024653390392503573561 83937768490042794377680171)
      ·
        refine ⟨125906652735064191566520257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83937768490042794377680171 125906652735064191566520257)
        ·
          refine ⟨94429989551298143674890193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125906652735064191566520257 94429989551298143674890193)
          ·
            refine ⟨70822492163473607756167645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94429989551298143674890193 70822492163473607756167645)
            ·
              refine ⟨26558434561302602908562867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70822492163473607756167645 26558434561302602908562867)
              ·
                refine ⟨39837651841953904362844301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26558434561302602908562867 39837651841953904362844301)
                ·
                  refine ⟨14939119440732714136066613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39837651841953904362844301 14939119440732714136066613)
                  ·
                    refine ⟨1400542447568691950256245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14939119440732714136066613 1400542447568691950256245)
                    ·
                      rfl

theorem cell22_4091320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_4091320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091320 prefixEnd_4091320 := by exact prefixLift 4091320
  have htrace : WordTrace (prefixWord ++ tailWord_4091320) baseStart_4091320 baseEnd_4091320 := by
    simpa [prefixWord, tailWord_4091320, baseEnd_4091320] using wordTrace_append hprefix tailTrace_4091320
  have hstable : (prefixWord ++ tailWord_4091320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091320).length < 2 ^ (prefixWord ++ tailWord_4091320).sum := by decide
  have hdescent : baseEnd_4091320 < baseStart_4091320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091339 : List Nat := [1, 1, 1, 1, 3, 3, 6, 2, 4]
def baseStart_4091339 : Nat := 118140960795 + 4091339 * 2 ^ 59
def prefixEnd_4091339 : Nat := 4983230072969 + 3 ^ 40 * 4091339 * 2
def baseEnd_4091339 : Nat := 466849650552327411343729

theorem tailTrace_4091339 : CollatzResearch.WordTrace tailWord_4091339 prefixEnd_4091339 466849650552327411343729 := by
  unfold tailWord_4091339
  simp only [CollatzResearch.WordTrace]
  refine ⟨149223392524785022916373071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99482261683190015277582047 149223392524785022916373071)
  ·
    refine ⟨223835088787177534374559607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149223392524785022916373071 223835088787177534374559607)
    ·
      refine ⟨335752633180766301561839411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223835088787177534374559607 335752633180766301561839411)
      ·
        refine ⟨503628949771149452342759117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335752633180766301561839411 503628949771149452342759117)
        ·
          refine ⟨188860856164181044628534669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503628949771149452342759117 188860856164181044628534669)
          ·
            refine ⟨70822821061567891735700501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188860856164181044628534669 70822821061567891735700501)
            ·
              refine ⟨3319819737260994925110961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70822821061567891735700501 3319819737260994925110961)
              ·
                refine ⟨2489864802945746193833221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3319819737260994925110961 2489864802945746193833221)
                ·
                  refine ⟨466849650552327411343729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2489864802945746193833221 466849650552327411343729)
                  ·
                    rfl

theorem cell22_4091339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 4].length) (baseStart_4091339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091339 prefixEnd_4091339 := by exact prefixLift 4091339
  have htrace : WordTrace (prefixWord ++ tailWord_4091339) baseStart_4091339 baseEnd_4091339 := by
    simpa [prefixWord, tailWord_4091339, baseEnd_4091339] using wordTrace_append hprefix tailTrace_4091339
  have hstable : (prefixWord ++ tailWord_4091339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091339).length < 2 ^ (prefixWord ++ tailWord_4091339).sum := by decide
  have hdescent : baseEnd_4091339 < baseStart_4091339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091354 : List Nat := [3, 1, 1, 2, 3, 2, 2, 3, 2, 3]
def baseStart_4091354 : Nat := 118140960795 + 4091354 * 2 ^ 59
def prefixEnd_4091354 : Nat := 4983230072969 + 3 ^ 40 * 4091354 * 2
def baseEnd_4091354 : Nat := 1400554086463527194906141

theorem tailTrace_4091354 : CollatzResearch.WordTrace tailWord_4091354 prefixEnd_4091354 1400554086463527194906141 := by
  unfold tailWord_4091354
  simp only [CollatzResearch.WordTrace]
  refine ⟨37305984904932670119542279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99482626413153786985446077 37305984904932670119542279)
  ·
    refine ⟨55958977357399005179313419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37305984904932670119542279 55958977357399005179313419)
    ·
      refine ⟨83938466036098507768970129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55958977357399005179313419 83938466036098507768970129)
      ·
        refine ⟨62953849527073880826727597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83938466036098507768970129 62953849527073880826727597)
        ·
          refine ⟨23607693572652705310022849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62953849527073880826727597 23607693572652705310022849)
          ·
            refine ⟨17705770179489528982517137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23607693572652705310022849 17705770179489528982517137)
            ·
              refine ⟨13279327634617146736887853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17705770179489528982517137 13279327634617146736887853)
              ·
                refine ⟨4979747862981430026332945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13279327634617146736887853 4979747862981430026332945)
                ·
                  refine ⟨3734810897236072519749709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4979747862981430026332945 3734810897236072519749709)
                  ·
                    refine ⟨1400554086463527194906141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3734810897236072519749709 1400554086463527194906141)
                    ·
                      rfl

theorem cell22_4091354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_4091354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091354 prefixEnd_4091354 := by exact prefixLift 4091354
  have htrace : WordTrace (prefixWord ++ tailWord_4091354) baseStart_4091354 baseEnd_4091354 := by
    simpa [prefixWord, tailWord_4091354, baseEnd_4091354] using wordTrace_append hprefix tailTrace_4091354
  have hstable : (prefixWord ++ tailWord_4091354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091354).length < 2 ^ (prefixWord ++ tailWord_4091354).sum := by decide
  have hdescent : baseEnd_4091354 < baseStart_4091354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091399 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 3, 3]
def baseStart_4091399 : Nat := 118140960795 + 4091399 * 2 ^ 59
def prefixEnd_4091399 : Nat := 4983230072969 + 3 ^ 40 * 4091399 * 2
def baseEnd_4091399 : Nat := 1400569490883162077531003

theorem tailTrace_4091399 : CollatzResearch.WordTrace tailWord_4091399 prefixEnd_4091399 1400569490883162077531003 := by
  unfold tailWord_4091399
  simp only [CollatzResearch.WordTrace]
  refine ⟨149225580904567653163557251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99483720603045102109038167 149225580904567653163557251)
  ·
    refine ⟨223838371356851479745335877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149225580904567653163557251 223838371356851479745335877)
    ·
      refine ⟨41969694629409652452250477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223838371356851479745335877 41969694629409652452250477)
      ·
        refine ⟨15738635486028619669593929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41969694629409652452250477 15738635486028619669593929)
        ·
          refine ⟨11803976614521464752195447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15738635486028619669593929 11803976614521464752195447)
          ·
            refine ⟨17705964921782197128293171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11803976614521464752195447 17705964921782197128293171)
            ·
              refine ⟨26558947382673295692439757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17705964921782197128293171 26558947382673295692439757)
              ·
                refine ⟨9959605268502485884664909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26558947382673295692439757 9959605268502485884664909)
                ·
                  refine ⟨3734851975688432206749341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9959605268502485884664909 3734851975688432206749341)
                  ·
                    refine ⟨1400569490883162077531003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3734851975688432206749341 1400569490883162077531003)
                    ·
                      rfl

theorem cell22_4091399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_4091399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091399 prefixEnd_4091399 := by exact prefixLift 4091399
  have htrace : WordTrace (prefixWord ++ tailWord_4091399) baseStart_4091399 baseEnd_4091399 := by
    simpa [prefixWord, tailWord_4091399, baseEnd_4091399] using wordTrace_append hprefix tailTrace_4091399
  have hstable : (prefixWord ++ tailWord_4091399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091399).length < 2 ^ (prefixWord ++ tailWord_4091399).sum := by decide
  have hdescent : baseEnd_4091399 < baseStart_4091399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091405 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_4091405 : Nat := 118140960795 + 4091405 * 2 ^ 59
def prefixEnd_4091405 : Nat := 4983230072969 + 3 ^ 40 * 4091405 * 2
def baseEnd_4091405 : Nat := 1400571544805780061880985

theorem tailTrace_4091405 : CollatzResearch.WordTrace tailWord_4091405 prefixEnd_4091405 1400571544805780061880985 := by
  unfold tailWord_4091405
  simp only [CollatzResearch.WordTrace]
  refine ⟨149225799742545916188275669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99483866495030610792183779 149225799742545916188275669)
  ·
    refine ⟨3497479681465919910662711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 149225799742545916188275669 3497479681465919910662711)
    ·
      refine ⟨5246219522198879865994067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3497479681465919910662711 5246219522198879865994067)
      ·
        refine ⟨7869329283298319798991101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5246219522198879865994067 7869329283298319798991101)
        ·
          refine ⟨2950998481236869924621663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7869329283298319798991101 2950998481236869924621663)
          ·
            refine ⟨4426497721855304886932495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2950998481236869924621663 4426497721855304886932495)
            ·
              refine ⟨6639746582782957330398743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426497721855304886932495 6639746582782957330398743)
              ·
                refine ⟨9959619874174435995598115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6639746582782957330398743 9959619874174435995598115)
                ·
                  refine ⟨14939429811261653993397173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9959619874174435995598115 14939429811261653993397173)
                  ·
                    refine ⟨1400571544805780061880985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14939429811261653993397173 1400571544805780061880985)
                    ·
                      rfl

theorem cell22_4091405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_4091405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091405 prefixEnd_4091405 := by exact prefixLift 4091405
  have htrace : WordTrace (prefixWord ++ tailWord_4091405) baseStart_4091405 baseEnd_4091405 := by
    simpa [prefixWord, tailWord_4091405, baseEnd_4091405] using wordTrace_append hprefix tailTrace_4091405
  have hstable : (prefixWord ++ tailWord_4091405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091405).length < 2 ^ (prefixWord ++ tailWord_4091405).sum := by decide
  have hdescent : baseEnd_4091405 < baseStart_4091405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091442 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_4091442 : Nat := 118140960795 + 4091442 * 2 ^ 59
def prefixEnd_4091442 : Nat := 4983230072969 + 3 ^ 40 * 4091442 * 2
def baseEnd_4091442 : Nat := 1400584210661924298705871

theorem tailTrace_4091442 : CollatzResearch.WordTrace tailWord_4091442 prefixEnd_4091442 1400584210661924298705871 := by
  unfold tailWord_4091442
  simp only [CollatzResearch.WordTrace]
  refine ⟨37306787310852967876843145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99484766162274581004915053 37306787310852967876843145)
  ·
    refine ⟨27980090483139725907632359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37306787310852967876843145 27980090483139725907632359)
    ·
      refine ⟨41970135724709588861448539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27980090483139725907632359 41970135724709588861448539)
      ·
        refine ⟨62955203587064383292172809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41970135724709588861448539 62955203587064383292172809)
        ·
          refine ⟨47216402690298287469129607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62955203587064383292172809 47216402690298287469129607)
          ·
            refine ⟨70824604035447431203694411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47216402690298287469129607 70824604035447431203694411)
            ·
              refine ⟨106236906053171146805541617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70824604035447431203694411 106236906053171146805541617)
              ·
                refine ⟨79677679539878360104156213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106236906053171146805541617 79677679539878360104156213)
                ·
                  refine ⟨7469782456863596259764645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79677679539878360104156213 7469782456863596259764645)
                  ·
                    refine ⟨1400584210661924298705871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7469782456863596259764645 1400584210661924298705871)
                    ·
                      rfl

theorem cell22_4091442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_4091442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091442 prefixEnd_4091442 := by exact prefixLift 4091442
  have htrace : WordTrace (prefixWord ++ tailWord_4091442) baseStart_4091442 baseEnd_4091442 := by
    simpa [prefixWord, tailWord_4091442, baseEnd_4091442] using wordTrace_append hprefix tailTrace_4091442
  have hstable : (prefixWord ++ tailWord_4091442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091442).length < 2 ^ (prefixWord ++ tailWord_4091442).sum := by decide
  have hdescent : baseEnd_4091442 < baseStart_4091442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091463 : List Nat := [1, 1, 4, 1, 6, 1, 2, 1, 5]
def baseStart_4091463 : Nat := 118140960795 + 4091463 * 2 ^ 59
def prefixEnd_4091463 : Nat := 4983230072969 + 3 ^ 40 * 4091463 * 2
def baseEnd_4091463 : Nat := 466863799797029081310269

theorem tailTrace_4091463 : CollatzResearch.WordTrace tailWord_4091463 prefixEnd_4091463 466863799797029081310269 := by
  unfold tailWord_4091463
  simp only [CollatzResearch.WordTrace]
  refine ⟨149227915176335792093887043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99485276784223861395924695 149227915176335792093887043)
  ·
    refine ⟨223841872764503688140830565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149227915176335792093887043 223841872764503688140830565)
    ·
      refine ⟨41970351143344441526405731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223841872764503688140830565 41970351143344441526405731)
      ·
        refine ⟨62955526715016662289608597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41970351143344441526405731 62955526715016662289608597)
        ·
          refine ⟨2951040314766406044825403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62955526715016662289608597 2951040314766406044825403)
          ·
            refine ⟨4426560472149609067238105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2951040314766406044825403 4426560472149609067238105)
            ·
              refine ⟨3319920354112206800428579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4426560472149609067238105 3319920354112206800428579)
              ·
                refine ⟨4979880531168310200642869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3319920354112206800428579 4979880531168310200642869)
                ·
                  refine ⟨466863799797029081310269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4979880531168310200642869 466863799797029081310269)
                  ·
                    rfl

theorem cell22_4091463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 5].length) (baseStart_4091463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091463 prefixEnd_4091463 := by exact prefixLift 4091463
  have htrace : WordTrace (prefixWord ++ tailWord_4091463) baseStart_4091463 baseEnd_4091463 := by
    simpa [prefixWord, tailWord_4091463, baseEnd_4091463] using wordTrace_append hprefix tailTrace_4091463
  have hstable : (prefixWord ++ tailWord_4091463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091463).length < 2 ^ (prefixWord ++ tailWord_4091463).sum := by decide
  have hdescent : baseEnd_4091463 < baseStart_4091463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091472 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 1, 5]
def baseStart_4091472 : Nat := 118140960795 + 4091472 * 2 ^ 59
def prefixEnd_4091472 : Nat := 4983230072969 + 3 ^ 40 * 4091472 * 2
def baseEnd_4091472 : Nat := 1400594480275014220455779

theorem tailTrace_4091472 : CollatzResearch.WordTrace tailWord_4091472 prefixEnd_4091472 1400594480275014220455779 := by
  unfold tailWord_4091472
  simp only [CollatzResearch.WordTrace]
  refine ⟨74614121716651593315482335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99485495622202124420643113 74614121716651593315482335)
  ·
    refine ⟨111921182574977389973223503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74614121716651593315482335 111921182574977389973223503)
    ·
      refine ⟨167881773862466084959835255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111921182574977389973223503 167881773862466084959835255)
      ·
        refine ⟨251822660793699127439752883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167881773862466084959835255 251822660793699127439752883)
        ·
          refine ⟨377733991190548691159629325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251822660793699127439752883 377733991190548691159629325)
          ·
            refine ⟨141650246696455759184860997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377733991190548691159629325 141650246696455759184860997)
            ·
              refine ⟨26559421255585454847161437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141650246696455759184860997 26559421255585454847161437)
              ·
                refine ⟨9959782970844545567685539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26559421255585454847161437 9959782970844545567685539)
                ·
                  refine ⟨14939674456266818351528309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9959782970844545567685539 14939674456266818351528309)
                  ·
                    refine ⟨1400594480275014220455779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14939674456266818351528309 1400594480275014220455779)
                    ·
                      rfl

theorem cell22_4091472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_4091472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091472 prefixEnd_4091472 := by exact prefixLift 4091472
  have htrace : WordTrace (prefixWord ++ tailWord_4091472) baseStart_4091472 baseEnd_4091472 := by
    simpa [prefixWord, tailWord_4091472, baseEnd_4091472] using wordTrace_append hprefix tailTrace_4091472
  have hstable : (prefixWord ++ tailWord_4091472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091472).length < 2 ^ (prefixWord ++ tailWord_4091472).sum := by decide
  have hdescent : baseEnd_4091472 < baseStart_4091472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091502 : List Nat := [4, 1, 2, 2, 13]
def baseStart_4091502 : Nat := 118140960795 + 4091502 * 2 ^ 59
def prefixEnd_4091502 : Nat := 4983230072969 + 3 ^ 40 * 4091502 * 2
def baseEnd_4091502 : Nat := 5763805555095078774509

theorem tailTrace_4091502 : CollatzResearch.WordTrace tailWord_4091502 prefixEnd_4091502 5763805555095078774509 := by
  unfold tailWord_4091502
  simp only [CollatzResearch.WordTrace]
  refine ⟨18653667202899312719319595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99486225082129667836371173 18653667202899312719319595)
  ·
    refine ⟨27980500804348969078979393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18653667202899312719319595 27980500804348969078979393)
    ·
      refine ⟨20985375603261726809234545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27980500804348969078979393 20985375603261726809234545)
      ·
        refine ⟨15739031702446295106925909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20985375603261726809234545 15739031702446295106925909)
        ·
          refine ⟨5763805555095078774509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 15739031702446295106925909 5763805555095078774509)
          ·
            rfl

theorem cell22_4091502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 13].length) (baseStart_4091502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091502 prefixEnd_4091502 := by exact prefixLift 4091502
  have htrace : WordTrace (prefixWord ++ tailWord_4091502) baseStart_4091502 baseEnd_4091502 := by
    simpa [prefixWord, tailWord_4091502, baseEnd_4091502] using wordTrace_append hprefix tailTrace_4091502
  have hstable : (prefixWord ++ tailWord_4091502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091502).length < 2 ^ (prefixWord ++ tailWord_4091502).sum := by decide
  have hdescent : baseEnd_4091502 < baseStart_4091502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091504 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 2, 4]
def baseStart_4091504 : Nat := 118140960795 + 4091504 * 2 ^ 59
def prefixEnd_4091504 : Nat := 4983230072969 + 3 ^ 40 * 4091504 * 2
def baseEnd_4091504 : Nat := 1400605434528976803655681

theorem tailTrace_4091504 : CollatzResearch.WordTrace tailWord_4091504 prefixEnd_4091504 1400605434528976803655681 := by
  unfold tailWord_4091504
  simp only [CollatzResearch.WordTrace]
  refine ⟨74614705284593628048064783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99486273712791504064086377 74614705284593628048064783)
  ·
    refine ⟨111922057926890442072097175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74614705284593628048064783 111922057926890442072097175)
    ·
      refine ⟨167883086890335663108145763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111922057926890442072097175 167883086890335663108145763)
      ·
        refine ⟨251824630335503494662218645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167883086890335663108145763 251824630335503494662218645)
        ·
          refine ⟨11804279546976726312291499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251824630335503494662218645 11804279546976726312291499)
          ·
            refine ⟨17706419320465089468437249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11804279546976726312291499 17706419320465089468437249)
            ·
              refine ⟨13279814490348817101327937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17706419320465089468437249 13279814490348817101327937)
              ·
                refine ⟨9959860867761612825995953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13279814490348817101327937 9959860867761612825995953)
                ·
                  refine ⟨7469895650821209619496965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9959860867761612825995953 7469895650821209619496965)
                  ·
                    refine ⟨1400605434528976803655681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7469895650821209619496965 1400605434528976803655681)
                    ·
                      rfl

theorem cell22_4091504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_4091504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091504 prefixEnd_4091504 := by exact prefixLift 4091504
  have htrace : WordTrace (prefixWord ++ tailWord_4091504) baseStart_4091504 baseEnd_4091504 := by
    simpa [prefixWord, tailWord_4091504, baseEnd_4091504] using wordTrace_append hprefix tailTrace_4091504
  have hstable : (prefixWord ++ tailWord_4091504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091504).length < 2 ^ (prefixWord ++ tailWord_4091504).sum := by decide
  have hdescent : baseEnd_4091504 < baseStart_4091504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091506 : List Nat := [3, 2, 1, 2, 3, 1, 1, 4, 2, 3]
def baseStart_4091506 : Nat := 118140960795 + 4091506 * 2 ^ 59
def prefixEnd_4091506 : Nat := 4983230072969 + 3 ^ 40 * 4091506 * 2
def baseEnd_4091506 : Nat := 1400606119169849465105675

theorem tailTrace_4091506 : CollatzResearch.WordTrace tailWord_4091506 prefixEnd_4091506 1400606119169849465105675 := by
  unfold tailWord_4091506
  simp only [CollatzResearch.WordTrace]
  refine ⟨37307370878795002609425593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99486322343453340291801581 37307370878795002609425593)
  ·
    refine ⟨27980528159096251957069195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37307370878795002609425593 27980528159096251957069195)
    ·
      refine ⟨41970792238644377935603793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27980528159096251957069195 41970792238644377935603793)
      ·
        refine ⟨31478094178983283451702845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41970792238644377935603793 31478094178983283451702845)
        ·
          refine ⟨11804285317118731294388567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31478094178983283451702845 11804285317118731294388567)
          ·
            refine ⟨17706427975678096941582851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11804285317118731294388567 17706427975678096941582851)
            ·
              refine ⟨26559641963517145412374277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17706427975678096941582851 26559641963517145412374277)
              ·
                refine ⟨4979932868159464764820177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26559641963517145412374277 4979932868159464764820177)
                ·
                  refine ⟨3734949651119598573615133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4979932868159464764820177 3734949651119598573615133)
                  ·
                    refine ⟨1400606119169849465105675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3734949651119598573615133 1400606119169849465105675)
                    ·
                      rfl

theorem cell22_4091506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_4091506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091506 prefixEnd_4091506 := by exact prefixLift 4091506
  have htrace : WordTrace (prefixWord ++ tailWord_4091506) baseStart_4091506 baseEnd_4091506 := by
    simpa [prefixWord, tailWord_4091506, baseEnd_4091506] using wordTrace_append hprefix tailTrace_4091506
  have hstable : (prefixWord ++ tailWord_4091506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091506).length < 2 ^ (prefixWord ++ tailWord_4091506).sum := by decide
  have hdescent : baseEnd_4091506 < baseStart_4091506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091532 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_4091532 : Nat := 118140960795 + 4091532 * 2 ^ 59
def prefixEnd_4091532 : Nat := 4983230072969 + 3 ^ 40 * 4091532 * 2
def baseEnd_4091532 : Nat := 1400615019501194063955595

theorem tailTrace_4091532 : CollatzResearch.WordTrace tailWord_4091532 prefixEnd_4091532 1400615019501194063955595 := by
  unfold tailWord_4091532
  simp only [CollatzResearch.WordTrace]
  refine ⟨74615215906542908439074425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99486954542057211252099233 74615215906542908439074425)
  ·
    refine ⟨55961411929907181329305819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74615215906542908439074425 55961411929907181329305819)
    ·
      refine ⟨83942117894860771993958729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55961411929907181329305819 83942117894860771993958729)
      ·
        refine ⟨62956588421145578995469047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83942117894860771993958729 62956588421145578995469047)
        ·
          refine ⟨94434882631718368493203571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62956588421145578995469047 94434882631718368493203571)
          ·
            refine ⟨141652323947577552739805357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94434882631718368493203571 141652323947577552739805357)
            ·
              refine ⟨53119621480341582277427009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141652323947577552739805357 53119621480341582277427009)
              ·
                refine ⟨39839716110256186708070257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53119621480341582277427009 39839716110256186708070257)
                ·
                  refine ⟨29879787082692140031052693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39839716110256186708070257 29879787082692140031052693)
                  ·
                    refine ⟨1400615019501194063955595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29879787082692140031052693 1400615019501194063955595)
                    ·
                      rfl

theorem cell22_4091532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_4091532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091532 prefixEnd_4091532 := by exact prefixLift 4091532
  have htrace : WordTrace (prefixWord ++ tailWord_4091532) baseStart_4091532 baseEnd_4091532 := by
    simpa [prefixWord, tailWord_4091532, baseEnd_4091532] using wordTrace_append hprefix tailTrace_4091532
  have hstable : (prefixWord ++ tailWord_4091532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091532).length < 2 ^ (prefixWord ++ tailWord_4091532).sum := by decide
  have hdescent : baseEnd_4091532 < baseStart_4091532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091538 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 2, 4]
def baseStart_4091538 : Nat := 118140960795 + 4091538 * 2 ^ 59
def prefixEnd_4091538 : Nat := 4983230072969 + 3 ^ 40 * 4091538 * 2
def baseEnd_4091538 : Nat := 1400617073423812048305577

theorem tailTrace_4091538 : CollatzResearch.WordTrace tailWord_4091538 prefixEnd_4091538 1400617073423812048305577 := by
  unfold tailWord_4091538
  simp only [CollatzResearch.WordTrace]
  refine ⟨37307662662766019975716817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99487100434042719935244845 37307662662766019975716817)
  ·
    refine ⟨27980746997074514981787613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37307662662766019975716817 27980746997074514981787613)
    ·
      refine ⟨10492780123902943118170355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27980746997074514981787613 10492780123902943118170355)
      ·
        refine ⟨15739170185854414677255533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10492780123902943118170355 15739170185854414677255533)
        ·
          refine ⟨5902188819695405503970825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15739170185854414677255533 5902188819695405503970825)
          ·
            refine ⟨4426641614771554127978119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5902188819695405503970825 4426641614771554127978119)
            ·
              refine ⟨6639962422157331191967179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426641614771554127978119 6639962422157331191967179)
              ·
                refine ⟨9959943633235996787950769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6639962422157331191967179 9959943633235996787950769)
                ·
                  refine ⟨7469957724926997590963077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9959943633235996787950769 7469957724926997590963077)
                  ·
                    refine ⟨1400617073423812048305577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7469957724926997590963077 1400617073423812048305577)
                    ·
                      rfl

theorem cell22_4091538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_4091538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091538 prefixEnd_4091538 := by exact prefixLift 4091538
  have htrace : WordTrace (prefixWord ++ tailWord_4091538) baseStart_4091538 baseEnd_4091538 := by
    simpa [prefixWord, tailWord_4091538, baseEnd_4091538] using wordTrace_append hprefix tailTrace_4091538
  have hstable : (prefixWord ++ tailWord_4091538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091538).length < 2 ^ (prefixWord ++ tailWord_4091538).sum := by decide
  have hdescent : baseEnd_4091538 < baseStart_4091538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091581 : List Nat := [1, 4, 1, 2, 1, 2, 5, 1, 5]
def baseStart_4091581 : Nat := 118140960795 + 4091581 * 2 ^ 59
def prefixEnd_4091581 : Nat := 4983230072969 + 3 ^ 40 * 4091581 * 2
def baseEnd_4091581 : Nat := 466877264400858089826815

theorem tailTrace_4091581 : CollatzResearch.WordTrace tailWord_4091581 prefixEnd_4091581 466877264400858089826815 := by
  unfold tailWord_4091581
  simp only [CollatzResearch.WordTrace]
  refine ⟨149232218989908298246682597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99488145993272198831121731 149232218989908298246682597)
  ·
    refine ⟨27981041060607805921252987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149232218989908298246682597 27981041060607805921252987)
    ·
      refine ⟨41971561590911708881879481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27981041060607805921252987 41971561590911708881879481)
      ·
        refine ⟨31478671193183781661409611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41971561590911708881879481 31478671193183781661409611)
        ·
          refine ⟨47218006789775672492114417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31478671193183781661409611 47218006789775672492114417)
          ·
            refine ⟨35413505092331754369085813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47218006789775672492114417 35413505092331754369085813)
            ·
              refine ⟨3320016102406101972101795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35413505092331754369085813 3320016102406101972101795)
              ·
                refine ⟨4980024153609152958152693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3320016102406101972101795 4980024153609152958152693)
                ·
                  refine ⟨466877264400858089826815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4980024153609152958152693 466877264400858089826815)
                  ·
                    rfl

theorem cell22_4091581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_4091581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091581 prefixEnd_4091581 := by exact prefixLift 4091581
  have htrace : WordTrace (prefixWord ++ tailWord_4091581) baseStart_4091581 baseEnd_4091581 := by
    simpa [prefixWord, tailWord_4091581, baseEnd_4091581] using wordTrace_append hprefix tailTrace_4091581
  have hstable : (prefixWord ++ tailWord_4091581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091581).length < 2 ^ (prefixWord ++ tailWord_4091581).sum := by decide
  have hdescent : baseEnd_4091581 < baseStart_4091581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091626 : List Nat := [3, 1, 3, 1, 1, 1, 2, 6, 4]
def baseStart_4091626 : Nat := 118140960795 + 4091626 * 2 ^ 59
def prefixEnd_4091626 : Nat := 4983230072969 + 3 ^ 40 * 4091626 * 2
def baseEnd_4091626 : Nat := 466882399207403050701769

theorem tailTrace_4091626 : CollatzResearch.WordTrace tailWord_4091626 prefixEnd_4091626 466882399207403050701769 := by
  unfold tailWord_4091626
  simp only [CollatzResearch.WordTrace]
  refine ⟨37308465068686317733017683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99489240183163513954713821 37308465068686317733017683)
  ·
    refine ⟨55962697603029476599526525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37308465068686317733017683 55962697603029476599526525)
    ·
      refine ⟨20986011601136053724822447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55962697603029476599526525 20986011601136053724822447)
      ·
        refine ⟨31479017401704080587233671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20986011601136053724822447 31479017401704080587233671)
        ·
          refine ⟨47218526102556120880850507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31479017401704080587233671 47218526102556120880850507)
          ·
            refine ⟨70827789153834181321275761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47218526102556120880850507 70827789153834181321275761)
            ·
              refine ⟨53120841865375635990956821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70827789153834181321275761 53120841865375635990956821)
              ·
                refine ⟨2490039462439482937076101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53120841865375635990956821 2490039462439482937076101)
                ·
                  refine ⟨466882399207403050701769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2490039462439482937076101 466882399207403050701769)
                  ·
                    rfl

theorem cell22_4091626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_4091626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091626 prefixEnd_4091626 := by exact prefixLift 4091626
  have htrace : WordTrace (prefixWord ++ tailWord_4091626) baseStart_4091626 baseEnd_4091626 := by
    simpa [prefixWord, tailWord_4091626, baseEnd_4091626] using wordTrace_append hprefix tailTrace_4091626
  have hstable : (prefixWord ++ tailWord_4091626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091626).length < 2 ^ (prefixWord ++ tailWord_4091626).sum := by decide
  have hdescent : baseEnd_4091626 < baseStart_4091626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091656 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 2, 4]
def baseStart_4091656 : Nat := 118140960795 + 4091656 * 2 ^ 59
def prefixEnd_4091656 : Nat := 4983230072969 + 3 ^ 40 * 4091656 * 2
def baseEnd_4091656 : Nat := 1400657467235299073855215

theorem tailTrace_4091656 : CollatzResearch.WordTrace tailWord_4091656 prefixEnd_4091656 1400657467235299073855215 := by
  unfold tailWord_4091656
  simp only [CollatzResearch.WordTrace]
  refine ⟨74617477232318293027831411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99489969643091057370441881 74617477232318293027831411)
  ·
    refine ⟨111926215848477439541747117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74617477232318293027831411 111926215848477439541747117)
    ·
      refine ⟨41972330943179039828155169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111926215848477439541747117 41972330943179039828155169)
      ·
        refine ⟨31479248207384279871116377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41972330943179039828155169 31479248207384279871116377)
        ·
          refine ⟨23609436155538209903337283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31479248207384279871116377 23609436155538209903337283)
          ·
            refine ⟨35414154233307314855005925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23609436155538209903337283 35414154233307314855005925)
            ·
              refine ⟨6640153918745121535313611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35414154233307314855005925 6640153918745121535313611)
              ·
                refine ⟨9960230878117682302970417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6640153918745121535313611 9960230878117682302970417)
                ·
                  refine ⟨7470173158588261727227813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9960230878117682302970417 7470173158588261727227813)
                  ·
                    refine ⟨1400657467235299073855215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7470173158588261727227813 1400657467235299073855215)
                    ·
                      rfl

theorem cell22_4091656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_4091656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091656 prefixEnd_4091656 := by exact prefixLift 4091656
  have htrace : WordTrace (prefixWord ++ tailWord_4091656) baseStart_4091656 baseEnd_4091656 := by
    simpa [prefixWord, tailWord_4091656, baseEnd_4091656] using wordTrace_append hprefix tailTrace_4091656
  have hstable : (prefixWord ++ tailWord_4091656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091656).length < 2 ^ (prefixWord ++ tailWord_4091656).sum := by decide
  have hdescent : baseEnd_4091656 < baseStart_4091656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091720 : List Nat := [2, 1, 3, 1, 1, 5, 2, 3, 1, 3]
def baseStart_4091720 : Nat := 118140960795 + 4091720 * 2 ^ 59
def prefixEnd_4091720 : Nat := 4983230072969 + 3 ^ 40 * 4091720 * 2
def baseEnd_4091720 : Nat := 1400679375743224240255019

theorem tailTrace_4091720 : CollatzResearch.WordTrace tailWord_4091720 prefixEnd_4091720 1400679375743224240255019 := by
  unfold tailWord_4091720
  simp only [CollatzResearch.WordTrace]
  refine ⟨74618644368202362492996307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99491525824269816657328409 74618644368202362492996307)
  ·
    refine ⟨111927966552303543739494461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74618644368202362492996307 111927966552303543739494461)
    ·
      refine ⟨41972987457113828902310423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111927966552303543739494461 41972987457113828902310423)
      ·
        refine ⟨62959481185670743353465635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41972987457113828902310423 62959481185670743353465635)
        ·
          refine ⟨94439221778506115030198453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62959481185670743353465635 94439221778506115030198453)
          ·
            refine ⟨8853677041734948284081105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94439221778506115030198453 8853677041734948284081105)
            ·
              refine ⟨6640257781301211213060829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8853677041734948284081105 6640257781301211213060829)
              ·
                refine ⟨2490096667987954204897811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6640257781301211213060829 2490096667987954204897811)
                ·
                  refine ⟨3735145001981931307346717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2490096667987954204897811 3735145001981931307346717)
                  ·
                    refine ⟨1400679375743224240255019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3735145001981931307346717 1400679375743224240255019)
                    ·
                      rfl

theorem cell22_4091720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_4091720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091720 prefixEnd_4091720 := by exact prefixLift 4091720
  have htrace : WordTrace (prefixWord ++ tailWord_4091720) baseStart_4091720 baseEnd_4091720 := by
    simpa [prefixWord, tailWord_4091720, baseEnd_4091720] using wordTrace_append hprefix tailTrace_4091720
  have hstable : (prefixWord ++ tailWord_4091720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091720).length < 2 ^ (prefixWord ++ tailWord_4091720).sum := by decide
  have hdescent : baseEnd_4091720 < baseStart_4091720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091733 : List Nat := [1, 3, 2, 2, 2, 4, 1, 2, 5]
def baseStart_4091733 : Nat := 118140960795 + 4091733 * 2 ^ 59
def prefixEnd_4091733 : Nat := 4983230072969 + 3 ^ 40 * 4091733 * 2
def baseEnd_4091733 : Nat := 466894608636298846559993

theorem tailTrace_4091733 : CollatzResearch.WordTrace tailWord_4091733 prefixEnd_4091733 466894608636298846559993 := by
  unfold tailWord_4091733
  simp only [CollatzResearch.WordTrace]
  refine ⟨149237762885357628206215853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99491841923571752137477235 149237762885357628206215853)
  ·
    refine ⟨55964161082009110577330945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149237762885357628206215853 55964161082009110577330945)
    ·
      refine ⟨41973120811506832932998209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55964161082009110577330945 41973120811506832932998209)
      ·
        refine ⟨31479840608630124699748657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41973120811506832932998209 31479840608630124699748657)
        ·
          refine ⟨23609880456472593524811493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31479840608630124699748657 23609880456472593524811493)
          ·
            refine ⟨4426852585588611285902155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23609880456472593524811493 4426852585588611285902155)
            ·
              refine ⟨6640278878382916928853233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426852585588611285902155 6640278878382916928853233)
              ·
                refine ⟨4980209158787187696639925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6640278878382916928853233 4980209158787187696639925)
                ·
                  refine ⟨466894608636298846559993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4980209158787187696639925 466894608636298846559993)
                  ·
                    rfl

theorem cell22_4091733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_4091733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091733 prefixEnd_4091733 := by exact prefixLift 4091733
  have htrace : WordTrace (prefixWord ++ tailWord_4091733) baseStart_4091733 baseEnd_4091733 := by
    simpa [prefixWord, tailWord_4091733, baseEnd_4091733] using wordTrace_append hprefix tailTrace_4091733
  have hstable : (prefixWord ++ tailWord_4091733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091733).length < 2 ^ (prefixWord ++ tailWord_4091733).sum := by decide
  have hdescent : baseEnd_4091733 < baseStart_4091733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091776 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 6, 3]
def baseStart_4091776 : Nat := 118140960795 + 4091776 * 2 ^ 59
def prefixEnd_4091776 : Nat := 4983230072969 + 3 ^ 40 * 4091776 * 2
def baseEnd_4091776 : Nat := 1400698545687658760854847

theorem tailTrace_4091776 : CollatzResearch.WordTrace tailWord_4091776 prefixEnd_4091776 1400698545687658760854847 := by
  unfold tailWord_4091776
  simp only [CollatzResearch.WordTrace]
  refine ⟨74619665612100923275015591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99492887482801231033354121 74619665612100923275015591)
  ·
    refine ⟨111929498418151384912523387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74619665612100923275015591 111929498418151384912523387)
    ·
      refine ⟨167894247627227077368785081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111929498418151384912523387 167894247627227077368785081)
      ·
        refine ⟨125920685720420308026588811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167894247627227077368785081 125920685720420308026588811)
        ·
          refine ⟨188881028580630462039883217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125920685720420308026588811 188881028580630462039883217)
          ·
            refine ⟨141660771435472846529912413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188881028580630462039883217 141660771435472846529912413)
            ·
              refine ⟨53122789288302317448717155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141660771435472846529912413 53122789288302317448717155)
              ·
                refine ⟨79684183932453476173075733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53122789288302317448717155 79684183932453476173075733)
                ·
                  refine ⟨3735196121833756695612925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79684183932453476173075733 3735196121833756695612925)
                  ·
                    refine ⟨1400698545687658760854847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3735196121833756695612925 1400698545687658760854847)
                    ·
                      rfl

theorem cell22_4091776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 6, 3].length) (baseStart_4091776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091776 prefixEnd_4091776 := by exact prefixLift 4091776
  have htrace : WordTrace (prefixWord ++ tailWord_4091776) baseStart_4091776 baseEnd_4091776 := by
    simpa [prefixWord, tailWord_4091776, baseEnd_4091776] using wordTrace_append hprefix tailTrace_4091776
  have hstable : (prefixWord ++ tailWord_4091776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091776).length < 2 ^ (prefixWord ++ tailWord_4091776).sum := by decide
  have hdescent : baseEnd_4091776 < baseStart_4091776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091855 : List Nat := [1, 1, 2, 1, 1, 5, 3, 4, 1, 3]
def baseStart_4091855 : Nat := 118140960795 + 4091855 * 2 ^ 59
def prefixEnd_4091855 : Nat := 4983230072969 + 3 ^ 40 * 4091855 * 2
def baseEnd_4091855 : Nat := 1400725589002128888129605

theorem tailTrace_4091855 : CollatzResearch.WordTrace tailWord_4091855 prefixEnd_4091855 1400725589002128888129605 := by
  unfold tailWord_4091855
  simp only [CollatzResearch.WordTrace]
  refine ⟨149242212590915643042157019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99494808393943762028104679 149242212590915643042157019)
  ·
    refine ⟨223863318886373464563235529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149242212590915643042157019 223863318886373464563235529)
    ·
      refine ⟨167897489164780098422426647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223863318886373464563235529 167897489164780098422426647)
      ·
        refine ⟨251846233747170147633639971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167897489164780098422426647 251846233747170147633639971)
        ·
          refine ⟨377769350620755221450459957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251846233747170147633639971 377769350620755221450459957)
          ·
            refine ⟨35415876620695802010980621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 377769350620755221450459957 35415876620695802010980621)
            ·
              refine ⟨13280953732760925754117733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35415876620695802010980621 13280953732760925754117733)
              ·
                refine ⟨2490178824892673578897075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13280953732760925754117733 2490178824892673578897075)
                ·
                  refine ⟨3735268237339010368345613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2490178824892673578897075 3735268237339010368345613)
                  ·
                    refine ⟨1400725589002128888129605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3735268237339010368345613 1400725589002128888129605)
                    ·
                      rfl

theorem cell22_4091855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 1, 3].length) (baseStart_4091855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091855 prefixEnd_4091855 := by exact prefixLift 4091855
  have htrace : WordTrace (prefixWord ++ tailWord_4091855) baseStart_4091855 baseEnd_4091855 := by
    simpa [prefixWord, tailWord_4091855, baseEnd_4091855] using wordTrace_append hprefix tailTrace_4091855
  have hstable : (prefixWord ++ tailWord_4091855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091855).length < 2 ^ (prefixWord ++ tailWord_4091855).sum := by decide
  have hdescent : baseEnd_4091855 < baseStart_4091855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091902 : List Nat := [4, 2, 2, 2, 1, 3, 1, 2, 5]
def baseStart_4091902 : Nat := 118140960795 + 4091902 * 2 ^ 59
def prefixEnd_4091902 : Nat := 4983230072969 + 3 ^ 40 * 4091902 * 2
def baseEnd_4091902 : Nat := 466913892687545477401487

theorem tailTrace_4091902 : CollatzResearch.WordTrace tailWord_4091902 prefixEnd_4091902 466913892687545477401487 := by
  unfold tailWord_4091902
  simp only [CollatzResearch.WordTrace]
  refine ⟨18655490852718171258639745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99495951214496913379411973 18655490852718171258639745)
  ·
    refine ⟨13991618139538628443979809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18655490852718171258639745 13991618139538628443979809)
    ·
      refine ⟨10493713604653971332984857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13991618139538628443979809 10493713604653971332984857)
      ·
        refine ⟨7870285203490478499738643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10493713604653971332984857 7870285203490478499738643)
        ·
          refine ⟨11805427805235717749607965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7870285203490478499738643 11805427805235717749607965)
          ·
            refine ⟨4427035426963394156102987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11805427805235717749607965 4427035426963394156102987)
            ·
              refine ⟨6640553140445091234154481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4427035426963394156102987 6640553140445091234154481)
              ·
                refine ⟨4980414855333818425615861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6640553140445091234154481 4980414855333818425615861)
                ·
                  refine ⟨466913892687545477401487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4980414855333818425615861 466913892687545477401487)
                  ·
                    rfl

theorem cell22_4091902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_4091902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091902 prefixEnd_4091902 := by exact prefixLift 4091902
  have htrace : WordTrace (prefixWord ++ tailWord_4091902) baseStart_4091902 baseEnd_4091902 := by
    simpa [prefixWord, tailWord_4091902, baseEnd_4091902] using wordTrace_append hprefix tailTrace_4091902
  have hstable : (prefixWord ++ tailWord_4091902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091902).length < 2 ^ (prefixWord ++ tailWord_4091902).sum := by decide
  have hdescent : baseEnd_4091902 < baseStart_4091902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091960 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 2, 4]
def baseStart_4091960 : Nat := 118140960795 + 4091960 * 2 ^ 59
def prefixEnd_4091960 : Nat := 4983230072969 + 3 ^ 40 * 4091960 * 2
def baseEnd_4091960 : Nat := 1400761532647943614254283

theorem tailTrace_4091960 : CollatzResearch.WordTrace tailWord_4091960 prefixEnd_4091960 1400761532647943614254283 := by
  unfold tailWord_4091960
  simp only [CollatzResearch.WordTrace]
  refine ⟨74623021127767622987364667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99497361503690163983152889 74623021127767622987364667)
  ·
    refine ⟨111934531691651434481047001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74623021127767622987364667 111934531691651434481047001)
    ·
      refine ⟨83950898768738575860785251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111934531691651434481047001 83950898768738575860785251)
      ·
        refine ⟨125926348153107863791177877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83950898768738575860785251 125926348153107863791177877)
        ·
          refine ⟨5902797569676931115211463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125926348153107863791177877 5902797569676931115211463)
          ·
            refine ⟨8854196354515396672817195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5902797569676931115211463 8854196354515396672817195)
            ·
              refine ⟨13281294531773095009225793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8854196354515396672817195 13281294531773095009225793)
              ·
                refine ⟨9960970898829821256919345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13281294531773095009225793 9960970898829821256919345)
                ·
                  refine ⟨7470728174122365942689509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9960970898829821256919345 7470728174122365942689509)
                  ·
                    refine ⟨1400761532647943614254283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7470728174122365942689509 1400761532647943614254283)
                    ·
                      rfl

theorem cell22_4091960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_4091960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091960 prefixEnd_4091960 := by exact prefixLift 4091960
  have htrace : WordTrace (prefixWord ++ tailWord_4091960) baseStart_4091960 baseEnd_4091960 := by
    simpa [prefixWord, tailWord_4091960, baseEnd_4091960] using wordTrace_append hprefix tailTrace_4091960
  have hstable : (prefixWord ++ tailWord_4091960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091960).length < 2 ^ (prefixWord ++ tailWord_4091960).sum := by decide
  have hdescent : baseEnd_4091960 < baseStart_4091960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092007 : List Nat := [1, 1, 5, 1, 1, 2, 2, 5, 1, 3]
def baseStart_4092007 : Nat := 118140960795 + 4092007 * 2 ^ 59
def prefixEnd_4092007 : Nat := 4983230072969 + 3 ^ 40 * 4092007 * 2
def baseEnd_4092007 : Nat := 1400777621708451158329139

theorem tailTrace_4092007 : CollatzResearch.WordTrace tailWord_4092007 prefixEnd_4092007 1400777621708451158329139 := by
  unfold tailWord_4092007
  simp only [CollatzResearch.WordTrace]
  refine ⟨149247756486364973001690275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99498504324243315334460183 149247756486364973001690275)
  ·
    refine ⟨223871634729547459502535413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149247756486364973001690275 223871634729547459502535413)
    ·
      refine ⟨20987965755895074328362695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223871634729547459502535413 20987965755895074328362695)
      ·
        refine ⟨31481948633842611492544043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20987965755895074328362695 31481948633842611492544043)
        ·
          refine ⟨47222922950763917238816065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31481948633842611492544043 47222922950763917238816065)
          ·
            refine ⟨35417192213072937929112049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47222922950763917238816065 35417192213072937929112049)
            ·
              refine ⟨26562894159804703446834037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35417192213072937929112049 26562894159804703446834037)
              ·
                refine ⟨2490271327481690948140691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26562894159804703446834037 2490271327481690948140691)
                ·
                  refine ⟨3735406991222536422211037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2490271327481690948140691 3735406991222536422211037)
                  ·
                    refine ⟨1400777621708451158329139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3735406991222536422211037 1400777621708451158329139)
                    ·
                      rfl

theorem cell22_4092007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_4092007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092007 prefixEnd_4092007 := by exact prefixLift 4092007
  have htrace : WordTrace (prefixWord ++ tailWord_4092007) baseStart_4092007 baseEnd_4092007 := by
    simpa [prefixWord, tailWord_4092007, baseEnd_4092007] using wordTrace_append hprefix tailTrace_4092007
  have hstable : (prefixWord ++ tailWord_4092007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092007).length < 2 ^ (prefixWord ++ tailWord_4092007).sum := by decide
  have hdescent : baseEnd_4092007 < baseStart_4092007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092048 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 6]
def baseStart_4092048 : Nat := 118140960795 + 4092048 * 2 ^ 59
def prefixEnd_4092048 : Nat := 4983230072969 + 3 ^ 40 * 4092048 * 2
def baseEnd_4092048 : Nat := 466930552282113572684671

theorem tailTrace_4092048 : CollatzResearch.WordTrace tailWord_4092048 prefixEnd_4092048 466930552282113572684671 := by
  unfold tailWord_4092048
  simp only [CollatzResearch.WordTrace]
  refine ⟨74624625939608218501966399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99499501252810958002621865 74624625939608218501966399)
  ·
    refine ⟨111936938909412327752949599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74624625939608218501966399 111936938909412327752949599)
    ·
      refine ⟨167905408364118491629424399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111936938909412327752949599 167905408364118491629424399)
      ·
        refine ⟨251858112546177737444136599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167905408364118491629424399 251858112546177737444136599)
        ·
          refine ⟨377787168819266606166204899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251858112546177737444136599 377787168819266606166204899)
          ·
            refine ⟨566680753228899909249307349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377787168819266606166204899 566680753228899909249307349)
            ·
              refine ⟨13281580153802341623030641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 566680753228899909249307349 13281580153802341623030641)
              ·
                refine ⟨9961185115351756217272981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13281580153802341623030641 9961185115351756217272981)
                ·
                  refine ⟨466930552282113572684671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9961185115351756217272981 466930552282113572684671)
                  ·
                    rfl

theorem cell22_4092048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 6].length) (baseStart_4092048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092048 prefixEnd_4092048 := by exact prefixLift 4092048
  have htrace : WordTrace (prefixWord ++ tailWord_4092048) baseStart_4092048 baseEnd_4092048 := by
    simpa [prefixWord, tailWord_4092048, baseEnd_4092048] using wordTrace_append hprefix tailTrace_4092048
  have hstable : (prefixWord ++ tailWord_4092048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092048).length < 2 ^ (prefixWord ++ tailWord_4092048).sum := by decide
  have hdescent : baseEnd_4092048 < baseStart_4092048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092050 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_4092050 : Nat := 118140960795 + 4092050 * 2 ^ 59
def prefixEnd_4092050 : Nat := 4983230072969 + 3 ^ 40 * 4092050 * 2
def baseEnd_4092050 : Nat := 1400792341487213379504007

theorem tailTrace_4092050 : CollatzResearch.WordTrace tailWord_4092050 prefixEnd_4092050 1400792341487213379504007 := by
  unfold tailWord_4092050
  simp only [CollatzResearch.WordTrace]
  refine ⟨37312331206302297836376401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99499549883472794230337069 37312331206302297836376401)
  ·
    refine ⟨27984248404726723377282301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37312331206302297836376401 27984248404726723377282301)
    ·
      refine ⟨10494093151772521266480863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27984248404726723377282301 10494093151772521266480863)
      ·
        refine ⟨15741139727658781899721295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10494093151772521266480863 15741139727658781899721295)
        ·
          refine ⟨23611709591488172849581943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15741139727658781899721295 23611709591488172849581943)
          ·
            refine ⟨35417564387232259274372915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23611709591488172849581943 35417564387232259274372915)
            ·
              refine ⟨53126346580848388911559373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35417564387232259274372915 53126346580848388911559373)
              ·
                refine ⟨19922379967818145841834765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53126346580848388911559373 19922379967818145841834765)
                ·
                  refine ⟨7470892487931804690688037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19922379967818145841834765 7470892487931804690688037)
                  ·
                    refine ⟨1400792341487213379504007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7470892487931804690688037 1400792341487213379504007)
                    ·
                      rfl

theorem cell22_4092050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_4092050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092050 prefixEnd_4092050 := by exact prefixLift 4092050
  have htrace : WordTrace (prefixWord ++ tailWord_4092050) baseStart_4092050 baseEnd_4092050 := by
    simpa [prefixWord, tailWord_4092050, baseEnd_4092050] using wordTrace_append hprefix tailTrace_4092050
  have hstable : (prefixWord ++ tailWord_4092050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092050).length < 2 ^ (prefixWord ++ tailWord_4092050).sum := by decide
  have hdescent : baseEnd_4092050 < baseStart_4092050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092093 : List Nat := [1, 4, 1, 2, 1, 1, 1, 11]
def baseStart_4092093 : Nat := 118140960795 + 4092093 * 2 ^ 59
def prefixEnd_4092093 : Nat := 4983230072969 + 3 ^ 40 * 4092093 * 2
def baseEnd_4092093 : Nat := 155645229029552844519875

theorem tailTrace_4092093 : CollatzResearch.WordTrace tailWord_4092093 prefixEnd_4092093 155645229029552844519875 := by
  unfold tailWord_4092093
  simp only [CollatzResearch.WordTrace]
  refine ⟨149250893164053409689320933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99500595442702273126213955 149250893164053409689320933)
  ·
    refine ⟨27984542468260014316747675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149250893164053409689320933 27984542468260014316747675)
    ·
      refine ⟨41976813702390021475121513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27984542468260014316747675 41976813702390021475121513)
      ·
        refine ⟨31482610276792516106341135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41976813702390021475121513 31482610276792516106341135)
        ·
          refine ⟨47223915415188774159511703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31482610276792516106341135 47223915415188774159511703)
          ·
            refine ⟨70835873122783161239267555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47223915415188774159511703 70835873122783161239267555)
            ·
              refine ⟨106253809684174741858901333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70835873122783161239267555 106253809684174741858901333)
              ·
                refine ⟨155645229029552844519875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 106253809684174741858901333 155645229029552844519875)
                ·
                  rfl

theorem cell22_4092093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 11].length) (baseStart_4092093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092093 prefixEnd_4092093 := by exact prefixLift 4092093
  have htrace : WordTrace (prefixWord ++ tailWord_4092093) baseStart_4092093 baseEnd_4092093 := by
    simpa [prefixWord, tailWord_4092093, baseEnd_4092093] using wordTrace_append hprefix tailTrace_4092093
  have hstable : (prefixWord ++ tailWord_4092093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092093).length < 2 ^ (prefixWord ++ tailWord_4092093).sum := by decide
  have hdescent : baseEnd_4092093 < baseStart_4092093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092110 : List Nat := [4, 1, 1, 1, 4, 2, 1, 8]
def baseStart_4092110 : Nat := 118140960795 + 4092110 * 2 ^ 59
def prefixEnd_4092110 : Nat := 4983230072969 + 3 ^ 40 * 4092110 * 2
def baseEnd_4092110 : Nat := 155645875634821469222647

theorem tailTrace_4092110 : CollatzResearch.WordTrace tailWord_4092110 prefixEnd_4092110 155645875634821469222647 := by
  unfold tailWord_4092110
  simp only [CollatzResearch.WordTrace]
  refine ⟨18656439150623977699086223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99501008803327881061793189 18656439150623977699086223)
  ·
    refine ⟨27984658725935966548629335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18656439150623977699086223 27984658725935966548629335)
    ·
      refine ⟨41976988088903949822944003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27984658725935966548629335 41976988088903949822944003)
      ·
        refine ⟨62965482133355924734416005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41976988088903949822944003 62965482133355924734416005)
        ·
          refine ⟨11806027900004235887703001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62965482133355924734416005 11806027900004235887703001)
          ·
            refine ⟨8854520925003176915777251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11806027900004235887703001 8854520925003176915777251)
            ·
              refine ⟨13281781387504765373665877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8854520925003176915777251 13281781387504765373665877)
              ·
                refine ⟨155645875634821469222647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13281781387504765373665877 155645875634821469222647)
                ·
                  rfl

theorem cell22_4092110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_4092110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092110 prefixEnd_4092110 := by exact prefixLift 4092110
  have htrace : WordTrace (prefixWord ++ tailWord_4092110) baseStart_4092110 baseEnd_4092110 := by
    simpa [prefixWord, tailWord_4092110, baseEnd_4092110] using wordTrace_append hprefix tailTrace_4092110
  have hstable : (prefixWord ++ tailWord_4092110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092110).length < 2 ^ (prefixWord ++ tailWord_4092110).sum := by decide
  have hdescent : baseEnd_4092110 < baseStart_4092110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092189 : List Nat := [1, 4, 2, 3, 2, 1, 2, 2, 5]
def baseStart_4092189 : Nat := 118140960795 + 4092189 * 2 ^ 59
def prefixEnd_4092189 : Nat := 4983230072969 + 3 ^ 40 * 4092189 * 2
def baseEnd_4092189 : Nat := 466946641342621116759527

theorem tailTrace_4092189 : CollatzResearch.WordTrace tailWord_4092189 prefixEnd_4092189 466946641342621116759527 := by
  unfold tailWord_4092189
  simp only [CollatzResearch.WordTrace]
  refine ⟨149254394571705618084815621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99502929714470412056543747 149254394571705618084815621)
  ·
    refine ⟨27985198982194803390902929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149254394571705618084815621 27985198982194803390902929)
    ·
      refine ⟨20988899236646102543177197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27985198982194803390902929 20988899236646102543177197)
      ·
        refine ⟨7870837213742288453691449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20988899236646102543177197 7870837213742288453691449)
        ·
          refine ⟨5903127910306716340268587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7870837213742288453691449 5903127910306716340268587)
          ·
            refine ⟨8854691865460074510402881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5903127910306716340268587 8854691865460074510402881)
            ·
              refine ⟨6641018899095055882802161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8854691865460074510402881 6641018899095055882802161)
              ·
                refine ⟨4980764174321291912101621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6641018899095055882802161 4980764174321291912101621)
                ·
                  refine ⟨466946641342621116759527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4980764174321291912101621 466946641342621116759527)
                  ·
                    rfl

theorem cell22_4092189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_4092189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092189 prefixEnd_4092189 := by exact prefixLift 4092189
  have htrace : WordTrace (prefixWord ++ tailWord_4092189) baseStart_4092189 baseEnd_4092189 := by
    simpa [prefixWord, tailWord_4092189, baseEnd_4092189] using wordTrace_append hprefix tailTrace_4092189
  have hstable : (prefixWord ++ tailWord_4092189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092189).length < 2 ^ (prefixWord ++ tailWord_4092189).sum := by decide
  have hdescent : baseEnd_4092189 < baseStart_4092189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092217 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 6]
def baseStart_4092217 : Nat := 118140960795 + 4092217 * 2 ^ 59
def prefixEnd_4092217 : Nat := 4983230072969 + 3 ^ 40 * 4092217 * 2
def baseEnd_4092217 : Nat := 466949836333360203526165

theorem tailTrace_4092217 : CollatzResearch.WordTrace tailWord_4092217 prefixEnd_4092217 466949836333360203526165 := by
  unfold tailWord_4092217
  simp only [CollatzResearch.WordTrace]
  refine ⟨149255415815604178866834905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99503610543736119244556603 149255415815604178866834905)
  ·
    refine ⟨111941561861703134150126179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149255415815604178866834905 111941561861703134150126179)
    ·
      refine ⟨167912342792554701225189269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111941561861703134150126179 167912342792554701225189269)
      ·
        refine ⟨7870891068401001619930747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 167912342792554701225189269 7870891068401001619930747)
        ·
          refine ⟨11806336602601502429896121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7870891068401001619930747 11806336602601502429896121)
          ·
            refine ⟨8854752451951126822422091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11806336602601502429896121 8854752451951126822422091)
            ·
              refine ⟨13282128677926690233633137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8854752451951126822422091 13282128677926690233633137)
              ·
                refine ⟨9961596508445017675224853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13282128677926690233633137 9961596508445017675224853)
                ·
                  refine ⟨466949836333360203526165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9961596508445017675224853 466949836333360203526165)
                  ·
                    rfl

theorem cell22_4092217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 6].length) (baseStart_4092217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092217 prefixEnd_4092217 := by exact prefixLift 4092217
  have htrace : WordTrace (prefixWord ++ tailWord_4092217) baseStart_4092217 baseEnd_4092217 := by
    simpa [prefixWord, tailWord_4092217, baseEnd_4092217] using wordTrace_append hprefix tailTrace_4092217
  have hstable : (prefixWord ++ tailWord_4092217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092217).length < 2 ^ (prefixWord ++ tailWord_4092217).sum := by decide
  have hdescent : baseEnd_4092217 < baseStart_4092217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092322 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_4092322 : Nat := 118140960795 + 4092322 * 2 ^ 59
def prefixEnd_4092322 : Nat := 4983230072969 + 3 ^ 40 * 4092322 * 2
def baseEnd_4092322 : Nat := 1400885452645895336703173

theorem tailTrace_4092322 : CollatzResearch.WordTrace tailWord_4092322 prefixEnd_4092322 1400885452645895336703173 := by
  unfold tailWord_4092322
  simp only [CollatzResearch.WordTrace]
  refine ⟨37314811370055945449851805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99506163653482521199604813 37314811370055945449851805)
  ·
    refine ⟨13993054263770979543694427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37314811370055945449851805 13993054263770979543694427)
    ·
      refine ⟨20989581395656469315541641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13993054263770979543694427 20989581395656469315541641)
      ·
        refine ⟨15742186046742351986656231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20989581395656469315541641 15742186046742351986656231)
        ·
          refine ⟨23613279070113527979984347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15742186046742351986656231 23613279070113527979984347)
          ·
            refine ⟨35419918605170291969976521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23613279070113527979984347 35419918605170291969976521)
            ·
              refine ⟨26564938953877718977482391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35419918605170291969976521 26564938953877718977482391)
              ·
                refine ⟨39847408430816578466223587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26564938953877718977482391 39847408430816578466223587)
                ·
                  refine ⟨59771112646224867699335381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39847408430816578466223587 59771112646224867699335381)
                  ·
                    refine ⟨1400885452645895336703173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59771112646224867699335381 1400885452645895336703173)
                    ·
                      rfl

theorem cell22_4092322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_4092322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092322 prefixEnd_4092322 := by exact prefixLift 4092322
  have htrace : WordTrace (prefixWord ++ tailWord_4092322) baseStart_4092322 baseEnd_4092322 := by
    simpa [prefixWord, tailWord_4092322, baseEnd_4092322] using wordTrace_append hprefix tailTrace_4092322
  have hstable : (prefixWord ++ tailWord_4092322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092322).length < 2 ^ (prefixWord ++ tailWord_4092322).sum := by decide
  have hdescent : baseEnd_4092322 < baseStart_4092322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092324 : List Nat := [2, 3, 1, 2, 1, 1, 6, 1, 5]
def baseStart_4092324 : Nat := 118140960795 + 4092324 * 2 ^ 59
def prefixEnd_4092324 : Nat := 4983230072969 + 3 ^ 40 * 4092324 * 2
def baseEnd_4092324 : Nat := 466962045762255999384389

theorem tailTrace_4092324 : CollatzResearch.WordTrace tailWord_4092324 prefixEnd_4092324 466962045762255999384389 := by
  unfold tailWord_4092324
  simp only [CollatzResearch.WordTrace]
  refine ⟨74629659213108268070490013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99506212284144357427320017 74629659213108268070490013)
  ·
    refine ⟨27986122204915600526433755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74629659213108268070490013 27986122204915600526433755)
    ·
      refine ⟨41979183307373400789650633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27986122204915600526433755 41979183307373400789650633)
      ·
        refine ⟨31484387480530050592237975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41979183307373400789650633 31484387480530050592237975)
        ·
          refine ⟨47226581220795075888356963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31484387480530050592237975 47226581220795075888356963)
          ·
            refine ⟨70839871831192613832535445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47226581220795075888356963 70839871831192613832535445)
            ·
              refine ⟨3320618992087153773400099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70839871831192613832535445 3320618992087153773400099)
              ·
                refine ⟨4980928488130730660100149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3320618992087153773400099 4980928488130730660100149)
                ·
                  refine ⟨466962045762255999384389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4980928488130730660100149 466962045762255999384389)
                  ·
                    rfl

theorem cell22_4092324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_4092324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092324 prefixEnd_4092324 := by exact prefixLift 4092324
  have htrace : WordTrace (prefixWord ++ tailWord_4092324) baseStart_4092324 baseEnd_4092324 := by
    simpa [prefixWord, tailWord_4092324, baseEnd_4092324] using wordTrace_append hprefix tailTrace_4092324
  have hstable : (prefixWord ++ tailWord_4092324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092324).length < 2 ^ (prefixWord ++ tailWord_4092324).sum := by decide
  have hdescent : baseEnd_4092324 < baseStart_4092324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092384 : List Nat := [2, 1, 1, 3, 1, 1, 3, 5, 2, 3]
def baseStart_4092384 : Nat := 118140960795 + 4092384 * 2 ^ 59
def prefixEnd_4092384 : Nat := 4983230072969 + 3 ^ 40 * 4092384 * 2
def baseEnd_4092384 : Nat := 1400906676512947841652983

theorem tailTrace_4092384 : CollatzResearch.WordTrace tailWord_4092384 prefixEnd_4092384 1400906676512947841652983 := by
  unfold tailWord_4092384
  simp only [CollatzResearch.WordTrace]
  refine ⟨74630753402999583194082103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99507671203999444258776137 74630753402999583194082103)
  ·
    refine ⟨111946130104499374791123155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74630753402999583194082103 111946130104499374791123155)
    ·
      refine ⟨167919195156749062186684733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111946130104499374791123155 167919195156749062186684733)
      ·
        refine ⟨62969698183780898320006775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167919195156749062186684733 62969698183780898320006775)
        ·
          refine ⟨94454547275671347480010163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62969698183780898320006775 94454547275671347480010163)
          ·
            refine ⟨141681820913507021220015245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94454547275671347480010163 141681820913507021220015245)
            ·
              refine ⟨53130682842565132957505717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141681820913507021220015245 53130682842565132957505717)
              ·
                refine ⟨4981001516490481214766161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53130682842565132957505717 4981001516490481214766161)
                ·
                  refine ⟨3735751137367860911074621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4981001516490481214766161 3735751137367860911074621)
                  ·
                    refine ⟨1400906676512947841652983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3735751137367860911074621 1400906676512947841652983)
                    ·
                      rfl

theorem cell22_4092384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 2, 3].length) (baseStart_4092384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092384 prefixEnd_4092384 := by exact prefixLift 4092384
  have htrace : WordTrace (prefixWord ++ tailWord_4092384) baseStart_4092384 baseEnd_4092384 := by
    simpa [prefixWord, tailWord_4092384, baseEnd_4092384] using wordTrace_append hprefix tailTrace_4092384
  have hstable : (prefixWord ++ tailWord_4092384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092384).length < 2 ^ (prefixWord ++ tailWord_4092384).sum := by decide
  have hdescent : baseEnd_4092384 < baseStart_4092384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092405 : List Nat := [1, 3, 5, 1, 2, 2, 2, 1, 1, 4]
def baseStart_4092405 : Nat := 118140960795 + 4092405 * 2 ^ 59
def prefixEnd_4092405 : Nat := 4983230072969 + 3 ^ 40 * 4092405 * 2
def baseEnd_4092405 : Nat := 1400913865242110786877919

theorem tailTrace_4092405 : CollatzResearch.WordTrace tailWord_4092405 prefixEnd_4092405 1400913865242110786877919 := by
  unfold tailWord_4092405
  simp only [CollatzResearch.WordTrace]
  refine ⟨149262272738923086974678669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99508181825948724649785779 149262272738923086974678669)
  ·
    refine ⟨55973352277096157615504501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149262272738923086974678669 55973352277096157615504501)
    ·
      refine ⟨5247501775977764776453547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55973352277096157615504501 5247501775977764776453547)
      ·
        refine ⟨7871252663966647164680321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5247501775977764776453547 7871252663966647164680321)
        ·
          refine ⟨5903439497974985373510241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7871252663966647164680321 5903439497974985373510241)
          ·
            refine ⟨4427579623481239030132681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5903439497974985373510241 4427579623481239030132681)
            ·
              refine ⟨3320684717610929272599511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4427579623481239030132681 3320684717610929272599511)
              ·
                refine ⟨4981027076416393908899267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3320684717610929272599511 4981027076416393908899267)
                ·
                  refine ⟨7471540614624590863348901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4981027076416393908899267 7471540614624590863348901)
                  ·
                    refine ⟨1400913865242110786877919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7471540614624590863348901 1400913865242110786877919)
                    ·
                      rfl

theorem cell22_4092405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_4092405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092405 prefixEnd_4092405 := by exact prefixLift 4092405
  have htrace : WordTrace (prefixWord ++ tailWord_4092405) baseStart_4092405 baseEnd_4092405 := by
    simpa [prefixWord, tailWord_4092405, baseEnd_4092405] using wordTrace_append hprefix tailTrace_4092405
  have hstable : (prefixWord ++ tailWord_4092405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092405).length < 2 ^ (prefixWord ++ tailWord_4092405).sum := by decide
  have hdescent : baseEnd_4092405 < baseStart_4092405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092418 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_4092418 : Nat := 118140960795 + 4092418 * 2 ^ 59
def prefixEnd_4092418 : Nat := 4983230072969 + 3 ^ 40 * 4092418 * 2
def baseEnd_4092418 : Nat := 1400918315407783086302879

theorem tailTrace_4092418 : CollatzResearch.WordTrace tailWord_4092418 prefixEnd_4092418 1400918315407783086302879 := by
  unfold tailWord_4092418
  simp only [CollatzResearch.WordTrace]
  refine ⟨37315686721968997548725477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99508497925250660129934605 37315686721968997548725477)
  ·
    refine ⟨6996691260369187040386027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37315686721968997548725477 6996691260369187040386027)
    ·
      refine ⟨10495036890553780560579041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6996691260369187040386027 10495036890553780560579041)
      ·
        refine ⟨7871277667915335420434281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10495036890553780560579041 7871277667915335420434281)
        ·
          refine ⟨5903458250936501565325711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7871277667915335420434281 5903458250936501565325711)
          ·
            refine ⟨8855187376404752347988567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5903458250936501565325711 8855187376404752347988567)
            ·
              refine ⟨13282781064607128521982851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8855187376404752347988567 13282781064607128521982851)
              ·
                refine ⟨19924171596910692782974277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13282781064607128521982851 19924171596910692782974277)
                ·
                  refine ⟨3735782174420754896807677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19924171596910692782974277 3735782174420754896807677)
                  ·
                    refine ⟨1400918315407783086302879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3735782174420754896807677 1400918315407783086302879)
                    ·
                      rfl

theorem cell22_4092418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_4092418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092418 prefixEnd_4092418 := by exact prefixLift 4092418
  have htrace : WordTrace (prefixWord ++ tailWord_4092418) baseStart_4092418 baseEnd_4092418 := by
    simpa [prefixWord, tailWord_4092418, baseEnd_4092418] using wordTrace_append hprefix tailTrace_4092418
  have hstable : (prefixWord ++ tailWord_4092418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092418).length < 2 ^ (prefixWord ++ tailWord_4092418).sum := by decide
  have hdescent : baseEnd_4092418 < baseStart_4092418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092448 : List Nat := [2, 1, 1, 6, 3, 1, 2, 6]
def baseStart_4092448 : Nat := 118140960795 + 4092448 * 2 ^ 59
def prefixEnd_4092448 : Nat := 4983230072969 + 3 ^ 40 * 4092448 * 2
def baseEnd_4092448 : Nat := 155658731668985889783643

theorem tailTrace_4092448 : CollatzResearch.WordTrace tailWord_4092448 prefixEnd_4092448 155658731668985889783643 := by
  unfold tailWord_4092448
  simp only [CollatzResearch.WordTrace]
  refine ⟨74631920538883652659246999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99509227385178203545662665 74631920538883652659246999)
  ·
    refine ⟨111947880808325478988870499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74631920538883652659246999 111947880808325478988870499)
    ·
      refine ⟨167921821212488218483305749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111947880808325478988870499 167921821212488218483305749)
      ·
        refine ⟨7871335369335385241404957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 167921821212488218483305749 7871335369335385241404957)
        ·
          refine ⟨2951750763500769465526859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7871335369335385241404957 2951750763500769465526859)
          ·
            refine ⟨4427626145251154198290289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2951750763500769465526859 4427626145251154198290289)
            ·
              refine ⟨3320719608938365648717717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4427626145251154198290289 3320719608938365648717717)
              ·
                refine ⟨155658731668985889783643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3320719608938365648717717 155658731668985889783643)
                ·
                  rfl

theorem cell22_4092448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 6].length) (baseStart_4092448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092448 prefixEnd_4092448 := by exact prefixLift 4092448
  have htrace : WordTrace (prefixWord ++ tailWord_4092448) baseStart_4092448 baseEnd_4092448 := by
    simpa [prefixWord, tailWord_4092448, baseEnd_4092448] using wordTrace_append hprefix tailTrace_4092448
  have hstable : (prefixWord ++ tailWord_4092448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092448).length < 2 ^ (prefixWord ++ tailWord_4092448).sum := by decide
  have hdescent : baseEnd_4092448 < baseStart_4092448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092493 : List Nat := [1, 6, 1, 1, 2, 1, 4, 1, 5]
def baseStart_4092493 : Nat := 118140960795 + 4092493 * 2 ^ 59
def prefixEnd_4092493 : Nat := 4983230072969 + 3 ^ 40 * 4092493 * 2
def baseEnd_4092493 : Nat := 466981329813502630225883

theorem tailTrace_4092493 : CollatzResearch.WordTrace tailWord_4092493 prefixEnd_4092493 466981329813502630225883 := by
  unfold tailWord_4092493
  simp only [CollatzResearch.WordTrace]
  refine ⟨149265482362604278003882133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99510321575069518669254755 149265482362604278003882133)
  ·
    refine ⟨6996819485747075531431975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 149265482362604278003882133 6996819485747075531431975)
    ·
      refine ⟨10495229228620613297147963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6996819485747075531431975 10495229228620613297147963)
      ·
        refine ⟨15742843842930919945721945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10495229228620613297147963 15742843842930919945721945)
        ·
          refine ⟨11807132882198189959291459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15742843842930919945721945 11807132882198189959291459)
          ·
            refine ⟨17710699323297284938937189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11807132882198189959291459 17710699323297284938937189)
            ·
              refine ⟨3320756123118240926050723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17710699323297284938937189 3320756123118240926050723)
              ·
                refine ⟨4981134184677361389076085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3320756123118240926050723 4981134184677361389076085)
                ·
                  refine ⟨466981329813502630225883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4981134184677361389076085 466981329813502630225883)
                  ·
                    rfl

theorem cell22_4092493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_4092493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092493 prefixEnd_4092493 := by exact prefixLift 4092493
  have htrace : WordTrace (prefixWord ++ tailWord_4092493) baseStart_4092493 baseEnd_4092493 := by
    simpa [prefixWord, tailWord_4092493, baseEnd_4092493] using wordTrace_append hprefix tailTrace_4092493
  have hstable : (prefixWord ++ tailWord_4092493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092493).length < 2 ^ (prefixWord ++ tailWord_4092493).sum := by decide
  have hdescent : baseEnd_4092493 < baseStart_4092493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092549 : List Nat := [1, 3, 1, 1, 4, 2, 3, 7]
def baseStart_4092549 : Nat := 118140960795 + 4092549 * 2 ^ 59
def prefixEnd_4092549 : Nat := 4983230072969 + 3 ^ 40 * 4092549 * 2
def baseEnd_4092549 : Nat := 155662573264993601253053

theorem tailTrace_4092549 : CollatzResearch.WordTrace tailWord_4092549 prefixEnd_4092549 155662573264993601253053 := by
  unfold tailWord_4092549
  simp only [CollatzResearch.WordTrace]
  refine ⟨149267524850401399567920701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99511683233600933045280467 149267524850401399567920701)
  ·
    refine ⟨55975321818900524837970263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149267524850401399567920701 55975321818900524837970263)
    ·
      refine ⟨83962982728350787256955395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55975321818900524837970263 83962982728350787256955395)
      ·
        refine ⟨125944474092526180885433093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83962982728350787256955395 125944474092526180885433093)
        ·
          refine ⟨23614588892348658916018705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125944474092526180885433093 23614588892348658916018705)
          ·
            refine ⟨17710941669261494187014029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23614588892348658916018705 17710941669261494187014029)
            ·
              refine ⟨6641603125973060320130261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17710941669261494187014029 6641603125973060320130261)
              ·
                refine ⟨155662573264993601253053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6641603125973060320130261 155662573264993601253053)
                ·
                  rfl

theorem cell22_4092549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 7].length) (baseStart_4092549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092549 prefixEnd_4092549 := by exact prefixLift 4092549
  have htrace : WordTrace (prefixWord ++ tailWord_4092549) baseStart_4092549 baseEnd_4092549 := by
    simpa [prefixWord, tailWord_4092549, baseEnd_4092549] using wordTrace_append hprefix tailTrace_4092549
  have hstable : (prefixWord ++ tailWord_4092549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092549).length < 2 ^ (prefixWord ++ tailWord_4092549).sum := by decide
  have hdescent : baseEnd_4092549 < baseStart_4092549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092624 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 7, 4]
def baseStart_4092624 : Nat := 118140960795 + 4092624 * 2 ^ 59
def prefixEnd_4092624 : Nat := 4983230072969 + 3 ^ 40 * 4092624 * 2
def baseEnd_4092624 : Nat := 1400988833417667215652247

theorem tailTrace_4092624 : CollatzResearch.WordTrace tailWord_4092624 prefixEnd_4092624 1400988833417667215652247 := by
  unfold tailWord_4092624
  simp only [CollatzResearch.WordTrace]
  refine ⟨74635130162564843688450463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99513506883419791584600617 74635130162564843688450463)
  ·
    refine ⟨111952695243847265532675695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74635130162564843688450463 111952695243847265532675695)
    ·
      refine ⟨167929042865770898299013543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111952695243847265532675695 167929042865770898299013543)
      ·
        refine ⟨251893564298656347448520315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167929042865770898299013543 251893564298656347448520315)
        ·
          refine ⟨377840346447984521172780473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251893564298656347448520315 377840346447984521172780473)
          ·
            refine ⟨283380259835988390879585355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377840346447984521172780473 283380259835988390879585355)
            ·
              refine ⟨425070389753982586319378033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283380259835988390879585355 425070389753982586319378033)
              ·
                refine ⟨318802792315486939739533525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425070389753982586319378033 318802792315486939739533525)
                ·
                  refine ⟨7471940444894225150145317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 318802792315486939739533525 7471940444894225150145317)
                  ·
                    refine ⟨1400988833417667215652247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7471940444894225150145317 1400988833417667215652247)
                    ·
                      rfl

theorem cell22_4092624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_4092624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092624 prefixEnd_4092624 := by exact prefixLift 4092624
  have htrace : WordTrace (prefixWord ++ tailWord_4092624) baseStart_4092624 baseEnd_4092624 := by
    simpa [prefixWord, tailWord_4092624, baseEnd_4092624] using wordTrace_append hprefix tailTrace_4092624
  have hstable : (prefixWord ++ tailWord_4092624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092624).length < 2 ^ (prefixWord ++ tailWord_4092624).sum := by decide
  have hdescent : baseEnd_4092624 < baseStart_4092624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092701 : List Nat := [1, 4, 2, 4, 11]
def baseStart_4092701 : Nat := 118140960795 + 4092701 * 2 ^ 59
def prefixEnd_4092701 : Nat := 4983230072969 + 3 ^ 40 * 4092701 * 2
def baseEnd_4092701 : Nat := 5765494617659525438177

theorem tailTrace_4092701 : CollatzResearch.WordTrace tailWord_4092701 prefixEnd_4092701 5765494617659525438177 := by
  unfold tailWord_4092701
  simp only [CollatzResearch.WordTrace]
  refine ⟨149273068745850729527453957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99515379163900486351635971 149273068745850729527453957)
  ·
    refine ⟨27988700389847011786397617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149273068745850729527453957 27988700389847011786397617)
    ·
      refine ⟨20991525292385258839798213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27988700389847011786397617 20991525292385258839798213)
      ·
        refine ⟨3935910992322236032462165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20991525292385258839798213 3935910992322236032462165)
        ·
          refine ⟨5765494617659525438177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3935910992322236032462165 5765494617659525438177)
          ·
            rfl

theorem cell22_4092701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 11].length) (baseStart_4092701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092701 prefixEnd_4092701 := by exact prefixLift 4092701
  have htrace : WordTrace (prefixWord ++ tailWord_4092701) baseStart_4092701 baseEnd_4092701 := by
    simpa [prefixWord, tailWord_4092701, baseEnd_4092701] using wordTrace_append hprefix tailTrace_4092701
  have hstable : (prefixWord ++ tailWord_4092701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092701).length < 2 ^ (prefixWord ++ tailWord_4092701).sum := by decide
  have hdescent : baseEnd_4092701 < baseStart_4092701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092718 : List Nat := [4, 1, 3, 2, 1, 1, 3, 7]
def baseStart_4092718 : Nat := 118140960795 + 4092718 * 2 ^ 59
def prefixEnd_4092718 : Nat := 4983230072969 + 3 ^ 40 * 4092718 * 2
def baseEnd_4092718 : Nat := 155669001282075811533551

theorem tailTrace_4092718 : CollatzResearch.WordTrace tailWord_4092718 prefixEnd_4092718 155669001282075811533551 := by
  unfold tailWord_4092718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18659211098348642678852851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99515792524526094287215205 18659211098348642678852851)
  ·
    refine ⟨27988816647522964018279277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18659211098348642678852851 27988816647522964018279277)
    ·
      refine ⟨10495806242821111506854729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27988816647522964018279277 10495806242821111506854729)
      ·
        refine ⟨7871854682115833630141047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10495806242821111506854729 7871854682115833630141047)
        ·
          refine ⟨11807782023173750445211571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7871854682115833630141047 11807782023173750445211571)
          ·
            refine ⟨17711673034760625667817357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11807782023173750445211571 17711673034760625667817357)
            ·
              refine ⟨6641877388035234625431509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17711673034760625667817357 6641877388035234625431509)
              ·
                refine ⟨155669001282075811533551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6641877388035234625431509 155669001282075811533551)
                ·
                  rfl

theorem cell22_4092718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_4092718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092718 prefixEnd_4092718 := by exact prefixLift 4092718
  have htrace : WordTrace (prefixWord ++ tailWord_4092718) baseStart_4092718 baseEnd_4092718 := by
    simpa [prefixWord, tailWord_4092718, baseEnd_4092718] using wordTrace_append hprefix tailTrace_4092718
  have hstable : (prefixWord ++ tailWord_4092718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092718).length < 2 ^ (prefixWord ++ tailWord_4092718).sum := by decide
  have hdescent : baseEnd_4092718 < baseStart_4092718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092737 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 2, 4]
def baseStart_4092737 : Nat := 118140960795 + 4092737 * 2 ^ 59
def prefixEnd_4092737 : Nat := 4983230072969 + 3 ^ 40 * 4092737 * 2
def baseEnd_4092737 : Nat := 1401027515626972587576901

theorem tailTrace_4092737 : CollatzResearch.WordTrace tailWord_4092737 prefixEnd_4092737 1401027515626972587576901 := by
  unfold tailWord_4092737
  simp only [CollatzResearch.WordTrace]
  refine ⟨149274381773720307675764465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99516254515813538450509643 149274381773720307675764465)
  ·
    refine ⟨111955786330290230756823349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149274381773720307675764465 111955786330290230756823349)
    ·
      refine ⟨10495854968464709133452189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111955786330290230756823349 10495854968464709133452189)
      ·
        refine ⟨3935945613174265925044571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10495854968464709133452189 3935945613174265925044571)
        ·
          refine ⟨5903918419761398887566857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3935945613174265925044571 5903918419761398887566857)
          ·
            refine ⟨4427938814821049165675143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5903918419761398887566857 4427938814821049165675143)
            ·
              refine ⟨6641908222231573748512715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4427938814821049165675143 6641908222231573748512715)
              ·
                refine ⟨9962862333347360622769073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6641908222231573748512715 9962862333347360622769073)
                ·
                  refine ⟨7472146750010520467076805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9962862333347360622769073 7472146750010520467076805)
                  ·
                    refine ⟨1401027515626972587576901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7472146750010520467076805 1401027515626972587576901)
                    ·
                      rfl

theorem cell22_4092737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_4092737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092737 prefixEnd_4092737 := by exact prefixLift 4092737
  have htrace : WordTrace (prefixWord ++ tailWord_4092737) baseStart_4092737 baseEnd_4092737 := by
    simpa [prefixWord, tailWord_4092737, baseEnd_4092737] using wordTrace_append hprefix tailTrace_4092737
  have hstable : (prefixWord ++ tailWord_4092737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092737).length < 2 ^ (prefixWord ++ tailWord_4092737).sum := by decide
  have hdescent : baseEnd_4092737 < baseStart_4092737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092761 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 2, 5]
def baseStart_4092761 : Nat := 118140960795 + 4092761 * 2 ^ 59
def prefixEnd_4092761 : Nat := 4983230072969 + 3 ^ 40 * 4092761 * 2
def baseEnd_4092761 : Nat := 1401035731317444524976827

theorem tailTrace_4092761 : CollatzResearch.WordTrace tailWord_4092761 prefixEnd_4092761 1401035731317444524976827 := by
  unfold tailWord_4092761
  simp only [CollatzResearch.WordTrace]
  refine ⟨149275257125633359774638137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99516838083755573183092091 149275257125633359774638137)
  ·
    refine ⟨111956442844225019830978603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149275257125633359774638137 111956442844225019830978603)
    ·
      refine ⟨167934664266337529746467905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111956442844225019830978603 167934664266337529746467905)
      ·
        refine ⟨125950998199753147309850929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167934664266337529746467905 125950998199753147309850929)
        ·
          refine ⟨94463248649814860482388197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125950998199753147309850929 94463248649814860482388197)
          ·
            refine ⟨17711859121840286340447787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94463248649814860482388197 17711859121840286340447787)
            ·
              refine ⟨26567788682760429510671681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17711859121840286340447787 26567788682760429510671681)
              ·
                refine ⟨19925841512070322133003761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26567788682760429510671681 19925841512070322133003761)
                ·
                  refine ⟨14944381134052741599752821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19925841512070322133003761 14944381134052741599752821)
                  ·
                    refine ⟨1401035731317444524976827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14944381134052741599752821 1401035731317444524976827)
                    ·
                      rfl

theorem cell22_4092761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_4092761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092761 prefixEnd_4092761 := by exact prefixLift 4092761
  have htrace : WordTrace (prefixWord ++ tailWord_4092761) baseStart_4092761 baseEnd_4092761 := by
    simpa [prefixWord, tailWord_4092761, baseEnd_4092761] using wordTrace_append hprefix tailTrace_4092761
  have hstable : (prefixWord ++ tailWord_4092761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092761).length < 2 ^ (prefixWord ++ tailWord_4092761).sum := by decide
  have hdescent : baseEnd_4092761 < baseStart_4092761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092793 : List Nat := [1, 2, 1, 3, 2, 3, 1, 4, 1, 4]
def baseStart_4092793 : Nat := 118140960795 + 4092793 * 2 ^ 59
def prefixEnd_4092793 : Nat := 4983230072969 + 3 ^ 40 * 4092793 * 2
def baseEnd_4092793 : Nat := 1401046685571407108176729

theorem tailTrace_4092793 : CollatzResearch.WordTrace tailWord_4092793 prefixEnd_4092793 1401046685571407108176729 := by
  unfold tailWord_4092793
  simp only [CollatzResearch.WordTrace]
  refine ⟨149276424261517429239803033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99517616174344952826535355 149276424261517429239803033)
  ·
    refine ⟨111957318196138071929852275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149276424261517429239803033 111957318196138071929852275)
    ·
      refine ⟨167935977294207107894778413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111957318196138071929852275 167935977294207107894778413)
      ·
        refine ⟨62975991485327665460541905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167935977294207107894778413 62975991485327665460541905)
        ·
          refine ⟨47231993613995749095406429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62975991485327665460541905 47231993613995749095406429)
          ·
            refine ⟨17711997605248405910777411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47231993613995749095406429 17711997605248405910777411)
            ·
              refine ⟨26567996407872608866166117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17711997605248405910777411 26567996407872608866166117)
              ·
                refine ⟨4981499326476114162406147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26567996407872608866166117 4981499326476114162406147)
                ·
                  refine ⟨7472248989714171243609221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4981499326476114162406147 7472248989714171243609221)
                  ·
                    refine ⟨1401046685571407108176729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7472248989714171243609221 1401046685571407108176729)
                    ·
                      rfl

theorem cell22_4092793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_4092793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092793 prefixEnd_4092793 := by exact prefixLift 4092793
  have htrace : WordTrace (prefixWord ++ tailWord_4092793) baseStart_4092793 baseEnd_4092793 := by
    simpa [prefixWord, tailWord_4092793, baseEnd_4092793] using wordTrace_append hprefix tailTrace_4092793
  have hstable : (prefixWord ++ tailWord_4092793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092793).length < 2 ^ (prefixWord ++ tailWord_4092793).sum := by decide
  have hdescent : baseEnd_4092793 < baseStart_4092793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092810 : List Nat := [3, 1, 2, 4, 1, 1, 2, 3, 1, 4]
def baseStart_4092810 : Nat := 118140960795 + 4092810 * 2 ^ 59
def prefixEnd_4092810 : Nat := 4983230072969 + 3 ^ 40 * 4092810 * 2
def baseEnd_4092810 : Nat := 1401052505018824730501677

theorem tailTrace_4092810 : CollatzResearch.WordTrace tailWord_4092810 prefixEnd_4092810 1401052505018824730501677 := by
  unfold tailWord_4092810
  simp only [CollatzResearch.WordTrace]
  refine ⟨37319261075613960285792971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99518029534970560762114589 37319261075613960285792971)
  ·
    refine ⟨55978891613420940428689457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37319261075613960285792971 55978891613420940428689457)
    ·
      refine ⟨41984168710065705321517093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55978891613420940428689457 41984168710065705321517093)
      ·
        refine ⟨7872031633137319747784455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41984168710065705321517093 7872031633137319747784455)
        ·
          refine ⟨11808047449705979621676683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7872031633137319747784455 11808047449705979621676683)
          ·
            refine ⟨17712071174558969432515025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11808047449705979621676683 17712071174558969432515025)
            ·
              refine ⟨13284053380919227074386269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17712071174558969432515025 13284053380919227074386269)
              ·
                refine ⟨4981520017844710152894851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13284053380919227074386269 4981520017844710152894851)
                ·
                  refine ⟨7472280026767065229342277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4981520017844710152894851 7472280026767065229342277)
                  ·
                    refine ⟨1401052505018824730501677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7472280026767065229342277 1401052505018824730501677)
                    ·
                      rfl

theorem cell22_4092810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_4092810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092810 prefixEnd_4092810 := by exact prefixLift 4092810
  have htrace : WordTrace (prefixWord ++ tailWord_4092810) baseStart_4092810 baseEnd_4092810 := by
    simpa [prefixWord, tailWord_4092810, baseEnd_4092810] using wordTrace_append hprefix tailTrace_4092810
  have hstable : (prefixWord ++ tailWord_4092810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092810).length < 2 ^ (prefixWord ++ tailWord_4092810).sum := by decide
  have hdescent : baseEnd_4092810 < baseStart_4092810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092823 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 4, 3]
def baseStart_4092823 : Nat := 118140960795 + 4092823 * 2 ^ 59
def prefixEnd_4092823 : Nat := 4983230072969 + 3 ^ 40 * 4092823 * 2
def baseEnd_4092823 : Nat := 1401056955184497029926637

theorem tailTrace_4092823 : CollatzResearch.WordTrace tailWord_4092823 prefixEnd_4092823 1401056955184497029926637 := by
  unfold tailWord_4092823
  simp only [CollatzResearch.WordTrace]
  refine ⟨149277518451408744363395123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99518345634272496242263415 149277518451408744363395123)
  ·
    refine ⟨223916277677113116545092685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149277518451408744363395123 223916277677113116545092685)
    ·
      refine ⟨83968604128917418704409757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223916277677113116545092685 83968604128917418704409757)
      ·
        refine ⟨31488226548344032014153659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83968604128917418704409757 31488226548344032014153659)
        ·
          refine ⟨47232339822516048021230489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31488226548344032014153659 47232339822516048021230489)
          ·
            refine ⟨35424254866887036015922867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47232339822516048021230489 35424254866887036015922867)
            ·
              refine ⟨53136382300330554023884301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35424254866887036015922867 53136382300330554023884301)
              ·
                refine ⟨19926143362623957758956613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53136382300330554023884301 19926143362623957758956613)
                ·
                  refine ⟨3736151880491992079804365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19926143362623957758956613 3736151880491992079804365)
                  ·
                    refine ⟨1401056955184497029926637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3736151880491992079804365 1401056955184497029926637)
                    ·
                      rfl

theorem cell22_4092823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_4092823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092823 prefixEnd_4092823 := by exact prefixLift 4092823
  have htrace : WordTrace (prefixWord ++ tailWord_4092823) baseStart_4092823 baseEnd_4092823 := by
    simpa [prefixWord, tailWord_4092823, baseEnd_4092823] using wordTrace_append hprefix tailTrace_4092823
  have hstable : (prefixWord ++ tailWord_4092823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092823).length < 2 ^ (prefixWord ++ tailWord_4092823).sum := by decide
  have hdescent : baseEnd_4092823 < baseStart_4092823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092962 : List Nat := [3, 3, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_4092962 : Nat := 118140960795 + 4092962 * 2 ^ 59
def prefixEnd_4092962 : Nat := 4983230072969 + 3 ^ 40 * 4092962 * 2
def baseEnd_4092962 : Nat := 1401104537725147000701211

theorem tailTrace_4092962 : CollatzResearch.WordTrace tailWord_4092962 prefixEnd_4092962 1401104537725147000701211 := by
  unfold tailWord_4092962
  simp only [CollatzResearch.WordTrace]
  refine ⟨37320647049476292775676285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99521725465270114068470093 37320647049476292775676285)
  ·
    refine ⟨13995242643553609790878607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37320647049476292775676285 13995242643553609790878607)
    ·
      refine ⟨20992863965330414686317911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13995242643553609790878607 20992863965330414686317911)
      ·
        refine ⟨31489295947995622029476867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20992863965330414686317911 31489295947995622029476867)
        ·
          refine ⟨47233943921993433044215301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31489295947995622029476867 47233943921993433044215301)
          ·
            refine ⟨8856364485373768695790369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47233943921993433044215301 8856364485373768695790369)
            ·
              refine ⟨6642273364030326521842777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8856364485373768695790369 6642273364030326521842777)
              ·
                refine ⟨4981705023022744891382083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6642273364030326521842777 4981705023022744891382083)
                ·
                  refine ⟨7472557534534117337073125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4981705023022744891382083 7472557534534117337073125)
                  ·
                    refine ⟨1401104537725147000701211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7472557534534117337073125 1401104537725147000701211)
                    ·
                      rfl

theorem cell22_4092962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_4092962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092962 prefixEnd_4092962 := by exact prefixLift 4092962
  have htrace : WordTrace (prefixWord ++ tailWord_4092962) baseStart_4092962 baseEnd_4092962 := by
    simpa [prefixWord, tailWord_4092962, baseEnd_4092962] using wordTrace_append hprefix tailTrace_4092962
  have hstable : (prefixWord ++ tailWord_4092962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092962).length < 2 ^ (prefixWord ++ tailWord_4092962).sum := by decide
  have hdescent : baseEnd_4092962 < baseStart_4092962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092988 : List Nat := [2, 2, 2, 2, 2, 2, 10]
def baseStart_4092988 : Nat := 118140960795 + 4092988 * 2 ^ 59
def prefixEnd_4092988 : Nat := 4983230072969 + 3 ^ 40 * 4092988 * 2
def baseEnd_4092988 : Nat := 51893090298388577761153

theorem tailTrace_4092988 : CollatzResearch.WordTrace tailWord_4092988 prefixEnd_4092988 51893090298388577761153 := by
  unfold tailWord_4092988
  simp only [CollatzResearch.WordTrace]
  refine ⟨74641768247905488771575809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99522357663873985028767745 74641768247905488771575809)
  ·
    refine ⟨55981326185929116578681857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74641768247905488771575809 55981326185929116578681857)
    ·
      refine ⟨41985994639446837434011393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55981326185929116578681857 41985994639446837434011393)
      ·
        refine ⟨31489495979585128075508545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41985994639446837434011393 31489495979585128075508545)
        ·
          refine ⟨23617121984688846056631409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31489495979585128075508545 23617121984688846056631409)
          ·
            refine ⟨17712841488516634542473557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23617121984688846056631409 17712841488516634542473557)
            ·
              refine ⟨51893090298388577761153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17712841488516634542473557 51893090298388577761153)
              ·
                rfl

theorem cell22_4092988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 10].length) (baseStart_4092988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4092988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4092988 prefixEnd_4092988 := by exact prefixLift 4092988
  have htrace : WordTrace (prefixWord ++ tailWord_4092988) baseStart_4092988 baseEnd_4092988 := by
    simpa [prefixWord, tailWord_4092988, baseEnd_4092988] using wordTrace_append hprefix tailTrace_4092988
  have hstable : (prefixWord ++ tailWord_4092988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092988).length < 2 ^ (prefixWord ++ tailWord_4092988).sum := by decide
  have hdescent : baseEnd_4092988 < baseStart_4092988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093005 : List Nat := [1, 6, 1, 1, 1, 2, 1, 9]
def baseStart_4093005 : Nat := 118140960795 + 4093005 * 2 ^ 59
def prefixEnd_4093005 : Nat := 4983230072969 + 3 ^ 40 * 4093005 * 2
def baseEnd_4093005 : Nat := 155679917500434357986231

theorem tailTrace_4093005 : CollatzResearch.WordTrace tailWord_4093005 prefixEnd_4093005 155679917500434357986231 := by
  unfold tailWord_4093005
  simp only [CollatzResearch.WordTrace]
  refine ⟨149284156536749389446520469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99522771024499592964346979 149284156536749389446520469)
  ·
    refine ⟨6997694837660127630305647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 149284156536749389446520469 6997694837660127630305647)
    ·
      refine ⟨10496542256490191445458471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6997694837660127630305647 10496542256490191445458471)
      ·
        refine ⟨15744813384735287168187707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10496542256490191445458471 15744813384735287168187707)
        ·
          refine ⟨23617220077102930752281561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15744813384735287168187707 23617220077102930752281561)
          ·
            refine ⟨17712915057827198064211171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23617220077102930752281561 17712915057827198064211171)
            ·
              refine ⟨26569372586740797096316757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17712915057827198064211171 26569372586740797096316757)
              ·
                refine ⟨155679917500434357986231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26569372586740797096316757 155679917500434357986231)
                ·
                  rfl

theorem cell22_4093005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 9].length) (baseStart_4093005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093005 prefixEnd_4093005 := by exact prefixLift 4093005
  have htrace : WordTrace (prefixWord ++ tailWord_4093005) baseStart_4093005 baseEnd_4093005 := by
    simpa [prefixWord, tailWord_4093005, baseEnd_4093005] using wordTrace_append hprefix tailTrace_4093005
  have hstable : (prefixWord ++ tailWord_4093005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093005).length < 2 ^ (prefixWord ++ tailWord_4093005).sum := by decide
  have hdescent : baseEnd_4093005 < baseStart_4093005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093018 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_4093018 : Nat := 118140960795 + 4093018 * 2 ^ 59
def prefixEnd_4093018 : Nat := 4983230072969 + 3 ^ 40 * 4093018 * 2
def baseEnd_4093018 : Nat := 1401123707669581521301039

theorem tailTrace_4093018 : CollatzResearch.WordTrace tailWord_4093018 prefixEnd_4093018 1401123707669581521301039 := by
  unfold tailWord_4093018
  simp only [CollatzResearch.WordTrace]
  refine ⟨37321157671425573166685927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99523087123801528444495805 37321157671425573166685927)
  ·
    refine ⟨55981736507138359750028891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37321157671425573166685927 55981736507138359750028891)
    ·
      refine ⟨83972604760707539625043337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55981736507138359750028891 83972604760707539625043337)
      ·
        refine ⟨62979453570530654718782503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83972604760707539625043337 62979453570530654718782503)
        ·
          refine ⟨94469180355795982078173755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62979453570530654718782503 94469180355795982078173755)
          ·
            refine ⟨141703770533693973117260633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94469180355795982078173755 141703770533693973117260633)
            ·
              refine ⟨106277827900270479837945475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141703770533693973117260633 106277827900270479837945475)
              ·
                refine ⟨159416741850405719756918213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106277827900270479837945475 159416741850405719756918213)
                ·
                  refine ⟨29890639096951072454422165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159416741850405719756918213 29890639096951072454422165)
                  ·
                    refine ⟨1401123707669581521301039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29890639096951072454422165 1401123707669581521301039)
                    ·
                      rfl

theorem cell22_4093018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_4093018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093018 prefixEnd_4093018 := by exact prefixLift 4093018
  have htrace : WordTrace (prefixWord ++ tailWord_4093018) baseStart_4093018 baseEnd_4093018 := by
    simpa [prefixWord, tailWord_4093018, baseEnd_4093018] using wordTrace_append hprefix tailTrace_4093018
  have hstable : (prefixWord ++ tailWord_4093018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093018).length < 2 ^ (prefixWord ++ tailWord_4093018).sum := by decide
  have hdescent : baseEnd_4093018 < baseStart_4093018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093065 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 2, 5]
def baseStart_4093065 : Nat := 118140960795 + 4093065 * 2 ^ 59
def prefixEnd_4093065 : Nat := 4983230072969 + 3 ^ 40 * 4093065 * 2
def baseEnd_4093065 : Nat := 1401139796730089065375895

theorem tailTrace_4093065 : CollatzResearch.WordTrace tailWord_4093065 prefixEnd_4093065 1401139796730089065375895 := by
  unfold tailWord_4093065
  simp only [CollatzResearch.WordTrace]
  refine ⟨149286344916532019693704649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99524229944354679795803099 149286344916532019693704649)
  ·
    refine ⟨111964758687399014770278487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149286344916532019693704649 111964758687399014770278487)
    ·
      refine ⟨167947138031098522155417731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111964758687399014770278487 167947138031098522155417731)
      ·
        refine ⟨251920707046647783233126597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167947138031098522155417731 251920707046647783233126597)
        ·
          refine ⟨47235132571246459356211237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251920707046647783233126597 47235132571246459356211237)
          ·
            refine ⟨8856587357108711129289607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47235132571246459356211237 8856587357108711129289607)
            ·
              refine ⟨13284881035663066693934411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8856587357108711129289607 13284881035663066693934411)
              ·
                refine ⟨19927321553494600040901617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13284881035663066693934411 19927321553494600040901617)
                ·
                  refine ⟨14945491165120950030676213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19927321553494600040901617 14945491165120950030676213)
                  ·
                    refine ⟨1401139796730089065375895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14945491165120950030676213 1401139796730089065375895)
                    ·
                      rfl

theorem cell22_4093065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_4093065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093065 prefixEnd_4093065 := by exact prefixLift 4093065
  have htrace : WordTrace (prefixWord ++ tailWord_4093065) baseStart_4093065 baseEnd_4093065 := by
    simpa [prefixWord, tailWord_4093065, baseEnd_4093065] using wordTrace_append hprefix tailTrace_4093065
  have hstable : (prefixWord ++ tailWord_4093065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093065).length < 2 ^ (prefixWord ++ tailWord_4093065).sum := by decide
  have hdescent : baseEnd_4093065 < baseStart_4093065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093101 : List Nat := [1, 5, 2, 1, 4, 1, 1, 2, 5]
def baseStart_4093101 : Nat := 118140960795 + 4093101 * 2 ^ 59
def prefixEnd_4093101 : Nat := 4983230072969 + 3 ^ 40 * 4093101 * 2
def baseEnd_4093101 : Nat := 467050706755265657158595

theorem tailTrace_4093101 : CollatzResearch.WordTrace tailWord_4093101 prefixEnd_4093101 467050706755265657158595 := by
  unfold tailWord_4093101
  simp only [CollatzResearch.WordTrace]
  refine ⟨149287657944401597842015157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99525105296267731894676771 149287657944401597842015157)
  ·
    refine ⟨13995717932287649797688921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149287657944401597842015157 13995717932287649797688921)
    ·
      refine ⟨10496788449215737348266691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13995717932287649797688921 10496788449215737348266691)
      ·
        refine ⟨15745182673823606022400037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10496788449215737348266691 15745182673823606022400037)
        ·
          refine ⟨2952221751341926129200007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15745182673823606022400037 2952221751341926129200007)
          ·
            refine ⟨4428332627012889193800011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952221751341926129200007 4428332627012889193800011)
            ·
              refine ⟨6642498940519333790700017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4428332627012889193800011 6642498940519333790700017)
              ·
                refine ⟨4981874205389500343025013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6642498940519333790700017 4981874205389500343025013)
                ·
                  refine ⟨467050706755265657158595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4981874205389500343025013 467050706755265657158595)
                  ·
                    rfl

theorem cell22_4093101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_4093101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093101 prefixEnd_4093101 := by exact prefixLift 4093101
  have htrace : WordTrace (prefixWord ++ tailWord_4093101) baseStart_4093101 baseEnd_4093101 := by
    simpa [prefixWord, tailWord_4093101, baseEnd_4093101] using wordTrace_append hprefix tailTrace_4093101
  have hstable : (prefixWord ++ tailWord_4093101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093101).length < 2 ^ (prefixWord ++ tailWord_4093101).sum := by decide
  have hdescent : baseEnd_4093101 < baseStart_4093101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093127 : List Nat := [1, 1, 4, 1, 1, 1, 1, 7, 2, 3]
def baseStart_4093127 : Nat := 118140960795 + 4093127 * 2 ^ 59
def prefixEnd_4093127 : Nat := 4983230072969 + 3 ^ 40 * 4093127 * 2
def baseEnd_4093127 : Nat := 1401161020597141570325705

theorem tailTrace_4093127 : CollatzResearch.WordTrace tailWord_4093127 prefixEnd_4093127 1401161020597141570325705 := by
  unfold tailWord_4093127
  simp only [CollatzResearch.WordTrace]
  refine ⟨149288606242307404282461635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99525737494871602854974423 149288606242307404282461635)
  ·
    refine ⟨223932909363461106423692453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149288606242307404282461635 223932909363461106423692453)
    ·
      refine ⟨41987420505648957454442335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223932909363461106423692453 41987420505648957454442335)
      ·
        refine ⟨62981130758473436181663503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41987420505648957454442335 62981130758473436181663503)
        ·
          refine ⟨94471696137710154272495255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62981130758473436181663503 94471696137710154272495255)
          ·
            refine ⟨141707544206565231408742883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94471696137710154272495255 141707544206565231408742883)
            ·
              refine ⟨212561316309847847113114325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141707544206565231408742883 212561316309847847113114325)
              ·
                refine ⟨4981905851012058916713617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 212561316309847847113114325 4981905851012058916713617)
                ·
                  refine ⟨3736429388259044187535213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4981905851012058916713617 3736429388259044187535213)
                  ·
                    refine ⟨1401161020597141570325705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3736429388259044187535213 1401161020597141570325705)
                    ·
                      rfl

theorem cell22_4093127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_4093127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093127 prefixEnd_4093127 := by exact prefixLift 4093127
  have htrace : WordTrace (prefixWord ++ tailWord_4093127) baseStart_4093127 baseEnd_4093127 := by
    simpa [prefixWord, tailWord_4093127, baseEnd_4093127] using wordTrace_append hprefix tailTrace_4093127
  have hstable : (prefixWord ++ tailWord_4093127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093127).length < 2 ^ (prefixWord ++ tailWord_4093127).sum := by decide
  have hdescent : baseEnd_4093127 < baseStart_4093127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093157 : List Nat := [1, 3, 1, 4, 3, 2, 8]
def baseStart_4093157 : Nat := 118140960795 + 4093157 * 2 ^ 59
def prefixEnd_4093157 : Nat := 4983230072969 + 3 ^ 40 * 4093157 * 2
def baseEnd_4093157 : Nat := 51895232970749314521319

theorem tailTrace_4093157 : CollatzResearch.WordTrace tailWord_4093157 prefixEnd_4093157 51895232970749314521319 := by
  unfold tailWord_4093157
  simp only [CollatzResearch.WordTrace]
  refine ⟨149289700432198719406053725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99526466954799146270702483 149289700432198719406053725)
  ·
    refine ⟨55983637662074519777270147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149289700432198719406053725 55983637662074519777270147)
    ·
      refine ⟨83975456493111779665905221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55983637662074519777270147 83975456493111779665905221)
      ·
        refine ⟨15745398092458458687357229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83975456493111779665905221 15745398092458458687357229)
        ·
          refine ⟨5904524284671922007758961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15745398092458458687357229 5904524284671922007758961)
          ·
            refine ⟨4428393213503941505819221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5904524284671922007758961 4428393213503941505819221)
            ·
              refine ⟨51895232970749314521319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4428393213503941505819221 51895232970749314521319)
              ·
                rfl

theorem cell22_4093157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 8].length) (baseStart_4093157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093157 prefixEnd_4093157 := by exact prefixLift 4093157
  have htrace : WordTrace (prefixWord ++ tailWord_4093157) baseStart_4093157 baseEnd_4093157 := by
    simpa [prefixWord, tailWord_4093157, baseEnd_4093157] using wordTrace_append hprefix tailTrace_4093157
  have hstable : (prefixWord ++ tailWord_4093157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093157).length < 2 ^ (prefixWord ++ tailWord_4093157).sum := by decide
  have hdescent : baseEnd_4093157 < baseStart_4093157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093159 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 2, 4]
def baseStart_4093159 : Nat := 118140960795 + 4093159 * 2 ^ 59
def prefixEnd_4093159 : Nat := 4983230072969 + 3 ^ 40 * 4093159 * 2
def baseEnd_4093159 : Nat := 1401171974851104153525607

theorem tailTrace_4093159 : CollatzResearch.WordTrace tailWord_4093159 prefixEnd_4093159 1401171974851104153525607 := by
  unfold tailWord_4093159
  simp only [CollatzResearch.WordTrace]
  refine ⟨149289773378191473747626531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99526515585460982498417687 149289773378191473747626531)
  ·
    refine ⟨223934660067287210621439797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149289773378191473747626531 223934660067287210621439797)
    ·
      refine ⟨20993874381308175995759981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223934660067287210621439797 20993874381308175995759981)
      ·
        refine ⟨7872702892990565998409993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20993874381308175995759981 7872702892990565998409993)
        ·
          refine ⟨5904527169742924498807495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7872702892990565998409993 5904527169742924498807495)
          ·
            refine ⟨8856790754614386748211243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5904527169742924498807495 8856790754614386748211243)
            ·
              refine ⟨13285186131921580122316865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8856790754614386748211243 13285186131921580122316865)
              ·
                refine ⟨9963889598941185091737649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13285186131921580122316865 9963889598941185091737649)
                ·
                  refine ⟨7472917199205888818803237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9963889598941185091737649 7472917199205888818803237)
                  ·
                    refine ⟨1401171974851104153525607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7472917199205888818803237 1401171974851104153525607)
                    ·
                      rfl

theorem cell22_4093159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_4093159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093159 prefixEnd_4093159 := by exact prefixLift 4093159
  have htrace : WordTrace (prefixWord ++ tailWord_4093159) baseStart_4093159 baseEnd_4093159 := by
    simpa [prefixWord, tailWord_4093159, baseEnd_4093159] using wordTrace_append hprefix tailTrace_4093159
  have hstable : (prefixWord ++ tailWord_4093159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093159).length < 2 ^ (prefixWord ++ tailWord_4093159).sum := by decide
  have hdescent : baseEnd_4093159 < baseStart_4093159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093247 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 6]
def baseStart_4093247 : Nat := 118140960795 + 4093247 * 2 ^ 59
def prefixEnd_4093247 : Nat := 4983230072969 + 3 ^ 40 * 4093247 * 2
def baseEnd_4093247 : Nat := 467067366349833752441779

theorem tailTrace_4093247 : CollatzResearch.WordTrace tailWord_4093247 prefixEnd_4093247 467067366349833752441779 := by
  unfold tailWord_4093247
  simp only [CollatzResearch.WordTrace]
  refine ⟨149292983001872664776829995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99528655334581776517886663 149292983001872664776829995)
  ·
    refine ⟨223939474502808997165244993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149292983001872664776829995 223939474502808997165244993)
    ·
      refine ⟨167954605877106747873933745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223939474502808997165244993 167954605877106747873933745)
      ·
        refine ⟨125965954407830060905450309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167954605877106747873933745 125965954407830060905450309)
        ·
          refine ⟨23618616451468136419771933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125965954407830060905450309 23618616451468136419771933)
          ·
            refine ⟨8856981169300551157414475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23618616451468136419771933 8856981169300551157414475)
            ·
              refine ⟨13285471753950826736121713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8856981169300551157414475 13285471753950826736121713)
              ·
                refine ⟨9964103815463120052091285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13285471753950826736121713 9964103815463120052091285)
                ·
                  refine ⟨467067366349833752441779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9964103815463120052091285 467067366349833752441779)
                  ·
                    rfl

theorem cell22_4093247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 6].length) (baseStart_4093247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093247 prefixEnd_4093247 := by exact prefixLift 4093247
  have htrace : WordTrace (prefixWord ++ tailWord_4093247) baseStart_4093247 baseEnd_4093247 := by
    simpa [prefixWord, tailWord_4093247, baseEnd_4093247] using wordTrace_append hprefix tailTrace_4093247
  have hstable : (prefixWord ++ tailWord_4093247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093247).length < 2 ^ (prefixWord ++ tailWord_4093247).sum := by decide
  have hdescent : baseEnd_4093247 < baseStart_4093247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093249 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 3, 4]
def baseStart_4093249 : Nat := 118140960795 + 4093249 * 2 ^ 59
def prefixEnd_4093249 : Nat := 4983230072969 + 3 ^ 40 * 4093249 * 2
def baseEnd_4093249 : Nat := 1401202783690373918775331

theorem tailTrace_4093249 : CollatzResearch.WordTrace tailWord_4093249 prefixEnd_4093249 1401202783690373918775331 := by
  unfold tailWord_4093249
  simp only [CollatzResearch.WordTrace]
  refine ⟨149293055947865419118402801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99528703965243612745601867 149293055947865419118402801)
  ·
    refine ⟨111969791960899064338802101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149293055947865419118402801 111969791960899064338802101)
    ·
      refine ⟨10497167996334287281762697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111969791960899064338802101 10497167996334287281762697)
      ·
        refine ⟨7872875997250715461322023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10497167996334287281762697 7872875997250715461322023)
        ·
          refine ⟨11809313995876073191983035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7872875997250715461322023 11809313995876073191983035)
          ·
            refine ⟨17713970993814109787974553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11809313995876073191983035 17713970993814109787974553)
            ·
              refine ⟨13285478245360582340980915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17713970993814109787974553 13285478245360582340980915)
              ·
                refine ⟨19928217368040873511471373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13285478245360582340980915 19928217368040873511471373)
                ·
                  refine ⟨7473081513015327566801765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19928217368040873511471373 7473081513015327566801765)
                  ·
                    refine ⟨1401202783690373918775331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7473081513015327566801765 1401202783690373918775331)
                    ·
                      rfl

theorem cell22_4093249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_4093249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093249 prefixEnd_4093249 := by exact prefixLift 4093249
  have htrace : WordTrace (prefixWord ++ tailWord_4093249) baseStart_4093249 baseEnd_4093249 := by
    simpa [prefixWord, tailWord_4093249, baseEnd_4093249] using wordTrace_append hprefix tailTrace_4093249
  have hstable : (prefixWord ++ tailWord_4093249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093249).length < 2 ^ (prefixWord ++ tailWord_4093249).sum := by decide
  have hdescent : baseEnd_4093249 < baseStart_4093249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093262 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_4093262 : Nat := 118140960795 + 4093262 * 2 ^ 59
def prefixEnd_4093262 : Nat := 4983230072969 + 3 ^ 40 * 4093262 * 2
def baseEnd_4093262 : Nat := 1401207233856046218200291

theorem tailTrace_4093262 : CollatzResearch.WordTrace tailWord_4093262 prefixEnd_4093262 1401207233856046218200291 := by
  unfold tailWord_4093262
  simp only [CollatzResearch.WordTrace]
  refine ⟨18661691262102290292328255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99529020064545548225750693 18661691262102290292328255)
  ·
    refine ⟨27992536893153435438492383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18661691262102290292328255 27992536893153435438492383)
    ·
      refine ⟨41988805339730153157738575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27992536893153435438492383 41988805339730153157738575)
      ·
        refine ⟨62983208009595229736607863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41988805339730153157738575 62983208009595229736607863)
        ·
          refine ⟨94474812014392844604911795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62983208009595229736607863 94474812014392844604911795)
          ·
            refine ⟨141712218021589266907367693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94474812014392844604911795 141712218021589266907367693)
            ·
              refine ⟨53142081758095975090262885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141712218021589266907367693 53142081758095975090262885)
              ·
                refine ⟨9964140329642995329424291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53142081758095975090262885 9964140329642995329424291)
                ·
                  refine ⟨14946210494464492994136437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9964140329642995329424291 14946210494464492994136437)
                  ·
                    refine ⟨1401207233856046218200291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14946210494464492994136437 1401207233856046218200291)
                    ·
                      rfl

theorem cell22_4093262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_4093262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093262 prefixEnd_4093262 := by exact prefixLift 4093262
  have htrace : WordTrace (prefixWord ++ tailWord_4093262) baseStart_4093262 baseEnd_4093262 := by
    simpa [prefixWord, tailWord_4093262, baseEnd_4093262] using wordTrace_append hprefix tailTrace_4093262
  have hstable : (prefixWord ++ tailWord_4093262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093262).length < 2 ^ (prefixWord ++ tailWord_4093262).sum := by decide
  have hdescent : baseEnd_4093262 < baseStart_4093262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093264 : List Nat := [2, 1, 1, 1, 1, 5, 4, 3, 4]
def baseStart_4093264 : Nat := 118140960795 + 4093264 * 2 ^ 59
def prefixEnd_4093264 : Nat := 4983230072969 + 3 ^ 40 * 4093264 * 2
def baseEnd_4093264 : Nat := 467069306165639626550095

theorem tailTrace_4093264 : CollatzResearch.WordTrace tailWord_4093264 prefixEnd_4093264 467069306165639626550095 := by
  unfold tailWord_4093264
  simp only [CollatzResearch.WordTrace]
  refine ⟨74646801521405538340099423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99529068695207384453465897 74646801521405538340099423)
  ·
    refine ⟨111970202282108307510149135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74646801521405538340099423 111970202282108307510149135)
    ·
      refine ⟨167955303423162461265223703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111970202282108307510149135 167955303423162461265223703)
      ·
        refine ⟨251932955134743691897835555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167955303423162461265223703 251932955134743691897835555)
        ·
          refine ⟨377899432702115537846753333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251932955134743691897835555 377899432702115537846753333)
          ·
            refine ⟨35428071815823331673133125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 377899432702115537846753333 35428071815823331673133125)
            ·
              refine ⟨6642763465466874688712461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35428071815823331673133125 6642763465466874688712461)
              ·
                refine ⟨2491036299550078008267173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6642763465466874688712461 2491036299550078008267173)
                ·
                  refine ⟨467069306165639626550095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2491036299550078008267173 467069306165639626550095)
                  ·
                    rfl

theorem cell22_4093264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 4].length) (baseStart_4093264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093264 prefixEnd_4093264 := by exact prefixLift 4093264
  have htrace : WordTrace (prefixWord ++ tailWord_4093264) baseStart_4093264 baseEnd_4093264 := by
    simpa [prefixWord, tailWord_4093264, baseEnd_4093264] using wordTrace_append hprefix tailTrace_4093264
  have hstable : (prefixWord ++ tailWord_4093264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093264).length < 2 ^ (prefixWord ++ tailWord_4093264).sum := by decide
  have hdescent : baseEnd_4093264 < baseStart_4093264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093296 : List Nat := [2, 1, 1, 1, 4, 2, 5, 1, 2, 3]
def baseStart_4093296 : Nat := 118140960795 + 4093296 * 2 ^ 59
def prefixEnd_4093296 : Nat := 4983230072969 + 3 ^ 40 * 4093296 * 2
def baseEnd_4093296 : Nat := 1401218872750881462850187

theorem tailTrace_4093296 : CollatzResearch.WordTrace tailWord_4093296 prefixEnd_4093296 1401218872750881462850187 := by
  unfold tailWord_4093296
  simp only [CollatzResearch.WordTrace]
  refine ⟨74647385089347573072681871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99529846785796764096909161 74647385089347573072681871)
  ·
    refine ⟨111971077634021359609022807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74647385089347573072681871 111971077634021359609022807)
    ·
      refine ⟨167956616451032039413534211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111971077634021359609022807 167956616451032039413534211)
      ·
        refine ⟨251934924676548059120301317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167956616451032039413534211 251934924676548059120301317)
        ·
          refine ⟨47237798376852761085056497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251934924676548059120301317 47237798376852761085056497)
          ·
            refine ⟨35428348782639570813792373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47237798376852761085056497 35428348782639570813792373)
            ·
              refine ⟨3321407698372459763793035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35428348782639570813792373 3321407698372459763793035)
              ·
                refine ⟨4982111547558689645689553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3321407698372459763793035 4982111547558689645689553)
                ·
                  refine ⟨3736583660669017234267165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4982111547558689645689553 3736583660669017234267165)
                  ·
                    refine ⟨1401218872750881462850187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3736583660669017234267165 1401218872750881462850187)
                    ·
                      rfl

theorem cell22_4093296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 2, 3].length) (baseStart_4093296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093296 prefixEnd_4093296 := by exact prefixLift 4093296
  have htrace : WordTrace (prefixWord ++ tailWord_4093296) baseStart_4093296 baseEnd_4093296 := by
    simpa [prefixWord, tailWord_4093296, baseEnd_4093296] using wordTrace_append hprefix tailTrace_4093296
  have hstable : (prefixWord ++ tailWord_4093296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093296).length < 2 ^ (prefixWord ++ tailWord_4093296).sum := by decide
  have hdescent : baseEnd_4093296 < baseStart_4093296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093326 : List Nat := [4, 1, 1, 4, 3, 1, 8]
def baseStart_4093326 : Nat := 118140960795 + 4093326 * 2 ^ 59
def prefixEnd_4093326 : Nat := 4983230072969 + 3 ^ 40 * 4093326 * 2
def baseEnd_4093326 : Nat := 51897375643110051281485

theorem tailTrace_4093326 : CollatzResearch.WordTrace tailWord_4093326 prefixEnd_4093326 51897375643110051281485 := by
  unfold tailWord_4093326
  simp only [CollatzResearch.WordTrace]
  refine ⟨18661983046073307658619479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99530576245724307512637221 18661983046073307658619479)
  ·
    refine ⟨27992974569109961487929219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18661983046073307658619479 27992974569109961487929219)
    ·
      refine ⟨41989461853664942231893829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27992974569109961487929219 41989461853664942231893829)
      ·
        refine ⟨7873024097562176668480093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41989461853664942231893829 7873024097562176668480093)
        ·
          refine ⟨2952384036585816250680035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7873024097562176668480093 2952384036585816250680035)
          ·
            refine ⟨4428576054878724376020053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952384036585816250680035 4428576054878724376020053)
            ·
              refine ⟨51897375643110051281485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4428576054878724376020053 51897375643110051281485)
              ·
                rfl

theorem cell22_4093326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 8].length) (baseStart_4093326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093326 prefixEnd_4093326 := by exact prefixLift 4093326
  have htrace : WordTrace (prefixWord ++ tailWord_4093326) baseStart_4093326 baseEnd_4093326 := by
    simpa [prefixWord, tailWord_4093326, baseEnd_4093326] using wordTrace_append hprefix tailTrace_4093326
  have hstable : (prefixWord ++ tailWord_4093326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093326).length < 2 ^ (prefixWord ++ tailWord_4093326).sum := by decide
  have hdescent : baseEnd_4093326 < baseStart_4093326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093337 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 7]
def baseStart_4093337 : Nat := 118140960795 + 4093337 * 2 ^ 59
def prefixEnd_4093337 : Nat := 4983230072969 + 3 ^ 40 * 4093337 * 2
def baseEnd_4093337 : Nat := 467077635962923674191687

theorem tailTrace_4093337 : CollatzResearch.WordTrace tailWord_4093337 prefixEnd_4093337 467077635962923674191687 := by
  unfold tailWord_4093337
  simp only [CollatzResearch.WordTrace]
  refine ⟨149296265571546610147606265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99530843714364406765070843 149296265571546610147606265)
  ·
    refine ⟨111972199178659957610704699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149296265571546610147606265 111972199178659957610704699)
    ·
      refine ⟨167958298767989936416057049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111972199178659957610704699 167958298767989936416057049)
      ·
        refine ⟨125968724075992452312042787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167958298767989936416057049 125968724075992452312042787)
        ·
          refine ⟨188953086113988678468064181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125968724075992452312042787 188953086113988678468064181)
          ·
            refine ⟨17714351823186438606381017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188953086113988678468064181 17714351823186438606381017)
            ·
              refine ⟨13285763867389828954785763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17714351823186438606381017 13285763867389828954785763)
              ·
                refine ⟨19928645801084743432178645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13285763867389828954785763 19928645801084743432178645)
                ·
                  refine ⟨467077635962923674191687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19928645801084743432178645 467077635962923674191687)
                  ·
                    rfl

theorem cell22_4093337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 7].length) (baseStart_4093337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093337 prefixEnd_4093337 := by exact prefixLift 4093337
  have htrace : WordTrace (prefixWord ++ tailWord_4093337) baseStart_4093337 baseEnd_4093337 := by
    simpa [prefixWord, tailWord_4093337, baseEnd_4093337] using wordTrace_append hprefix tailTrace_4093337
  have hstable : (prefixWord ++ tailWord_4093337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093337).length < 2 ^ (prefixWord ++ tailWord_4093337).sum := by decide
  have hdescent : baseEnd_4093337 < baseStart_4093337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093341 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 3, 3]
def baseStart_4093341 : Nat := 118140960795 + 4093341 * 2 ^ 59
def prefixEnd_4093341 : Nat := 4983230072969 + 3 ^ 40 * 4093341 * 2
def baseEnd_4093341 : Nat := 1401234277170516345475049

theorem tailTrace_4093341 : CollatzResearch.WordTrace tailWord_4093341 prefixEnd_4093341 1401234277170516345475049 := by
  unfold tailWord_4093341
  simp only [CollatzResearch.WordTrace]
  refine ⟨149296411463532118830751877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99530940975688079220501251 149296411463532118830751877)
  ·
    refine ⟨27993077149412272280765977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149296411463532118830751877 27993077149412272280765977)
    ·
      refine ⟨20994807862059204210574483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27993077149412272280765977 20994807862059204210574483)
      ·
        refine ⟨31492211793088806315861725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20994807862059204210574483 31492211793088806315861725)
        ·
          refine ⟨11809579422408302368448147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31492211793088806315861725 11809579422408302368448147)
          ·
            refine ⟨17714369133612453552672221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11809579422408302368448147 17714369133612453552672221)
            ·
              refine ⟨6642888425104670082252083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17714369133612453552672221 6642888425104670082252083)
              ·
                refine ⟨9964332637657005123378125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6642888425104670082252083 9964332637657005123378125)
                ·
                  refine ⟨3736624739121376921266797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9964332637657005123378125 3736624739121376921266797)
                  ·
                    refine ⟨1401234277170516345475049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3736624739121376921266797 1401234277170516345475049)
                    ·
                      rfl

theorem cell22_4093341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_4093341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093341 prefixEnd_4093341 := by exact prefixLift 4093341
  have htrace : WordTrace (prefixWord ++ tailWord_4093341) baseStart_4093341 baseEnd_4093341 := by
    simpa [prefixWord, tailWord_4093341, baseEnd_4093341] using wordTrace_append hprefix tailTrace_4093341
  have hstable : (prefixWord ++ tailWord_4093341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093341).length < 2 ^ (prefixWord ++ tailWord_4093341).sum := by decide
  have hdescent : baseEnd_4093341 < baseStart_4093341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093474 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_4093474 : Nat := 118140960795 + 4093474 * 2 ^ 59
def prefixEnd_4093474 : Nat := 4983230072969 + 3 ^ 40 * 4093474 * 2
def baseEnd_4093474 : Nat := 1401279805788548331899641

theorem tailTrace_4093474 : CollatzResearch.WordTrace tailWord_4093474 prefixEnd_4093474 1401279805788548331899641 := by
  unfold tailWord_4093474
  simp only [CollatzResearch.WordTrace]
  refine ⟨37325315593012570636335869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99534174914700188363562317 37325315593012570636335869)
  ·
    refine ⟨13996993347379713988625951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37325315593012570636335869 13996993347379713988625951)
    ·
      refine ⟨20995490021069570982938927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13996993347379713988625951 20995490021069570982938927)
      ·
        refine ⟨31493235031604356474408391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20995490021069570982938927 31493235031604356474408391)
        ·
          refine ⟨47239852547406534711612587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31493235031604356474408391 47239852547406534711612587)
          ·
            refine ⟨70859778821109802067418881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47239852547406534711612587 70859778821109802067418881)
            ·
              refine ⟨53144834115832351550564161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70859778821109802067418881 53144834115832351550564161)
              ·
                refine ⟨39858625586874263662923121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53144834115832351550564161 39858625586874263662923121)
                ·
                  refine ⟨29893969190155697747192341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39858625586874263662923121 29893969190155697747192341)
                  ·
                    refine ⟨1401279805788548331899641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29893969190155697747192341 1401279805788548331899641)
                    ·
                      rfl

theorem cell22_4093474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_4093474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093474 prefixEnd_4093474 := by exact prefixLift 4093474
  have htrace : WordTrace (prefixWord ++ tailWord_4093474) baseStart_4093474 baseEnd_4093474 := by
    simpa [prefixWord, tailWord_4093474, baseEnd_4093474] using wordTrace_append hprefix tailTrace_4093474
  have hstable : (prefixWord ++ tailWord_4093474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093474).length < 2 ^ (prefixWord ++ tailWord_4093474).sum := by decide
  have hdescent : baseEnd_4093474 < baseStart_4093474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093519 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 3, 4]
def baseStart_4093519 : Nat := 118140960795 + 4093519 * 2 ^ 59
def prefixEnd_4093519 : Nat := 4983230072969 + 3 ^ 40 * 4093519 * 2
def baseEnd_4093519 : Nat := 1401295210208183214524503

theorem tailTrace_4093519 : CollatzResearch.WordTrace tailWord_4093519 prefixEnd_4093519 1401295210208183214524503 := by
  unfold tailWord_4093519
  simp only [CollatzResearch.WordTrace]
  refine ⟨149302903656887255230731611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99535269104591503487154407 149302903656887255230731611)
  ·
    refine ⟨223954355485330882846097417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149302903656887255230731611 223954355485330882846097417)
    ·
      refine ⟨167965766613998162134573063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223954355485330882846097417 167965766613998162134573063)
      ·
        refine ⟨251948649920997243201859595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167965766613998162134573063 251948649920997243201859595)
        ·
          refine ⟨377922974881495864802789393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251948649920997243201859595 377922974881495864802789393)
          ·
            refine ⟨283442231161121898602092045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377922974881495864802789393 283442231161121898602092045)
            ·
              refine ⟨106290836685420711975784517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283442231161121898602092045 106290836685420711975784517)
              ·
                refine ⟨19929531878516383495459597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106290836685420711975784517 19929531878516383495459597)
                ·
                  refine ⟨7473574454443643810797349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19929531878516383495459597 7473574454443643810797349)
                  ·
                    refine ⟨1401295210208183214524503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7473574454443643810797349 1401295210208183214524503)
                    ·
                      rfl

theorem cell22_4093519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_4093519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093519 prefixEnd_4093519 := by exact prefixLift 4093519
  have htrace : WordTrace (prefixWord ++ tailWord_4093519) baseStart_4093519 baseEnd_4093519 := by
    simpa [prefixWord, tailWord_4093519, baseEnd_4093519] using wordTrace_append hprefix tailTrace_4093519
  have hstable : (prefixWord ++ tailWord_4093519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093519).length < 2 ^ (prefixWord ++ tailWord_4093519).sum := by decide
  have hdescent : baseEnd_4093519 < baseStart_4093519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093551 : List Nat := [1, 1, 2, 1, 3, 2, 1, 7, 4]
def baseStart_4093551 : Nat := 118140960795 + 4093551 * 2 ^ 59
def prefixEnd_4093551 : Nat := 4983230072969 + 3 ^ 40 * 4093551 * 2
def baseEnd_4093551 : Nat := 467102054820715265908135

theorem tailTrace_4093551 : CollatzResearch.WordTrace tailWord_4093551 prefixEnd_4093551 467102054820715265908135 := by
  unfold tailWord_4093551
  simp only [CollatzResearch.WordTrace]
  refine ⟨149304070792771324695896507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99536047195180883130597671 149304070792771324695896507)
  ·
    refine ⟨223956106189156987043844761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149304070792771324695896507 223956106189156987043844761)
    ·
      refine ⟨167967079641867740282883571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223956106189156987043844761 167967079641867740282883571)
      ·
        refine ⟨251950619462801610424325357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167967079641867740282883571 251950619462801610424325357)
        ·
          refine ⟨94481482298550603909122009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251950619462801610424325357 94481482298550603909122009)
          ·
            refine ⟨70861111723912952931841507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94481482298550603909122009 70861111723912952931841507)
            ·
              refine ⟨106291667585869429397762261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70861111723912952931841507 106291667585869429397762261)
              ·
                refine ⟨2491210959043814751510053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 106291667585869429397762261 2491210959043814751510053)
                ·
                  refine ⟨467102054820715265908135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2491210959043814751510053 467102054820715265908135)
                  ·
                    rfl

theorem cell22_4093551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 4].length) (baseStart_4093551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093551 prefixEnd_4093551 := by exact prefixLift 4093551
  have htrace : WordTrace (prefixWord ++ tailWord_4093551) baseStart_4093551 baseEnd_4093551 := by
    simpa [prefixWord, tailWord_4093551, baseEnd_4093551] using wordTrace_append hprefix tailTrace_4093551
  have hstable : (prefixWord ++ tailWord_4093551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093551).length < 2 ^ (prefixWord ++ tailWord_4093551).sum := by decide
  have hdescent : baseEnd_4093551 < baseStart_4093551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093564 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_4093564 : Nat := 118140960795 + 4093564 * 2 ^ 59
def prefixEnd_4093564 : Nat := 4983230072969 + 3 ^ 40 * 4093564 * 2
def baseEnd_4093564 : Nat := 1401310614627818097149365

theorem tailTrace_4093564 : CollatzResearch.WordTrace tailWord_4093564 prefixEnd_4093564 1401310614627818097149365 := by
  unfold tailWord_4093564
  simp only [CollatzResearch.WordTrace]
  refine ⟨74652272470862113958059873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99536363294482818610746497 74652272470862113958059873)
  ·
    refine ⟨55989204353146585468544905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74652272470862113958059873 55989204353146585468544905)
    ·
      refine ⟨41991903264859939101408679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55989204353146585468544905 41991903264859939101408679)
      ·
        refine ⟨62987854897289908652113019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41991903264859939101408679 62987854897289908652113019)
        ·
          refine ⟨94481782345934862978169529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62987854897289908652113019 94481782345934862978169529)
          ·
            refine ⟨70861336759451147233627147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94481782345934862978169529 70861336759451147233627147)
            ·
              refine ⟨106292005139176720850440721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70861336759451147233627147 106292005139176720850440721)
              ·
                refine ⟨79719003854382540637830541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106292005139176720850440721 79719003854382540637830541)
                ·
                  refine ⟨29894626445393452739186453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79719003854382540637830541 29894626445393452739186453)
                  ·
                    refine ⟨1401310614627818097149365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29894626445393452739186453 1401310614627818097149365)
                    ·
                      rfl

theorem cell22_4093564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_4093564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093564 prefixEnd_4093564 := by exact prefixLift 4093564
  have htrace : WordTrace (prefixWord ++ tailWord_4093564) baseStart_4093564 baseEnd_4093564 := by
    simpa [prefixWord, tailWord_4093564, baseEnd_4093564] using wordTrace_append hprefix tailTrace_4093564
  have hstable : (prefixWord ++ tailWord_4093564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093564).length < 2 ^ (prefixWord ++ tailWord_4093564).sum := by decide
  have hdescent : baseEnd_4093564 < baseStart_4093564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093598 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_4093598 : Nat := 118140960795 + 4093598 * 2 ^ 59
def prefixEnd_4093598 : Nat := 4983230072969 + 3 ^ 40 * 4093598 * 2
def baseEnd_4093598 : Nat := 1401322253522653341799261

theorem tailTrace_4093598 : CollatzResearch.WordTrace tailWord_4093598 prefixEnd_4093598 1401322253522653341799261 := by
  unfold tailWord_4093598
  simp only [CollatzResearch.WordTrace]
  refine ⟨18663223127950131465357181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99537190015734034481904965 18663223127950131465357181)
  ·
    refine ⟨6998708672981299299508943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18663223127950131465357181 6998708672981299299508943)
    ·
      refine ⟨10498063009471948949263415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6998708672981299299508943 10498063009471948949263415)
      ·
        refine ⟨15747094514207923423895123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10498063009471948949263415 15747094514207923423895123)
        ·
          refine ⟨23620641771311885135842685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15747094514207923423895123 23620641771311885135842685)
          ·
            refine ⟨8857740664241956925941007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23620641771311885135842685 8857740664241956925941007)
            ·
              refine ⟨13286610996362935388911511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8857740664241956925941007 13286610996362935388911511)
              ·
                refine ⟨19929916494544403083367267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13286610996362935388911511 19929916494544403083367267)
                ·
                  refine ⟨29894874741816604625050901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19929916494544403083367267 29894874741816604625050901)
                  ·
                    refine ⟨1401322253522653341799261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29894874741816604625050901 1401322253522653341799261)
                    ·
                      rfl

theorem cell22_4093598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_4093598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093598 prefixEnd_4093598 := by exact prefixLift 4093598
  have htrace : WordTrace (prefixWord ++ tailWord_4093598) baseStart_4093598 baseEnd_4093598 := by
    simpa [prefixWord, tailWord_4093598, baseEnd_4093598] using wordTrace_append hprefix tailTrace_4093598
  have hstable : (prefixWord ++ tailWord_4093598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093598).length < 2 ^ (prefixWord ++ tailWord_4093598).sum := by decide
  have hdescent : baseEnd_4093598 < baseStart_4093598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093602 : List Nat := [3, 3, 1, 4, 1, 1, 2, 3, 4]
def baseStart_4093602 : Nat := 118140960795 + 4093602 * 2 ^ 59
def prefixEnd_4093602 : Nat := 4983230072969 + 3 ^ 40 * 4093602 * 2
def baseEnd_4093602 : Nat := 467107874268132888233083

theorem tailTrace_4093602 : CollatzResearch.WordTrace tailWord_4093602 prefixEnd_4093602 467107874268132888233083 := by
  unfold tailWord_4093602
  simp only [CollatzResearch.WordTrace]
  refine ⟨37326482728896640101500765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99537287277057706937335373 37326482728896640101500765)
  ·
    refine ⟨13997431023336240038062787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37326482728896640101500765 13997431023336240038062787)
    ·
      refine ⟨20996146535004360057094181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13997431023336240038062787 20996146535004360057094181)
      ·
        refine ⟨3936777475313317510705159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20996146535004360057094181 3936777475313317510705159)
        ·
          refine ⟨5905166212969976266057739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936777475313317510705159 5905166212969976266057739)
          ·
            refine ⟨8857749319454964399086609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5905166212969976266057739 8857749319454964399086609)
            ·
              refine ⟨6643311989591223299314957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8857749319454964399086609 6643311989591223299314957)
              ·
                refine ⟨2491241996096708737243109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6643311989591223299314957 2491241996096708737243109)
                ·
                  refine ⟨467107874268132888233083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2491241996096708737243109 467107874268132888233083)
                  ·
                    rfl

theorem cell22_4093602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_4093602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093602 prefixEnd_4093602 := by exact prefixLift 4093602
  have htrace : WordTrace (prefixWord ++ tailWord_4093602) baseStart_4093602 baseEnd_4093602 := by
    simpa [prefixWord, tailWord_4093602, baseEnd_4093602] using wordTrace_append hprefix tailTrace_4093602
  have hstable : (prefixWord ++ tailWord_4093602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093602).length < 2 ^ (prefixWord ++ tailWord_4093602).sum := by decide
  have hdescent : baseEnd_4093602 < baseStart_4093602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093628 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 3, 3]
def baseStart_4093628 : Nat := 118140960795 + 4093628 * 2 ^ 59
def prefixEnd_4093628 : Nat := 4983230072969 + 3 ^ 40 * 4093628 * 2
def baseEnd_4093628 : Nat := 1401332523135743263549169

theorem tailTrace_4093628 : CollatzResearch.WordTrace tailWord_4093628 prefixEnd_4093628 1401332523135743263549169 := by
  unfold tailWord_4093628
  simp only [CollatzResearch.WordTrace]
  refine ⟨74653439606746183423224769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99537919475661577897633025 74653439606746183423224769)
  ·
    refine ⟨55990079705059637567418577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74653439606746183423224769 55990079705059637567418577)
    ·
      refine ⟨41992559778794728175563933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55990079705059637567418577 41992559778794728175563933)
      ·
        refine ⟨15747209917048023065836475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41992559778794728175563933 15747209917048023065836475)
        ·
          refine ⟨23620814875572034598754713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15747209917048023065836475 23620814875572034598754713)
          ·
            refine ⟨17715611156679025949066035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23620814875572034598754713 17715611156679025949066035)
            ·
              refine ⟨26573416735018538923599053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17715611156679025949066035 26573416735018538923599053)
              ·
                refine ⟨9965031275631952096349645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26573416735018538923599053 9965031275631952096349645)
                ·
                  refine ⟨3736886728361982036131117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9965031275631952096349645 3736886728361982036131117)
                  ·
                    refine ⟨1401332523135743263549169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3736886728361982036131117 1401332523135743263549169)
                    ·
                      rfl

theorem cell22_4093628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_4093628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093628 prefixEnd_4093628 := by exact prefixLift 4093628
  have htrace : WordTrace (prefixWord ++ tailWord_4093628) baseStart_4093628 baseEnd_4093628 := by
    simpa [prefixWord, tailWord_4093628, baseEnd_4093628] using wordTrace_append hprefix tailTrace_4093628
  have hstable : (prefixWord ++ tailWord_4093628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093628).length < 2 ^ (prefixWord ++ tailWord_4093628).sum := by decide
  have hdescent : baseEnd_4093628 < baseStart_4093628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093634 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_4093634 : Nat := 118140960795 + 4093634 * 2 ^ 59
def prefixEnd_4093634 : Nat := 4983230072969 + 3 ^ 40 * 4093634 * 2
def baseEnd_4093634 : Nat := 1401334577058361247899151

theorem tailTrace_4093634 : CollatzResearch.WordTrace tailWord_4093634 prefixEnd_4093634 1401334577058361247899151 := by
  unfold tailWord_4093634
  simp only [CollatzResearch.WordTrace]
  refine ⟨37326774512867657467791989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99538065367647086580778637 37326774512867657467791989)
  ·
    refine ⟨3499385110581342887605499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37326774512867657467791989 3499385110581342887605499)
    ·
      refine ⟨5249077665872014331408249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3499385110581342887605499 5249077665872014331408249)
      ·
        refine ⟨3936808249404010748556187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5249077665872014331408249 3936808249404010748556187)
        ·
          refine ⟨5905212374106016122834281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936808249404010748556187 5905212374106016122834281)
          ·
            refine ⟨4428909280579512092125711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5905212374106016122834281 4428909280579512092125711)
            ·
              refine ⟨6643363920869268138188567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4428909280579512092125711 6643363920869268138188567)
              ·
                refine ⟨9965045881303902207282851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6643363920869268138188567 9965045881303902207282851)
                ·
                  refine ⟨14947568821955853310924277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9965045881303902207282851 14947568821955853310924277)
                  ·
                    refine ⟨1401334577058361247899151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14947568821955853310924277 1401334577058361247899151)
                    ·
                      rfl

theorem cell22_4093634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_4093634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093634 prefixEnd_4093634 := by exact prefixLift 4093634
  have htrace : WordTrace (prefixWord ++ tailWord_4093634) baseStart_4093634 baseEnd_4093634 := by
    simpa [prefixWord, tailWord_4093634, baseEnd_4093634] using wordTrace_append hprefix tailTrace_4093634
  have hstable : (prefixWord ++ tailWord_4093634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093634).length < 2 ^ (prefixWord ++ tailWord_4093634).sum := by decide
  have hdescent : baseEnd_4093634 < baseStart_4093634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093733 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 2, 4]
def baseStart_4093733 : Nat := 118140960795 + 4093733 * 2 ^ 59
def prefixEnd_4093733 : Nat := 4983230072969 + 3 ^ 40 * 4093733 * 2
def baseEnd_4093733 : Nat := 1401368466781557989673847

theorem tailTrace_4093733 : CollatzResearch.WordTrace tailWord_4093733 prefixEnd_4093733 1401368466781557989673847 := by
  unfold tailWord_4093733
  simp only [CollatzResearch.WordTrace]
  refine ⟨149310708878111969779021853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99540472585407979852681235 149310708878111969779021853)
  ·
    refine ⟨55991515829291988667133195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149310708878111969779021853 55991515829291988667133195)
    ·
      refine ⟨83987273743937983000699793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55991515829291988667133195 83987273743937983000699793)
      ·
        refine ⟨62990455307953487250524845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83987273743937983000699793 62990455307953487250524845)
        ·
          refine ⟨23621420740482557718946817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62990455307953487250524845 23621420740482557718946817)
          ·
            refine ⟨17716065555361918289210113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23621420740482557718946817 17716065555361918289210113)
            ·
              refine ⟨13287049166521438716907585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17716065555361918289210113 13287049166521438716907585)
              ·
                refine ⟨9965286874891079037680689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13287049166521438716907585 9965286874891079037680689)
                ·
                  refine ⟨7473965156168309278260517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9965286874891079037680689 7473965156168309278260517)
                  ·
                    refine ⟨1401368466781557989673847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7473965156168309278260517 1401368466781557989673847)
                    ·
                      rfl

theorem cell22_4093733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_4093733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093733 prefixEnd_4093733 := by exact prefixLift 4093733
  have htrace : WordTrace (prefixWord ++ tailWord_4093733) baseStart_4093733 baseEnd_4093733 := by
    simpa [prefixWord, tailWord_4093733, baseEnd_4093733] using wordTrace_append hprefix tailTrace_4093733
  have hstable : (prefixWord ++ tailWord_4093733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093733).length < 2 ^ (prefixWord ++ tailWord_4093733).sum := by decide
  have hdescent : baseEnd_4093733 < baseStart_4093733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093763 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 5, 3]
def baseStart_4093763 : Nat := 118140960795 + 4093763 * 2 ^ 59
def prefixEnd_4093763 : Nat := 4983230072969 + 3 ^ 40 * 4093763 * 2
def baseEnd_4093763 : Nat := 1401378736394647911423755

theorem tailTrace_4093763 : CollatzResearch.WordTrace tailWord_4093763 prefixEnd_4093763 1401378736394647911423755 := by
  unfold tailWord_4093763
  simp only [CollatzResearch.WordTrace]
  refine ⟨149311803068003284902613943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99541202045335523268409295 149311803068003284902613943)
  ·
    refine ⟨223967704602004927353920915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149311803068003284902613943 223967704602004927353920915)
    ·
      refine ⟨335951556903007391030881373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223967704602004927353920915 335951556903007391030881373)
      ·
        refine ⟨125981833838627771636580515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335951556903007391030881373 125981833838627771636580515)
        ·
          refine ⟨188972750757941657454870773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125981833838627771636580515 188972750757941657454870773)
          ·
            refine ⟨17716195383557030386394135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188972750757941657454870773 17716195383557030386394135)
            ·
              refine ⟨26574293075335545579591203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17716195383557030386394135 26574293075335545579591203)
              ·
                refine ⟨39861439613003318369386805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26574293075335545579591203 39861439613003318369386805)
                ·
                  refine ⟨3737009963719061097130013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39861439613003318369386805 3737009963719061097130013)
                  ·
                    refine ⟨1401378736394647911423755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3737009963719061097130013 1401378736394647911423755)
                    ·
                      rfl

theorem cell22_4093763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 3].length) (baseStart_4093763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093763 prefixEnd_4093763 := by exact prefixLift 4093763
  have htrace : WordTrace (prefixWord ++ tailWord_4093763) baseStart_4093763 baseEnd_4093763 := by
    simpa [prefixWord, tailWord_4093763, baseEnd_4093763] using wordTrace_append hprefix tailTrace_4093763
  have hstable : (prefixWord ++ tailWord_4093763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093763).length < 2 ^ (prefixWord ++ tailWord_4093763).sum := by decide
  have hdescent : baseEnd_4093763 < baseStart_4093763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093776 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 7]
def baseStart_4093776 : Nat := 118140960795 + 4093776 * 2 ^ 59
def prefixEnd_4093776 : Nat := 4983230072969 + 3 ^ 40 * 4093776 * 2
def baseEnd_4093776 : Nat := 467127728853440070282905

theorem tailTrace_4093776 : CollatzResearch.WordTrace tailWord_4093776 prefixEnd_4093776 467127728853440070282905 := by
  unfold tailWord_4093776
  simp only [CollatzResearch.WordTrace]
  refine ⟨74656138608478094061418591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99541518144637458748558121 74656138608478094061418591)
  ·
    refine ⟨111984207912717141092127887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74656138608478094061418591 111984207912717141092127887)
    ·
      refine ⟨167976311869075711638191831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111984207912717141092127887 167976311869075711638191831)
      ·
        refine ⟨251964467803613567457287747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167976311869075711638191831 251964467803613567457287747)
        ·
          refine ⟨377946701705420351185931621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251964467803613567457287747 377946701705420351185931621)
          ·
            refine ⟨70865006569766315847362179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377946701705420351185931621 70865006569766315847362179)
            ·
              refine ⟨106297509854649473771043269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70865006569766315847362179 106297509854649473771043269)
              ·
                refine ⟨19930783097746776332070613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106297509854649473771043269 19930783097746776332070613)
                ·
                  refine ⟨467127728853440070282905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19930783097746776332070613 467127728853440070282905)
                  ·
                    rfl

theorem cell22_4093776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 7].length) (baseStart_4093776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093776 prefixEnd_4093776 := by exact prefixLift 4093776
  have htrace : WordTrace (prefixWord ++ tailWord_4093776) baseStart_4093776 baseEnd_4093776 := by
    simpa [prefixWord, tailWord_4093776, baseEnd_4093776] using wordTrace_append hprefix tailTrace_4093776
  have hstable : (prefixWord ++ tailWord_4093776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093776).length < 2 ^ (prefixWord ++ tailWord_4093776).sum := by decide
  have hdescent : baseEnd_4093776 < baseStart_4093776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093831 : List Nat := [1, 1, 4, 2, 5, 1, 1, 3, 1, 3]
def baseStart_4093831 : Nat := 118140960795 + 4093831 * 2 ^ 59
def prefixEnd_4093831 : Nat := 4983230072969 + 3 ^ 40 * 4093831 * 2
def baseEnd_4093831 : Nat := 1401402014184318400723547

theorem tailTrace_4093831 : CollatzResearch.WordTrace tailWord_4093831 prefixEnd_4093831 1401402014184318400723547 := by
  unfold tailWord_4093831
  simp only [CollatzResearch.WordTrace]
  refine ⟨149314283231756932516089347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99542855487837955010726231 149314283231756932516089347)
  ·
    refine ⟨223971424847635398774134021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149314283231756932516089347 223971424847635398774134021)
    ·
      refine ⟨41994642158931637270150129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223971424847635398774134021 41994642158931637270150129)
      ·
        refine ⟨31495981619198727952612597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41994642158931637270150129 31495981619198727952612597)
        ·
          refine ⟨2952748276799880745557431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31495981619198727952612597 2952748276799880745557431)
          ·
            refine ⟨4429122415199821118336147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952748276799880745557431 4429122415199821118336147)
            ·
              refine ⟨6643683622799731677504221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4429122415199821118336147 6643683622799731677504221)
              ·
                refine ⟨2491381358549899379064083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6643683622799731677504221 2491381358549899379064083)
                ·
                  refine ⟨3737072037824849068596125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491381358549899379064083 3737072037824849068596125)
                  ·
                    refine ⟨1401402014184318400723547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3737072037824849068596125 1401402014184318400723547)
                    ·
                      rfl

theorem cell22_4093831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_4093831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093831 prefixEnd_4093831 := by exact prefixLift 4093831
  have htrace : WordTrace (prefixWord ++ tailWord_4093831) baseStart_4093831 baseEnd_4093831 := by
    simpa [prefixWord, tailWord_4093831, baseEnd_4093831] using wordTrace_append hprefix tailTrace_4093831
  have hstable : (prefixWord ++ tailWord_4093831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093831).length < 2 ^ (prefixWord ++ tailWord_4093831).sum := by decide
  have hdescent : baseEnd_4093831 < baseStart_4093831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093885 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_4093885 : Nat := 118140960795 + 4093885 * 2 ^ 59
def prefixEnd_4093885 : Nat := 4983230072969 + 3 ^ 40 * 4093885 * 2
def baseEnd_4093885 : Nat := 1401420499487880259873381

theorem tailTrace_4093885 : CollatzResearch.WordTrace tailWord_4093885 prefixEnd_4093885 1401420499487880259873381 := by
  unfold tailWord_4093885
  simp only [CollatzResearch.WordTrace]
  refine ⟨149316252773561299738555109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99544168515707533159036739 149316252773561299738555109)
  ·
    refine ⟨27996797395042743700979083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149316252773561299738555109 27996797395042743700979083)
    ·
      refine ⟨41995196092564115551468625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27996797395042743700979083 41995196092564115551468625)
      ·
        refine ⟨31496397069423086663601469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41995196092564115551468625 31496397069423086663601469)
        ·
          refine ⟨11811148901033657498850551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31496397069423086663601469 11811148901033657498850551)
          ·
            refine ⟨17716723351550486248275827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11811148901033657498850551 17716723351550486248275827)
            ·
              refine ⟨26575085027325729372413741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17716723351550486248275827 26575085027325729372413741)
              ·
                refine ⟨9965656885247148514655153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26575085027325729372413741 9965656885247148514655153)
                ·
                  refine ⟨7474242663935361385991365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9965656885247148514655153 7474242663935361385991365)
                  ·
                    refine ⟨1401420499487880259873381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7474242663935361385991365 1401420499487880259873381)
                    ·
                      rfl

theorem cell22_4093885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_4093885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093885 prefixEnd_4093885 := by exact prefixLift 4093885
  have htrace : WordTrace (prefixWord ++ tailWord_4093885) baseStart_4093885 baseEnd_4093885 := by
    simpa [prefixWord, tailWord_4093885, baseEnd_4093885] using wordTrace_append hprefix tailTrace_4093885
  have hstable : (prefixWord ++ tailWord_4093885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093885).length < 2 ^ (prefixWord ++ tailWord_4093885).sum := by decide
  have hdescent : baseEnd_4093885 < baseStart_4093885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093906 : List Nat := [3, 2, 2, 3, 2, 2, 2, 2, 4]
def baseStart_4093906 : Nat := 118140960795 + 4093906 * 2 ^ 59
def prefixEnd_4093906 : Nat := 4983230072969 + 3 ^ 40 * 4093906 * 2
def baseEnd_4093906 : Nat := 467142562739014401699439

theorem tailTrace_4093906 : CollatzResearch.WordTrace tailWord_4093906 prefixEnd_4093906 467142562739014401699439 := by
  unfold tailWord_4093906
  simp only [CollatzResearch.WordTrace]
  refine ⟨37329254676621305081267393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99544679137656813550046381 37329254676621305081267393)
  ·
    refine ⟨27996941007465978810950545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37329254676621305081267393 27996941007465978810950545)
    ·
      refine ⟨20997705755599484108212909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27996941007465978810950545 20997705755599484108212909)
      ·
        refine ⟨7874139658349806540579841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20997705755599484108212909 7874139658349806540579841)
        ·
          refine ⟨5905604743762354905434881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7874139658349806540579841 5905604743762354905434881)
          ·
            refine ⟨4429203557821766179076161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5905604743762354905434881 4429203557821766179076161)
            ·
              refine ⟨3321902668366324634307121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4429203557821766179076161 3321902668366324634307121)
              ·
                refine ⟨2491427001274743475730341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3321902668366324634307121 2491427001274743475730341)
                ·
                  refine ⟨467142562739014401699439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2491427001274743475730341 467142562739014401699439)
                  ·
                    rfl

theorem cell22_4093906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_4093906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093906 prefixEnd_4093906 := by exact prefixLift 4093906
  have htrace : WordTrace (prefixWord ++ tailWord_4093906) baseStart_4093906 baseEnd_4093906 := by
    simpa [prefixWord, tailWord_4093906, baseEnd_4093906] using wordTrace_append hprefix tailTrace_4093906
  have hstable : (prefixWord ++ tailWord_4093906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093906).length < 2 ^ (prefixWord ++ tailWord_4093906).sum := by decide
  have hdescent : baseEnd_4093906 < baseStart_4093906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093917 : List Nat := [1, 4, 3, 1, 3, 2, 1, 7]
def baseStart_4093917 : Nat := 118140960795 + 4093917 * 2 ^ 59
def prefixEnd_4093917 : Nat := 4983230072969 + 3 ^ 40 * 4093917 * 2
def baseEnd_4093917 : Nat := 155714605971315871452587

theorem tailTrace_4093917 : CollatzResearch.WordTrace tailWord_4093917 prefixEnd_4093917 155714605971315871452587 := by
  unfold tailWord_4093917
  simp only [CollatzResearch.WordTrace]
  refine ⟨149317419909445369203720005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99544946606296912802480003 149317419909445369203720005)
  ·
    refine ⟨27997016233021006725697501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149317419909445369203720005 27997016233021006725697501)
    ·
      refine ⟨10498881087382877522136563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27997016233021006725697501 10498881087382877522136563)
      ·
        refine ⟨15748321631074316283204845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10498881087382877522136563 15748321631074316283204845)
        ·
          refine ⟨5905620611652868606201817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15748321631074316283204845 5905620611652868606201817)
          ·
            refine ⟨4429215458739651454651363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5905620611652868606201817 4429215458739651454651363)
            ·
              refine ⟨6643823188109477181977045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4429215458739651454651363 6643823188109477181977045)
              ·
                refine ⟨155714605971315871452587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6643823188109477181977045 155714605971315871452587)
                ·
                  rfl

theorem cell22_4093917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 7].length) (baseStart_4093917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093917 prefixEnd_4093917 := by exact prefixLift 4093917
  have htrace : WordTrace (prefixWord ++ tailWord_4093917) baseStart_4093917 baseEnd_4093917 := by
    simpa [prefixWord, tailWord_4093917, baseEnd_4093917] using wordTrace_append hprefix tailTrace_4093917
  have hstable : (prefixWord ++ tailWord_4093917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093917).length < 2 ^ (prefixWord ++ tailWord_4093917).sum := by decide
  have hdescent : baseEnd_4093917 < baseStart_4093917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093928 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 9]
def baseStart_4093928 : Nat := 118140960795 + 4093928 * 2 ^ 59
def prefixEnd_4093928 : Nat := 4983230072969 + 3 ^ 40 * 4093928 * 2
def baseEnd_4093928 : Nat := 467145073088880827016083

theorem tailTrace_4093928 : CollatzResearch.WordTrace tailWord_4093928 prefixEnd_4093928 467145073088880827016083 := by
  unfold tailWord_4093928
  simp only [CollatzResearch.WordTrace]
  refine ⟨74658910556202759041185219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99545214074937012054913625 74658910556202759041185219)
  ·
    refine ⟨111988365834304138561777829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74658910556202759041185219 111988365834304138561777829)
    ·
      refine ⟨20997818593932025980333343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111988365834304138561777829 20997818593932025980333343)
      ·
        refine ⟨31496727890898038970500015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20997818593932025980333343 31496727890898038970500015)
        ·
          refine ⟨47245091836347058455750023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31496727890898038970500015 47245091836347058455750023)
          ·
            refine ⟨70867637754520587683625035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47245091836347058455750023 70867637754520587683625035)
            ·
              refine ⟨106301456631780881525437553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70867637754520587683625035 106301456631780881525437553)
              ·
                refine ⟨79726092473835661144078165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106301456631780881525437553 79726092473835661144078165)
                ·
                  refine ⟨467145073088880827016083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79726092473835661144078165 467145073088880827016083)
                  ·
                    rfl

theorem cell22_4093928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 9].length) (baseStart_4093928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093928 prefixEnd_4093928 := by exact prefixLift 4093928
  have htrace : WordTrace (prefixWord ++ tailWord_4093928) baseStart_4093928 baseEnd_4093928 := by
    simpa [prefixWord, tailWord_4093928, baseEnd_4093928] using wordTrace_append hprefix tailTrace_4093928
  have hstable : (prefixWord ++ tailWord_4093928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093928).length < 2 ^ (prefixWord ++ tailWord_4093928).sum := by decide
  have hdescent : baseEnd_4093928 < baseStart_4093928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094005 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 1, 5]
def baseStart_4094005 : Nat := 118140960795 + 4094005 * 2 ^ 59
def prefixEnd_4094005 : Nat := 4983230072969 + 3 ^ 40 * 4094005 * 2
def baseEnd_4094005 : Nat := 1401461577940239946873013

theorem tailTrace_4094005 : CollatzResearch.WordTrace tailWord_4094005 prefixEnd_4094005 1401461577940239946873013 := by
  unfold tailWord_4094005
  simp only [CollatzResearch.WordTrace]
  refine ⟨149320629533126560232923469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99547086355417706821948979 149320629533126560232923469)
  ·
    refine ⟨55995236074922460087346301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149320629533126560232923469 55995236074922460087346301)
    ·
      refine ⟨20998213528095922532754863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55995236074922460087346301 20998213528095922532754863)
      ·
        refine ⟨31497320292143883799132295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20998213528095922532754863 31497320292143883799132295)
        ·
          refine ⟨47245980438215825698698443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31497320292143883799132295 47245980438215825698698443)
          ·
            refine ⟨70868970657323738548047665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47245980438215825698698443 70868970657323738548047665)
            ·
              refine ⟨53151727992992803911035749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70868970657323738548047665 53151727992992803911035749)
              ·
                refine ⟨9965948998686150733319203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53151727992992803911035749 9965948998686150733319203)
                ·
                  refine ⟨14948923498029226099978805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9965948998686150733319203 14948923498029226099978805)
                  ·
                    refine ⟨1401461577940239946873013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14948923498029226099978805 1401461577940239946873013)
                    ·
                      rfl

theorem cell22_4094005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_4094005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094005 prefixEnd_4094005 := by exact prefixLift 4094005
  have htrace : WordTrace (prefixWord ++ tailWord_4094005) baseStart_4094005 baseEnd_4094005 := by
    simpa [prefixWord, tailWord_4094005, baseEnd_4094005] using wordTrace_append hprefix tailTrace_4094005
  have hstable : (prefixWord ++ tailWord_4094005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094005).length < 2 ^ (prefixWord ++ tailWord_4094005).sum := by decide
  have hdescent : baseEnd_4094005 < baseStart_4094005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094007 : List Nat := [1, 1, 3, 1, 2, 2, 5, 3, 4]
def baseStart_4094007 : Nat := 118140960795 + 4094007 * 2 ^ 59
def prefixEnd_4094007 : Nat := 4983230072969 + 3 ^ 40 * 4094007 * 2
def baseEnd_4094007 : Nat := 467154087527037536107669

theorem tailTrace_4094007 : CollatzResearch.WordTrace tailWord_4094007 prefixEnd_4094007 467154087527037536107669 := by
  unfold tailWord_4094007
  simp only [CollatzResearch.WordTrace]
  refine ⟨149320702479119314574496275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99547134986079543049664183 149320702479119314574496275)
  ·
    refine ⟨223981053718678971861744413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149320702479119314574496275 223981053718678971861744413)
    ·
      refine ⟨83992895144504614448154155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223981053718678971861744413 83992895144504614448154155)
      ·
        refine ⟨125989342716756921672231233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83992895144504614448154155 125989342716756921672231233)
        ·
          refine ⟨94492007037567691254173425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125989342716756921672231233 94492007037567691254173425)
          ·
            refine ⟨70869005278175768440630069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94492007037567691254173425 70869005278175768440630069)
            ·
              refine ⟨6643969244828978291309069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70869005278175768440630069 6643969244828978291309069)
              ·
                refine ⟨2491488466810866859240901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6643969244828978291309069 2491488466810866859240901)
                ·
                  refine ⟨467154087527037536107669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2491488466810866859240901 467154087527037536107669)
                  ·
                    rfl

theorem cell22_4094007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 4].length) (baseStart_4094007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094007 prefixEnd_4094007 := by exact prefixLift 4094007
  have htrace : WordTrace (prefixWord ++ tailWord_4094007) baseStart_4094007 baseEnd_4094007 := by
    simpa [prefixWord, tailWord_4094007, baseEnd_4094007] using wordTrace_append hprefix tailTrace_4094007
  have hstable : (prefixWord ++ tailWord_4094007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094007).length < 2 ^ (prefixWord ++ tailWord_4094007).sum := by decide
  have hdescent : baseEnd_4094007 < baseStart_4094007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094039 : List Nat := [1, 1, 3, 2, 2, 1, 6, 1, 2, 3]
def baseStart_4094039 : Nat := 118140960795 + 4094039 * 2 ^ 59
def prefixEnd_4094039 : Nat := 4983230072969 + 3 ^ 40 * 4094039 * 2
def baseEnd_4094039 : Nat := 1401473216835075191522909

theorem tailTrace_4094039 : CollatzResearch.WordTrace tailWord_4094039 prefixEnd_4094039 1401473216835075191522909 := by
  unfold tailWord_4094039
  simp only [CollatzResearch.WordTrace]
  refine ⟨149321869615003384039661171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99547913076668922693107447 149321869615003384039661171)
  ·
    refine ⟨223982804422505076059491757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149321869615003384039661171 223982804422505076059491757)
    ·
      refine ⟨83993551658439403522309409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223982804422505076059491757 83993551658439403522309409)
      ·
        refine ⟨62995163743829552641732057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83993551658439403522309409 62995163743829552641732057)
        ·
          refine ⟨47246372807872164481299043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62995163743829552641732057 47246372807872164481299043)
          ·
            refine ⟨70869559211808246721948565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47246372807872164481299043 70869559211808246721948565)
            ·
              refine ⟨3322010588053511565091339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70869559211808246721948565 3322010588053511565091339)
              ·
                refine ⟨4983015882080267347637009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3322010588053511565091339 4983015882080267347637009)
                ·
                  refine ⟨3737261911560200510727757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4983015882080267347637009 3737261911560200510727757)
                  ·
                    refine ⟨1401473216835075191522909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3737261911560200510727757 1401473216835075191522909)
                    ·
                      rfl

theorem cell22_4094039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_4094039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094039 prefixEnd_4094039 := by exact prefixLift 4094039
  have htrace : WordTrace (prefixWord ++ tailWord_4094039) baseStart_4094039 baseEnd_4094039 := by
    simpa [prefixWord, tailWord_4094039, baseEnd_4094039] using wordTrace_append hprefix tailTrace_4094039
  have hstable : (prefixWord ++ tailWord_4094039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094039).length < 2 ^ (prefixWord ++ tailWord_4094039).sum := by decide
  have hdescent : baseEnd_4094039 < baseStart_4094039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094146 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_4094146 : Nat := 118140960795 + 4094146 * 2 ^ 59
def prefixEnd_4094146 : Nat := 4983230072969 + 3 ^ 40 * 4094146 * 2
def baseEnd_4094146 : Nat := 1401509845121762579097581

theorem tailTrace_4094146 : CollatzResearch.WordTrace tailWord_4094146 prefixEnd_4094146 1401509845121762579097581 := by
  unfold tailWord_4094146
  simp only [CollatzResearch.WordTrace]
  refine ⟨37331443056403935328451573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99550514817077160875870861 37331443056403935328451573)
  ·
    refine ⟨3499822786537868937042335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37331443056403935328451573 3499822786537868937042335)
    ·
      refine ⟨5249734179806803405563503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3499822786537868937042335 5249734179806803405563503)
      ·
        refine ⟨7874601269710205108345255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5249734179806803405563503 7874601269710205108345255)
        ·
          refine ⟨11811901904565307662517883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7874601269710205108345255 11811901904565307662517883)
          ·
            refine ⟨17717852856847961493776825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11811901904565307662517883 17717852856847961493776825)
            ·
              refine ⟨13288389642635971120332619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17717852856847961493776825 13288389642635971120332619)
              ·
                refine ⟨19932584463953956680498929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13288389642635971120332619 19932584463953956680498929)
                ·
                  refine ⟨14949438347965467510374197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19932584463953956680498929 14949438347965467510374197)
                  ·
                    refine ⟨1401509845121762579097581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14949438347965467510374197 1401509845121762579097581)
                    ·
                      rfl

theorem cell22_4094146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_4094146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094146 prefixEnd_4094146 := by exact prefixLift 4094146
  have htrace : WordTrace (prefixWord ++ tailWord_4094146) baseStart_4094146 baseEnd_4094146 := by
    simpa [prefixWord, tailWord_4094146, baseEnd_4094146] using wordTrace_append hprefix tailTrace_4094146
  have hstable : (prefixWord ++ tailWord_4094146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094146).length < 2 ^ (prefixWord ++ tailWord_4094146).sum := by decide
  have hdescent : baseEnd_4094146 < baseStart_4094146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094155 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 3, 6]
def baseStart_4094155 : Nat := 118140960795 + 4094155 * 2 ^ 59
def prefixEnd_4094155 : Nat := 4983230072969 + 3 ^ 40 * 4094155 * 2
def baseEnd_4094155 : Nat := 1401512926005689555622553

theorem tailTrace_4094155 : CollatzResearch.WordTrace tailWord_4094155 prefixEnd_4094155 1401512926005689555622553 := by
  unfold tailWord_4094155
  simp only [CollatzResearch.WordTrace]
  refine ⟨149326100482583135850883919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99550733655055423900589279 149326100482583135850883919)
  ·
    refine ⟨223989150723874703776325879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149326100482583135850883919 223989150723874703776325879)
    ·
      refine ⟨335983726085812055664488819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223989150723874703776325879 335983726085812055664488819)
      ·
        refine ⟨503975589128718083496733229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335983726085812055664488819 503975589128718083496733229)
        ·
          refine ⟨188990845923269281311274961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503975589128718083496733229 188990845923269281311274961)
          ·
            refine ⟨141743134442451960983456221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188990845923269281311274961 141743134442451960983456221)
            ·
              refine ⟨53153675415919485368796083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141743134442451960983456221 53153675415919485368796083)
              ·
                refine ⟨79730513123879228053194125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53153675415919485368796083 79730513123879228053194125)
                ·
                  refine ⟨29898942421454710519947797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79730513123879228053194125 29898942421454710519947797)
                  ·
                    refine ⟨1401512926005689555622553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29898942421454710519947797 1401512926005689555622553)
                    ·
                      rfl

theorem cell22_4094155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 6].length) (baseStart_4094155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094155 prefixEnd_4094155 := by exact prefixLift 4094155
  have htrace : WordTrace (prefixWord ++ tailWord_4094155) baseStart_4094155 baseEnd_4094155 := by
    simpa [prefixWord, tailWord_4094155, baseEnd_4094155] using wordTrace_append hprefix tailTrace_4094155
  have hstable : (prefixWord ++ tailWord_4094155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094155).length < 2 ^ (prefixWord ++ tailWord_4094155).sum := by decide
  have hdescent : baseEnd_4094155 < baseStart_4094155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094185 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 1, 9]
def baseStart_4094185 : Nat := 118140960795 + 4094185 * 2 ^ 59
def prefixEnd_4094185 : Nat := 4983230072969 + 3 ^ 40 * 4094185 * 2
def baseEnd_4094185 : Nat := 1401523195618779477372461

theorem tailTrace_4094185 : CollatzResearch.WordTrace tailWord_4094185 prefixEnd_4094185 1401523195618779477372461 := by
  unfold tailWord_4094185
  simp only [CollatzResearch.WordTrace]
  refine ⟨149327194672474450974476009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99551463114982967316317339 149327194672474450974476009)
  ·
    refine ⟨111995396004355838230857007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149327194672474450974476009 111995396004355838230857007)
    ·
      refine ⟨167993094006533757346285511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111995396004355838230857007 167993094006533757346285511)
      ·
        refine ⟨251989641009800636019428267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167993094006533757346285511 251989641009800636019428267)
        ·
          refine ⟨377984461514700954029142401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251989641009800636019428267 377984461514700954029142401)
          ·
            refine ⟨283488346136025715521856801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377984461514700954029142401 283488346136025715521856801)
            ·
              refine ⟨212616259602019286641392601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283488346136025715521856801 212616259602019286641392601)
              ·
                refine ⟨159462194701514464981044451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212616259602019286641392601 159462194701514464981044451)
                ·
                  refine ⟨239193292052271697471566677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159462194701514464981044451 239193292052271697471566677)
                  ·
                    refine ⟨1401523195618779477372461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 239193292052271697471566677 1401523195618779477372461)
                    ·
                      rfl

theorem cell22_4094185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_4094185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094185 prefixEnd_4094185 := by exact prefixLift 4094185
  have htrace : WordTrace (prefixWord ++ tailWord_4094185) baseStart_4094185 baseEnd_4094185 := by
    simpa [prefixWord, tailWord_4094185, baseEnd_4094185] using wordTrace_append hprefix tailTrace_4094185
  have hstable : (prefixWord ++ tailWord_4094185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094185).length < 2 ^ (prefixWord ++ tailWord_4094185).sum := by decide
  have hdescent : baseEnd_4094185 < baseStart_4094185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094236 : List Nat := [2, 2, 3, 1, 1, 1, 1, 7, 1, 3]
def baseStart_4094236 : Nat := 118140960795 + 4094236 * 2 ^ 59
def prefixEnd_4094236 : Nat := 4983230072969 + 3 ^ 40 * 4094236 * 2
def baseEnd_4094236 : Nat := 1401540653961032344347305

theorem tailTrace_4094236 : CollatzResearch.WordTrace tailWord_4094236 prefixEnd_4094236 1401540653961032344347305 := by
  unfold tailWord_4094236
  simp only [CollatzResearch.WordTrace]
  refine ⟨74664527397644843342291281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99552703196859791123055041 74664527397644843342291281)
  ·
    refine ⟨55998395548233632506718461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74664527397644843342291281 55998395548233632506718461)
    ·
      refine ⟨20999398330587612190019423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55998395548233632506718461 20999398330587612190019423)
      ·
        refine ⟨31499097495881418285029135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20999398330587612190019423 31499097495881418285029135)
        ·
          refine ⟨47248646243822127427543703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31499097495881418285029135 47248646243822127427543703)
          ·
            refine ⟨70872969365733191141315555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47248646243822127427543703 70872969365733191141315555)
            ·
              refine ⟨106309454048599786711973333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70872969365733191141315555 106309454048599786711973333)
              ·
                refine ⟨2491627829264057501061875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 106309454048599786711973333 2491627829264057501061875)
                ·
                  refine ⟨3737441743896086251592813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491627829264057501061875 3737441743896086251592813)
                  ·
                    refine ⟨1401540653961032344347305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3737441743896086251592813 1401540653961032344347305)
                    ·
                      rfl

theorem cell22_4094236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_4094236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094236 prefixEnd_4094236 := by exact prefixLift 4094236
  have htrace : WordTrace (prefixWord ++ tailWord_4094236) baseStart_4094236 baseEnd_4094236 := by
    simpa [prefixWord, tailWord_4094236, baseEnd_4094236] using wordTrace_append hprefix tailTrace_4094236
  have hstable : (prefixWord ++ tailWord_4094236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094236).length < 2 ^ (prefixWord ++ tailWord_4094236).sum := by decide
  have hdescent : baseEnd_4094236 < baseStart_4094236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094279 : List Nat := [1, 1, 4, 1, 2, 2, 2, 4, 1, 4]
def baseStart_4094279 : Nat := 118140960795 + 4094279 * 2 ^ 59
def prefixEnd_4094279 : Nat := 4983230072969 + 3 ^ 40 * 4094279 * 2
def baseEnd_4094279 : Nat := 1401555373739794565522173

theorem tailTrace_4094279 : CollatzResearch.WordTrace tailWord_4094279 prefixEnd_4094279 1401555373739794565522173 := by
  unfold tailWord_4094279
  simp only [CollatzResearch.WordTrace]
  refine ⟨149330623134133905028397891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99553748756089270018931927 149330623134133905028397891)
  ·
    refine ⟨223995934701200857542596837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149330623134133905028397891 223995934701200857542596837)
    ·
      refine ⟨41999237756475160789236907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223995934701200857542596837 41999237756475160789236907)
      ·
        refine ⟨62998856634712741183855361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41999237756475160789236907 62998856634712741183855361)
        ·
          refine ⟨47249142476034555887891521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62998856634712741183855361 47249142476034555887891521)
          ·
            refine ⟨35436856857025916915918641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47249142476034555887891521 35436856857025916915918641)
            ·
              refine ⟨26577642642769437686938981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35436856857025916915918641 26577642642769437686938981)
              ·
                refine ⟨4983307995519269566301059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26577642642769437686938981 4983307995519269566301059)
                ·
                  refine ⟨7474961993278904349451589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4983307995519269566301059 7474961993278904349451589)
                  ·
                    refine ⟨1401555373739794565522173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7474961993278904349451589 1401555373739794565522173)
                    ·
                      rfl

theorem cell22_4094279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_4094279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094279 prefixEnd_4094279 := by exact prefixLift 4094279
  have htrace : WordTrace (prefixWord ++ tailWord_4094279) baseStart_4094279 baseEnd_4094279 := by
    simpa [prefixWord, tailWord_4094279, baseEnd_4094279] using wordTrace_append hprefix tailTrace_4094279
  have hstable : (prefixWord ++ tailWord_4094279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094279).length < 2 ^ (prefixWord ++ tailWord_4094279).sum := by decide
  have hdescent : baseEnd_4094279 < baseStart_4094279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094300 : List Nat := [2, 2, 4, 3, 2, 1, 1, 2, 5]
def baseStart_4094300 : Nat := 118140960795 + 4094300 * 2 ^ 59
def prefixEnd_4094300 : Nat := 4983230072969 + 3 ^ 40 * 4094300 * 2
def baseEnd_4094300 : Nat := 467187520822985836915703

theorem tailTrace_4094300 : CollatzResearch.WordTrace tailWord_4094300 prefixEnd_4094300 467187520822985836915703 := by
  unfold tailWord_4094300
  simp only [CollatzResearch.WordTrace]
  refine ⟨74665694533528912807456177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99554259378038550409941569 74665694533528912807456177)
  ·
    refine ⟨55999270900146684605592133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74665694533528912807456177 55999270900146684605592133)
    ·
      refine ⟨10499863293777503363548525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55999270900146684605592133 10499863293777503363548525)
      ·
        refine ⟨3937448735166563761330697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10499863293777503363548525 3937448735166563761330697)
        ·
          refine ⟨2953086551374922820998023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3937448735166563761330697 2953086551374922820998023)
          ·
            refine ⟨4429629827062384231497035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2953086551374922820998023 4429629827062384231497035)
            ·
              refine ⟨6644444740593576347245553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4429629827062384231497035 6644444740593576347245553)
              ·
                refine ⟨4983333555445182260434165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6644444740593576347245553 4983333555445182260434165)
                ·
                  refine ⟨467187520822985836915703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4983333555445182260434165 467187520822985836915703)
                  ·
                    rfl

theorem cell22_4094300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_4094300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094300 prefixEnd_4094300 := by exact prefixLift 4094300
  have htrace : WordTrace (prefixWord ++ tailWord_4094300) baseStart_4094300 baseEnd_4094300 := by
    simpa [prefixWord, tailWord_4094300, baseEnd_4094300] using wordTrace_append hprefix tailTrace_4094300
  have hstable : (prefixWord ++ tailWord_4094300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094300).length < 2 ^ (prefixWord ++ tailWord_4094300).sum := by decide
  have hdescent : baseEnd_4094300 < baseStart_4094300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094311 : List Nat := [1, 1, 5, 1, 3, 1, 2, 4, 4]
def baseStart_4094311 : Nat := 118140960795 + 4094311 * 2 ^ 59
def prefixEnd_4094311 : Nat := 4983230072969 + 3 ^ 40 * 4094311 * 2
def baseEnd_4094311 : Nat := 467188775997919049574025

theorem tailTrace_4094311 : CollatzResearch.WordTrace tailWord_4094311 prefixEnd_4094311 467188775997919049574025 := by
  unfold tailWord_4094311
  simp only [CollatzResearch.WordTrace]
  refine ⟨149331790270017974493562787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99554526846678649662375191 149331790270017974493562787)
  ·
    refine ⟨223997685405026961740344181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149331790270017974493562787 223997685405026961740344181)
    ·
      refine ⟨20999783006721277663157267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223997685405026961740344181 20999783006721277663157267)
      ·
        refine ⟨31499674510081916494735901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20999783006721277663157267 31499674510081916494735901)
        ·
          refine ⟨11812377941280718685525963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31499674510081916494735901 11812377941280718685525963)
          ·
            refine ⟨17718566911921078028288945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11812377941280718685525963 17718566911921078028288945)
            ·
              refine ⟨13288925183940808521216709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17718566911921078028288945 13288925183940808521216709)
              ·
                refine ⟨2491673471988901597728133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13288925183940808521216709 2491673471988901597728133)
                ·
                  refine ⟨467188775997919049574025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2491673471988901597728133 467188775997919049574025)
                  ·
                    rfl

theorem cell22_4094311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 4].length) (baseStart_4094311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094311 prefixEnd_4094311 := by exact prefixLift 4094311
  have htrace : WordTrace (prefixWord ++ tailWord_4094311) baseStart_4094311 baseEnd_4094311 := by
    simpa [prefixWord, tailWord_4094311, baseEnd_4094311] using wordTrace_append hprefix tailTrace_4094311
  have hstable : (prefixWord ++ tailWord_4094311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094311).length < 2 ^ (prefixWord ++ tailWord_4094311).sum := by decide
  have hdescent : baseEnd_4094311 < baseStart_4094311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094339 : List Nat := [1, 1, 1, 3, 6, 1, 1, 8]
def baseStart_4094339 : Nat := 118140960795 + 4094339 * 2 ^ 59
def prefixEnd_4094339 : Nat := 4983230072969 + 3 ^ 40 * 4094339 * 2
def baseEnd_4094339 : Nat := 155730656996219378780221

theorem tailTrace_4094339 : CollatzResearch.WordTrace tailWord_4094339 prefixEnd_4094339 155730656996219378780221 := by
  unfold tailWord_4094339
  simp only [CollatzResearch.WordTrace]
  refine ⟨149332811513916535275582071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99555207675944356850388047 149332811513916535275582071)
  ·
    refine ⟨223999217270874802913373107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149332811513916535275582071 223999217270874802913373107)
    ·
      refine ⟨335998825906312204370059661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223999217270874802913373107 335998825906312204370059661)
      ·
        refine ⟨125999559714867076638772373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335998825906312204370059661 125999559714867076638772373)
        ·
          refine ⟨5906229361634394217442455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125999559714867076638772373 5906229361634394217442455)
          ·
            refine ⟨8859344042451591326163683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5906229361634394217442455 8859344042451591326163683)
            ·
              refine ⟨13289016063677386989245525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8859344042451591326163683 13289016063677386989245525)
              ·
                refine ⟨155730656996219378780221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13289016063677386989245525 155730656996219378780221)
                ·
                  rfl

theorem cell22_4094339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 8].length) (baseStart_4094339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094339 prefixEnd_4094339 := by exact prefixLift 4094339
  have htrace : WordTrace (prefixWord ++ tailWord_4094339) baseStart_4094339 baseEnd_4094339 := by
    simpa [prefixWord, tailWord_4094339, baseEnd_4094339] using wordTrace_append hprefix tailTrace_4094339
  have hstable : (prefixWord ++ tailWord_4094339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094339).length < 2 ^ (prefixWord ++ tailWord_4094339).sum := by decide
  have hdescent : baseEnd_4094339 < baseStart_4094339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094352 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 6, 6]
def baseStart_4094352 : Nat := 118140960795 + 4094352 * 2 ^ 59
def prefixEnd_4094352 : Nat := 4983230072969 + 3 ^ 40 * 4094352 * 2
def baseEnd_4094352 : Nat := 1401580363131646708446949

theorem tailTrace_4094352 : CollatzResearch.WordTrace tailWord_4094352 prefixEnd_4094352 1401580363131646708446949 := by
  unfold tailWord_4094352
  simp only [CollatzResearch.WordTrace]
  refine ⟨74666642831434719247902655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99555523775246292330536873 74666642831434719247902655)
  ·
    refine ⟨111999964247152078871853983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74666642831434719247902655 111999964247152078871853983)
    ·
      refine ⟨167999946370728118307780975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111999964247152078871853983 167999946370728118307780975)
      ·
        refine ⟨251999919556092177461671463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167999946370728118307780975 251999919556092177461671463)
        ·
          refine ⟨377999879334138266192507195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251999919556092177461671463 377999879334138266192507195)
          ·
            refine ⟨566999819001207399288760793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377999879334138266192507195 566999819001207399288760793)
            ·
              refine ⟨425249864250905549466570595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566999819001207399288760793 425249864250905549466570595)
              ·
                refine ⟨637874796376358324199855893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425249864250905549466570595 637874796376358324199855893)
                ·
                  refine ⟨29900381080141796446868245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 637874796376358324199855893 29900381080141796446868245)
                  ·
                    refine ⟨1401580363131646708446949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29900381080141796446868245 1401580363131646708446949)
                    ·
                      rfl

theorem cell22_4094352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_4094352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094352 prefixEnd_4094352 := by exact prefixLift 4094352
  have htrace : WordTrace (prefixWord ++ tailWord_4094352) baseStart_4094352 baseEnd_4094352 := by
    simpa [prefixWord, tailWord_4094352, baseEnd_4094352] using wordTrace_append hprefix tailTrace_4094352
  have hstable : (prefixWord ++ tailWord_4094352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094352).length < 2 ^ (prefixWord ++ tailWord_4094352).sum := by decide
  have hdescent : baseEnd_4094352 < baseStart_4094352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094356 : List Nat := [2, 4, 2, 1, 3, 2, 8]
def baseStart_4094356 : Nat := 118140960795 + 4094356 * 2 ^ 59
def prefixEnd_4094356 : Nat := 4983230072969 + 3 ^ 40 * 4094356 * 2
def baseEnd_4094356 : Nat := 51910434533829334494331

theorem tailTrace_4094356 : CollatzResearch.WordTrace tailWord_4094356 prefixEnd_4094356 51910434533829334494331 := by
  unfold tailWord_4094356
  simp only [CollatzResearch.WordTrace]
  refine ⟨74666715777427473589475461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99555621036569964785967281 74666715777427473589475461)
  ·
    refine ⟨14000009208267651298026649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74666715777427473589475461 14000009208267651298026649)
    ·
      refine ⟨10500006906200738473519987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14000009208267651298026649 10500006906200738473519987)
      ·
        refine ⟨15750010359301107710279981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10500006906200738473519987 15750010359301107710279981)
        ·
          refine ⟨5906253884737915391354993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15750010359301107710279981 5906253884737915391354993)
          ·
            refine ⟨4429690413553436543516245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5906253884737915391354993 4429690413553436543516245)
            ·
              refine ⟨51910434533829334494331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4429690413553436543516245 51910434533829334494331)
              ·
                rfl

theorem cell22_4094356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 8].length) (baseStart_4094356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094356 prefixEnd_4094356 := by exact prefixLift 4094356
  have htrace : WordTrace (prefixWord ++ tailWord_4094356) baseStart_4094356 baseEnd_4094356 := by
    simpa [prefixWord, tailWord_4094356, baseEnd_4094356] using wordTrace_append hprefix tailTrace_4094356
  have hstable : (prefixWord ++ tailWord_4094356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094356).length < 2 ^ (prefixWord ++ tailWord_4094356).sum := by decide
  have hdescent : baseEnd_4094356 < baseStart_4094356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094371 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 3, 3]
def baseStart_4094371 : Nat := 118140960795 + 4094371 * 2 ^ 59
def prefixEnd_4094371 : Nat := 4983230072969 + 3 ^ 40 * 4094371 * 2
def baseEnd_4094371 : Nat := 1401586867219936992221891

theorem tailTrace_4094371 : CollatzResearch.WordTrace tailWord_4094371 prefixEnd_4094371 1401586867219936992221891 := by
  unfold tailWord_4094371
  simp only [CollatzResearch.WordTrace]
  refine ⟨149333978649800604740746967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99555985766533736493831311 149333978649800604740746967)
  ·
    refine ⟨224000967974700907111120451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149333978649800604740746967 224000967974700907111120451)
    ·
      refine ⟨336001451962051360666680677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224000967974700907111120451 336001451962051360666680677)
      ·
        refine ⟨63000272242884630125002627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336001451962051360666680677 63000272242884630125002627)
        ·
          refine ⟨94500408364326945187503941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63000272242884630125002627 94500408364326945187503941)
          ·
            refine ⟨17718826568311302222656989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94500408364326945187503941 17718826568311302222656989)
            ·
              refine ⟨6644559963116738333496371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17718826568311302222656989 6644559963116738333496371)
              ·
                refine ⟨9966839944675107500244557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6644559963116738333496371 9966839944675107500244557)
                ·
                  refine ⟨3737564979253165312591709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9966839944675107500244557 3737564979253165312591709)
                  ·
                    refine ⟨1401586867219936992221891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3737564979253165312591709 1401586867219936992221891)
                    ·
                      rfl

theorem cell22_4094371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 3].length) (baseStart_4094371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094371 prefixEnd_4094371 := by exact prefixLift 4094371
  have htrace : WordTrace (prefixWord ++ tailWord_4094371) baseStart_4094371 baseEnd_4094371 := by
    simpa [prefixWord, tailWord_4094371, baseEnd_4094371] using wordTrace_append hprefix tailTrace_4094371
  have hstable : (prefixWord ++ tailWord_4094371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094371).length < 2 ^ (prefixWord ++ tailWord_4094371).sum := by decide
  have hdescent : baseEnd_4094371 < baseStart_4094371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094446 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_4094446 : Nat := 118140960795 + 4094446 * 2 ^ 59
def prefixEnd_4094446 : Nat := 4983230072969 + 3 ^ 40 * 4094446 * 2
def baseEnd_4094446 : Nat := 467204180417553932198887

theorem tailTrace_4094446 : CollatzResearch.WordTrace tailWord_4094446 prefixEnd_4094446 467204180417553932198887 := by
  unfold tailWord_4094446
  simp only [CollatzResearch.WordTrace]
  refine ⟨18667089265566111568715899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99557809416352595033151461 18667089265566111568715899)
  ·
    refine ⟨28000633898349167353073849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18667089265566111568715899 28000633898349167353073849)
    ·
      refine ⟨21000475423761875514805387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28000633898349167353073849 21000475423761875514805387)
      ·
        refine ⟨31500713135642813272208081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21000475423761875514805387 31500713135642813272208081)
        ·
          refine ⟨23625534851732109954156061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31500713135642813272208081 23625534851732109954156061)
          ·
            refine ⟨8859575569399541232808523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23625534851732109954156061 8859575569399541232808523)
            ·
              refine ⟨13289363354099311849212785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8859575569399541232808523 13289363354099311849212785)
              ·
                refine ⟨9967022515574483886909589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13289363354099311849212785 9967022515574483886909589)
                ·
                  refine ⟨467204180417553932198887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9967022515574483886909589 467204180417553932198887)
                  ·
                    rfl

theorem cell22_4094446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_4094446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094446 prefixEnd_4094446 := by exact prefixLift 4094446
  have htrace : WordTrace (prefixWord ++ tailWord_4094446) baseStart_4094446 baseEnd_4094446 := by
    simpa [prefixWord, tailWord_4094446, baseEnd_4094446] using wordTrace_append hprefix tailTrace_4094446
  have hstable : (prefixWord ++ tailWord_4094446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094446).length < 2 ^ (prefixWord ++ tailWord_4094446).sum := by decide
  have hdescent : baseEnd_4094446 < baseStart_4094446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094461 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 4, 3]
def baseStart_4094461 : Nat := 118140960795 + 4094461 * 2 ^ 59
def prefixEnd_4094461 : Nat := 4983230072969 + 3 ^ 40 * 4094461 * 2
def baseEnd_4094461 : Nat := 1401617676059206757471615

theorem tailTrace_4094461 : CollatzResearch.WordTrace tailWord_4094461 prefixEnd_4094461 1401617676059206757471615 := by
  unfold tailWord_4094461
  simp only [CollatzResearch.WordTrace]
  refine ⟨149337261219474550111523237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99558174146316366741015491 149337261219474550111523237)
  ·
    refine ⟨28000736478651478145910607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149337261219474550111523237 28000736478651478145910607)
    ·
      refine ⟨42001104717977217218865911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28000736478651478145910607 42001104717977217218865911)
      ·
        refine ⟨63001657076965825828298867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42001104717977217218865911 63001657076965825828298867)
        ·
          refine ⟨94502485615448738742448301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63001657076965825828298867 94502485615448738742448301)
          ·
            refine ⟨35438432105793277028418113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94502485615448738742448301 35438432105793277028418113)
            ·
              refine ⟨26578824079344957771313585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35438432105793277028418113 26578824079344957771313585)
              ·
                refine ⟨19934118059508718328485189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26578824079344957771313585 19934118059508718328485189)
                ·
                  refine ⟨3737647136157884686590973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19934118059508718328485189 3737647136157884686590973)
                  ·
                    refine ⟨1401617676059206757471615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3737647136157884686590973 1401617676059206757471615)
                    ·
                      rfl

theorem cell22_4094461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_4094461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094461 prefixEnd_4094461 := by exact prefixLift 4094461
  have htrace : WordTrace (prefixWord ++ tailWord_4094461) baseStart_4094461 baseEnd_4094461 := by
    simpa [prefixWord, tailWord_4094461, baseEnd_4094461] using wordTrace_append hprefix tailTrace_4094461
  have hstable : (prefixWord ++ tailWord_4094461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094461).length < 2 ^ (prefixWord ++ tailWord_4094461).sum := by decide
  have hdescent : baseEnd_4094461 < baseStart_4094461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094465 : List Nat := [1, 2, 4, 1, 3, 3, 2, 1, 1, 4]
def baseStart_4094465 : Nat := 118140960795 + 4094465 * 2 ^ 59
def prefixEnd_4094465 : Nat := 4983230072969 + 3 ^ 40 * 4094465 * 2
def baseEnd_4094465 : Nat := 1401619045340952080371603

theorem tailTrace_4094465 : CollatzResearch.WordTrace tailWord_4094465 prefixEnd_4094465 1401619045340952080371603 := by
  unfold tailWord_4094465
  simp only [CollatzResearch.WordTrace]
  refine ⟨149337407111460058794668849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99558271407640039196445899 149337407111460058794668849)
  ·
    refine ⟨112003055333595044096001637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149337407111460058794668849 112003055333595044096001637)
    ·
      refine ⟨21000572875049070768000307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112003055333595044096001637 21000572875049070768000307)
      ·
        refine ⟨31500859312573606152000461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21000572875049070768000307 31500859312573606152000461)
        ·
          refine ⟨11812822242215102307000173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31500859312573606152000461 11812822242215102307000173)
          ·
            refine ⟨4429808340830663365125065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11812822242215102307000173 4429808340830663365125065)
            ·
              refine ⟨3322356255622997523843799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4429808340830663365125065 3322356255622997523843799)
              ·
                refine ⟨4983534383434496285765699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3322356255622997523843799 4983534383434496285765699)
                ·
                  refine ⟨7475301575151744428648549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4983534383434496285765699 7475301575151744428648549)
                  ·
                    refine ⟨1401619045340952080371603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7475301575151744428648549 1401619045340952080371603)
                    ·
                      rfl

theorem cell22_4094465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_4094465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094465 prefixEnd_4094465 := by exact prefixLift 4094465
  have htrace : WordTrace (prefixWord ++ tailWord_4094465) baseStart_4094465 baseEnd_4094465 := by
    simpa [prefixWord, tailWord_4094465, baseEnd_4094465] using wordTrace_append hprefix tailTrace_4094465
  have hstable : (prefixWord ++ tailWord_4094465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094465).length < 2 ^ (prefixWord ++ tailWord_4094465).sum := by decide
  have hdescent : baseEnd_4094465 < baseStart_4094465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094474 : List Nat := [3, 1, 2, 2, 2, 1, 11]
def baseStart_4094474 : Nat := 118140960795 + 4094474 * 2 ^ 59
def prefixEnd_4094474 : Nat := 4983230072969 + 3 ^ 40 * 4094474 * 2
def baseEnd_4094474 : Nat := 51911930600921446551725

theorem tailTrace_4094474 : CollatzResearch.WordTrace tailWord_4094474 prefixEnd_4094474 51911930600921446551725 := by
  unfold tailWord_4094474
  simp only [CollatzResearch.WordTrace]
  refine ⟨37334433842106863332936619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99558490245618302221164317 37334433842106863332936619)
  ·
    refine ⟨56001650763160294999404929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37334433842106863332936619 56001650763160294999404929)
    ·
      refine ⟨42001238072370221249553697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56001650763160294999404929 42001238072370221249553697)
      ·
        refine ⟨31500928554277665937165273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42001238072370221249553697 31500928554277665937165273)
        ·
          refine ⟨23625696415708249452873955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31500928554277665937165273 23625696415708249452873955)
          ·
            refine ⟨35438544623562374179310933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23625696415708249452873955 35438544623562374179310933)
            ·
              refine ⟨51911930600921446551725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35438544623562374179310933 51911930600921446551725)
              ·
                rfl

theorem cell22_4094474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 11].length) (baseStart_4094474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094474 prefixEnd_4094474 := by exact prefixLift 4094474
  have htrace : WordTrace (prefixWord ++ tailWord_4094474) baseStart_4094474 baseEnd_4094474 := by
    simpa [prefixWord, tailWord_4094474, baseEnd_4094474] using wordTrace_append hprefix tailTrace_4094474
  have hstable : (prefixWord ++ tailWord_4094474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094474).length < 2 ^ (prefixWord ++ tailWord_4094474).sum := by decide
  have hdescent : baseEnd_4094474 < baseStart_4094474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094478 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 4, 3]
def baseStart_4094478 : Nat := 118140960795 + 4094478 * 2 ^ 59
def prefixEnd_4094478 : Nat := 4983230072969 + 3 ^ 40 * 4094478 * 2
def baseEnd_4094478 : Nat := 1401623495506624379796563

theorem tailTrace_4094478 : CollatzResearch.WordTrace tailWord_4094478 prefixEnd_4094478 1401623495506624379796563 := by
  unfold tailWord_4094478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18667235157551620251861511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99558587506941974676594725 18667235157551620251861511)
  ·
    refine ⟨28000852736327430377792267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18667235157551620251861511 28000852736327430377792267)
    ·
      refine ⟨42001279104491145566688401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28000852736327430377792267 42001279104491145566688401)
      ·
        refine ⟨31500959328368359175016301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42001279104491145566688401 31500959328368359175016301)
        ·
          refine ⟨11812859748138134690631113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31500959328368359175016301 11812859748138134690631113)
          ·
            refine ⟨8859644811103601017973335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11812859748138134690631113 8859644811103601017973335)
            ·
              refine ⟨13289467216655401526960003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8859644811103601017973335 13289467216655401526960003)
              ·
                refine ⟨19934200824983102290440005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13289467216655401526960003 19934200824983102290440005)
                ·
                  refine ⟨3737662654684331679457501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19934200824983102290440005 3737662654684331679457501)
                  ·
                    refine ⟨1401623495506624379796563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3737662654684331679457501 1401623495506624379796563)
                    ·
                      rfl

theorem cell22_4094478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_4094478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094478 prefixEnd_4094478 := by exact prefixLift 4094478
  have htrace : WordTrace (prefixWord ++ tailWord_4094478) baseStart_4094478 baseEnd_4094478 := by
    simpa [prefixWord, tailWord_4094478, baseEnd_4094478] using wordTrace_append hprefix tailTrace_4094478
  have hstable : (prefixWord ++ tailWord_4094478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094478).length < 2 ^ (prefixWord ++ tailWord_4094478).sum := by decide
  have hdescent : baseEnd_4094478 < baseStart_4094478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094519 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 9]
def baseStart_4094519 : Nat := 118140960795 + 4094519 * 2 ^ 59
def prefixEnd_4094519 : Nat := 4983230072969 + 3 ^ 40 * 4094519 * 2
def baseEnd_4094519 : Nat := 467212510214837979840479

theorem tailTrace_4094519 : CollatzResearch.WordTrace tailWord_4094519 prefixEnd_4094519 467212510214837979840479 := by
  unfold tailWord_4094519
  simp only [CollatzResearch.WordTrace]
  refine ⟨149339376653264426017134611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99559584435509617344756407 149339376653264426017134611)
  ·
    refine ⟨224009064979896639025701917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149339376653264426017134611 224009064979896639025701917)
    ·
      refine ⟨84003399367461239634638219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224009064979896639025701917 84003399367461239634638219)
      ·
        refine ⟨126005099051191859451957329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84003399367461239634638219 126005099051191859451957329)
        ·
          refine ⟨94503824288393894588967997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126005099051191859451957329 94503824288393894588967997)
          ·
            refine ⟨35438934108147710470862999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94503824288393894588967997 35438934108147710470862999)
            ·
              refine ⟨53158401162221565706294499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35438934108147710470862999 53158401162221565706294499)
              ·
                refine ⟨79737601743332348559441749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53158401162221565706294499 79737601743332348559441749)
                ·
                  refine ⟨467212510214837979840479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79737601743332348559441749 467212510214837979840479)
                  ·
                    rfl

theorem cell22_4094519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 9].length) (baseStart_4094519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094519 prefixEnd_4094519 := by exact prefixLift 4094519
  have htrace : WordTrace (prefixWord ++ tailWord_4094519) baseStart_4094519 baseEnd_4094519 := by
    simpa [prefixWord, tailWord_4094519, baseEnd_4094519] using wordTrace_append hprefix tailTrace_4094519
  have hstable : (prefixWord ++ tailWord_4094519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094519).length < 2 ^ (prefixWord ++ tailWord_4094519).sum := by decide
  have hdescent : baseEnd_4094519 < baseStart_4094519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094647 : List Nat := [1, 1, 3, 1, 6, 2, 1, 2, 2, 3]
def baseStart_4094647 : Nat := 118140960795 + 4094647 * 2 ^ 59
def prefixEnd_4094647 : Nat := 4983230072969 + 3 ^ 40 * 4094647 * 2
def baseEnd_4094647 : Nat := 1401681347660364272321045

theorem tailTrace_4094647 : CollatzResearch.WordTrace tailWord_4094647 prefixEnd_4094647 1401681347660364272321045 := by
  unfold tailWord_4094647
  simp only [CollatzResearch.WordTrace]
  refine ⟨149344045196800703877794195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99562696797867135918529463 149344045196800703877794195)
  ·
    refine ⟨224016067795201055816691293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149344045196800703877794195 224016067795201055816691293)
    ·
      refine ⟨84006025423200395931259235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224016067795201055816691293 84006025423200395931259235)
      ·
        refine ⟨126009038134800593896888853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84006025423200395931259235 126009038134800593896888853)
        ·
          refine ⟨5906673662568777838916665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126009038134800593896888853 5906673662568777838916665)
          ·
            refine ⟨4430005246926583379187499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5906673662568777838916665 4430005246926583379187499)
            ·
              refine ⟨6645007870389875068781249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4430005246926583379187499 6645007870389875068781249)
              ·
                refine ⟨4983755902792406301585937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6645007870389875068781249 4983755902792406301585937)
                ·
                  refine ⟨3737816927094304726189453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4983755902792406301585937 3737816927094304726189453)
                  ·
                    refine ⟨1401681347660364272321045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3737816927094304726189453 1401681347660364272321045)
                    ·
                      rfl

theorem cell22_4094647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_4094647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094647 prefixEnd_4094647 := by exact prefixLift 4094647
  have htrace : WordTrace (prefixWord ++ tailWord_4094647) baseStart_4094647 baseEnd_4094647 := by
    simpa [prefixWord, tailWord_4094647, baseEnd_4094647] using wordTrace_append hprefix tailTrace_4094647
  have hstable : (prefixWord ++ tailWord_4094647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094647).length < 2 ^ (prefixWord ++ tailWord_4094647).sum := by decide
  have hdescent : baseEnd_4094647 < baseStart_4094647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094677 : List Nat := [1, 3, 2, 5, 1, 2, 2, 6]
def baseStart_4094677 : Nat := 118140960795 + 4094677 * 2 ^ 59
def prefixEnd_4094677 : Nat := 4983230072969 + 3 ^ 40 * 4094677 * 2
def baseEnd_4094677 : Nat := 155743513030383799341217

theorem tailTrace_4094677 : CollatzResearch.WordTrace tailWord_4094677 prefixEnd_4094677 155743513030383799341217 := by
  unfold tailWord_4094677
  simp only [CollatzResearch.WordTrace]
  refine ⟨149345139386692019001386285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99563426257794679334257523 149345139386692019001386285)
  ·
    refine ⟨56004427270009507125519857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149345139386692019001386285 56004427270009507125519857)
    ·
      refine ⟨42003320452507130344139893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56004427270009507125519857 42003320452507130344139893)
      ·
        refine ⟨3937811292422543469763115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42003320452507130344139893 3937811292422543469763115)
        ·
          refine ⟨5906716938633815204644673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3937811292422543469763115 5906716938633815204644673)
          ·
            refine ⟨4430037703975361403483505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5906716938633815204644673 4430037703975361403483505)
            ·
              refine ⟨3322528277981521052612629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4430037703975361403483505 3322528277981521052612629)
              ·
                refine ⟨155743513030383799341217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3322528277981521052612629 155743513030383799341217)
                ·
                  rfl

theorem cell22_4094677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 6].length) (baseStart_4094677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094677 prefixEnd_4094677 := by exact prefixLift 4094677
  have htrace : WordTrace (prefixWord ++ tailWord_4094677) baseStart_4094677 baseEnd_4094677 := by
    simpa [prefixWord, tailWord_4094677, baseEnd_4094677] using wordTrace_append hprefix tailTrace_4094677
  have hstable : (prefixWord ++ tailWord_4094677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094677).length < 2 ^ (prefixWord ++ tailWord_4094677).sum := by decide
  have hdescent : baseEnd_4094677 < baseStart_4094677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094692 : List Nat := [2, 3, 1, 1, 1, 4, 3, 3, 1, 3]
def baseStart_4094692 : Nat := 118140960795 + 4094692 * 2 ^ 59
def prefixEnd_4094692 : Nat := 4983230072969 + 3 ^ 40 * 4094692 * 2
def baseEnd_4094692 : Nat := 1401696752079999154945907

theorem tailTrace_4094692 : CollatzResearch.WordTrace tailWord_4094692 prefixEnd_4094692 1401696752079999154945907 := by
  unfold tailWord_4094692
  simp only [CollatzResearch.WordTrace]
  refine ⟨74672843240818838281591165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99563790987758451042121553 74672843240818838281591165)
  ·
    refine ⟨28002316215307064355596687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74672843240818838281591165 28002316215307064355596687)
    ·
      refine ⟨42003474322960596533395031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28002316215307064355596687 42003474322960596533395031)
      ·
        refine ⟨63005211484440894800092547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42003474322960596533395031 63005211484440894800092547)
        ·
          refine ⟨94507817226661342200138821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63005211484440894800092547 94507817226661342200138821)
          ·
            refine ⟨17720215729999001662526029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94507817226661342200138821 17720215729999001662526029)
            ·
              refine ⟨6645080898749625623447261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17720215729999001662526029 6645080898749625623447261)
              ·
                refine ⟨2491905337031109608792723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6645080898749625623447261 2491905337031109608792723)
                ·
                  refine ⟨3737858005546664413189085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491905337031109608792723 3737858005546664413189085)
                  ·
                    refine ⟨1401696752079999154945907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3737858005546664413189085 1401696752079999154945907)
                    ·
                      rfl

theorem cell22_4094692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_4094692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094692 prefixEnd_4094692 := by exact prefixLift 4094692
  have htrace : WordTrace (prefixWord ++ tailWord_4094692) baseStart_4094692 baseEnd_4094692 := by
    simpa [prefixWord, tailWord_4094692, baseEnd_4094692] using wordTrace_append hprefix tailTrace_4094692
  have hstable : (prefixWord ++ tailWord_4094692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094692).length < 2 ^ (prefixWord ++ tailWord_4094692).sum := by decide
  have hdescent : baseEnd_4094692 < baseStart_4094692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094722 : List Nat := [3, 4, 1, 1, 1, 2, 4, 1, 5]
def baseStart_4094722 : Nat := 118140960795 + 4094722 * 2 ^ 59
def prefixEnd_4094722 : Nat := 4983230072969 + 3 ^ 40 * 4094722 * 2
def baseEnd_4094722 : Nat := 467235673897696358898605

theorem tailTrace_4094722 : CollatzResearch.WordTrace tailWord_4094722 prefixEnd_4094722 467235673897696358898605 := by
  unfold tailWord_4094722
  simp only [CollatzResearch.WordTrace]
  refine ⟨37336695167882247921693605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99564520447685994457849613 37336695167882247921693605)
  ·
    refine ⟨7000630343977921485317551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37336695167882247921693605 7000630343977921485317551)
    ·
      refine ⟨10500945515966882227976327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7000630343977921485317551 10500945515966882227976327)
      ·
        refine ⟨15751418273950323341964491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10500945515966882227976327 15751418273950323341964491)
        ·
          refine ⟨23627127410925485012946737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15751418273950323341964491 23627127410925485012946737)
          ·
            refine ⟨17720345558194113759710053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23627127410925485012946737 17720345558194113759710053)
            ·
              refine ⟨3322564792161396329945635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17720345558194113759710053 3322564792161396329945635)
              ·
                refine ⟨4983847188242094494918453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3322564792161396329945635 4983847188242094494918453)
                ·
                  refine ⟨467235673897696358898605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4983847188242094494918453 467235673897696358898605)
                  ·
                    rfl

theorem cell22_4094722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_4094722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094722 prefixEnd_4094722 := by exact prefixLift 4094722
  have htrace : WordTrace (prefixWord ++ tailWord_4094722) baseStart_4094722 baseEnd_4094722 := by
    simpa [prefixWord, tailWord_4094722, baseEnd_4094722] using wordTrace_append hprefix tailTrace_4094722
  have hstable : (prefixWord ++ tailWord_4094722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094722).length < 2 ^ (prefixWord ++ tailWord_4094722).sum := by decide
  have hdescent : baseEnd_4094722 < baseStart_4094722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094748 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_4094748 : Nat := 118140960795 + 4094748 * 2 ^ 59
def prefixEnd_4094748 : Nat := 4983230072969 + 3 ^ 40 * 4094748 * 2
def baseEnd_4094748 : Nat := 1401715922024433675545735

theorem tailTrace_4094748 : CollatzResearch.WordTrace tailWord_4094748 prefixEnd_4094748 1401715922024433675545735 := by
  unfold tailWord_4094748
  simp only [CollatzResearch.WordTrace]
  refine ⟨74673864484717399063610449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99565152646289865418147265 74673864484717399063610449)
  ·
    refine ⟨56005398363538049297707837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74673864484717399063610449 56005398363538049297707837)
    ·
      refine ⟨21002024386326768486640439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56005398363538049297707837 21002024386326768486640439)
      ·
        refine ⟨31503036579490152729960659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21002024386326768486640439 31503036579490152729960659)
        ·
          refine ⟨47254554869235229094940989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31503036579490152729960659 47254554869235229094940989)
          ·
            refine ⟨17720458075963210910602871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47254554869235229094940989 17720458075963210910602871)
            ·
              refine ⟨26580687113944816365904307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17720458075963210910602871 26580687113944816365904307)
              ·
                refine ⟨39871030670917224548856461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26580687113944816365904307 39871030670917224548856461)
                ·
                  refine ⟨14951636501593959205821173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39871030670917224548856461 14951636501593959205821173)
                  ·
                    refine ⟨1401715922024433675545735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14951636501593959205821173 1401715922024433675545735)
                    ·
                      rfl

theorem cell22_4094748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_4094748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094748 prefixEnd_4094748 := by exact prefixLift 4094748
  have htrace : WordTrace (prefixWord ++ tailWord_4094748) baseStart_4094748 baseEnd_4094748 := by
    simpa [prefixWord, tailWord_4094748, baseEnd_4094748] using wordTrace_append hprefix tailTrace_4094748
  have hstable : (prefixWord ++ tailWord_4094748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094748).length < 2 ^ (prefixWord ++ tailWord_4094748).sum := by decide
  have hdescent : baseEnd_4094748 < baseStart_4094748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094752 : List Nat := [2, 1, 1, 5, 1, 3, 3, 1, 1, 4]
def baseStart_4094752 : Nat := 118140960795 + 4094752 * 2 ^ 59
def prefixEnd_4094752 : Nat := 4983230072969 + 3 ^ 40 * 4094752 * 2
def baseEnd_4094752 : Nat := 1401717291306178998445723

theorem tailTrace_4094752 : CollatzResearch.WordTrace tailWord_4094752 prefixEnd_4094752 1401717291306178998445723 := by
  unfold tailWord_4094752
  simp only [CollatzResearch.WordTrace]
  refine ⟨74673937430710153405183255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99565249907613537873577673 74673937430710153405183255)
  ·
    refine ⟨112010906146065230107774883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74673937430710153405183255 112010906146065230107774883)
    ·
      refine ⟨168016359219097845161662325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112010906146065230107774883 168016359219097845161662325)
      ·
        refine ⟨15751533676790422983905843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168016359219097845161662325 15751533676790422983905843)
        ·
          refine ⟨23627300515185634475858765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15751533676790422983905843 23627300515185634475858765)
          ·
            refine ⟨8860237693194612928447037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23627300515185634475858765 8860237693194612928447037)
            ·
              refine ⟨3322589134947979848167639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8860237693194612928447037 3322589134947979848167639)
              ·
                refine ⟨4983883702421969772251459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3322589134947979848167639 4983883702421969772251459)
                ·
                  refine ⟨7475825553632954658377189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4983883702421969772251459 7475825553632954658377189)
                  ·
                    refine ⟨1401717291306178998445723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7475825553632954658377189 1401717291306178998445723)
                    ·
                      rfl

theorem cell22_4094752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 1, 4].length) (baseStart_4094752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094752 prefixEnd_4094752 := by exact prefixLift 4094752
  have htrace : WordTrace (prefixWord ++ tailWord_4094752) baseStart_4094752 baseEnd_4094752 := by
    simpa [prefixWord, tailWord_4094752, baseEnd_4094752] using wordTrace_append hprefix tailTrace_4094752
  have hstable : (prefixWord ++ tailWord_4094752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094752).length < 2 ^ (prefixWord ++ tailWord_4094752).sum := by decide
  have hdescent : baseEnd_4094752 < baseStart_4094752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094782 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_4094782 : Nat := 118140960795 + 4094782 * 2 ^ 59
def prefixEnd_4094782 : Nat := 4983230072969 + 3 ^ 40 * 4094782 * 2
def baseEnd_4094782 : Nat := 1401727560919268920195631

theorem tailTrace_4094782 : CollatzResearch.WordTrace tailWord_4094782 prefixEnd_4094782 1401727560919268920195631 := by
  unfold tailWord_4094782
  simp only [CollatzResearch.WordTrace]
  refine ⟨18668621131413952741744825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99565979367541081289305733 18668621131413952741744825)
  ·
    refine ⟨14001465848560464556308619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18668621131413952741744825 14001465848560464556308619)
    ·
      refine ⟨21002198772840696834462929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14001465848560464556308619 21002198772840696834462929)
      ·
        refine ⟨15751649079630522625847197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21002198772840696834462929 15751649079630522625847197)
        ·
          refine ⟨5906868404861445984692699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15751649079630522625847197 5906868404861445984692699)
          ·
            refine ⟨8860302607292168977039049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5906868404861445984692699 8860302607292168977039049)
            ·
              refine ⟨6645226955469126732779287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8860302607292168977039049 6645226955469126732779287)
              ·
                refine ⟨9967840433203690099168931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6645226955469126732779287 9967840433203690099168931)
                ·
                  refine ⟨14951760649805535148753397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9967840433203690099168931 14951760649805535148753397)
                  ·
                    refine ⟨1401727560919268920195631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14951760649805535148753397 1401727560919268920195631)
                    ·
                      rfl

theorem cell22_4094782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_4094782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094782 prefixEnd_4094782 := by exact prefixLift 4094782
  have htrace : WordTrace (prefixWord ++ tailWord_4094782) baseStart_4094782 baseEnd_4094782 := by
    simpa [prefixWord, tailWord_4094782, baseEnd_4094782] using wordTrace_append hprefix tailTrace_4094782
  have hstable : (prefixWord ++ tailWord_4094782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094782).length < 2 ^ (prefixWord ++ tailWord_4094782).sum := by decide
  have hdescent : baseEnd_4094782 < baseStart_4094782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094797 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_4094797 : Nat := 118140960795 + 4094797 * 2 ^ 59
def prefixEnd_4094797 : Nat := 4983230072969 + 3 ^ 40 * 4094797 * 2
def baseEnd_4094797 : Nat := 1401732695725813881070585

theorem tailTrace_4094797 : CollatzResearch.WordTrace tailWord_4094797 prefixEnd_4094797 1401732695725813881070585 := by
  unfold tailWord_4094797
  simp only [CollatzResearch.WordTrace]
  refine ⟨149349516146257279495754645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99566344097504852997169763 149349516146257279495754645)
  ·
    refine ⟨7000758569355809976363499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 149349516146257279495754645 7000758569355809976363499)
    ·
      refine ⟨10501137854033714964545249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7000758569355809976363499 10501137854033714964545249)
      ·
        refine ⟨7875853390525286223408937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10501137854033714964545249 7875853390525286223408937)
        ·
          refine ⟨5906890042893964667556703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7875853390525286223408937 5906890042893964667556703)
          ·
            refine ⟨8860335064340947001335055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5906890042893964667556703 8860335064340947001335055)
            ·
              refine ⟨13290502596511420502002583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8860335064340947001335055 13290502596511420502002583)
              ·
                refine ⟨19935753894767130753003875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13290502596511420502002583 19935753894767130753003875)
                ·
                  refine ⟨29903630842150696129505813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19935753894767130753003875 29903630842150696129505813)
                  ·
                    refine ⟨1401732695725813881070585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29903630842150696129505813 1401732695725813881070585)
                    ·
                      rfl

theorem cell22_4094797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_4094797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094797 prefixEnd_4094797 := by exact prefixLift 4094797
  have htrace : WordTrace (prefixWord ++ tailWord_4094797) baseStart_4094797 baseEnd_4094797 := by
    simpa [prefixWord, tailWord_4094797, baseEnd_4094797] using wordTrace_append hprefix tailTrace_4094797
  have hstable : (prefixWord ++ tailWord_4094797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094797).length < 2 ^ (prefixWord ++ tailWord_4094797).sum := by decide
  have hdescent : baseEnd_4094797 < baseStart_4094797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094827 : List Nat := [1, 1, 1, 1, 2, 2, 6, 4, 1, 3]
def baseStart_4094827 : Nat := 118140960795 + 4094827 * 2 ^ 59
def prefixEnd_4094827 : Nat := 4983230072969 + 3 ^ 40 * 4094827 * 2
def baseEnd_4094827 : Nat := 1401742965338903802820493

theorem tailTrace_4094827 : CollatzResearch.WordTrace tailWord_4094827 prefixEnd_4094827 1401742965338903802820493 := by
  unfold tailWord_4094827
  simp only [CollatzResearch.WordTrace]
  refine ⟨149350610336148594619346735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99567073557432396412897823 149350610336148594619346735)
  ·
    refine ⟨224025915504222891929020103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149350610336148594619346735 224025915504222891929020103)
    ·
      refine ⟨336038873256334337893530155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224025915504222891929020103 336038873256334337893530155)
      ·
        refine ⟨504058309884501506840295233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336038873256334337893530155 504058309884501506840295233)
        ·
          refine ⟨378043732413376130130221425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504058309884501506840295233 378043732413376130130221425)
          ·
            refine ⟨283532799310032097597666069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378043732413376130130221425 283532799310032097597666069)
            ·
              refine ⟨13290599967657754574890597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 283532799310032097597666069 13290599967657754574890597)
              ·
                refine ⟨2491987493935828982791987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13290599967657754574890597 2491987493935828982791987)
                ·
                  refine ⟨3737981240903743474187981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491987493935828982791987 3737981240903743474187981)
                  ·
                    refine ⟨1401742965338903802820493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3737981240903743474187981 1401742965338903802820493)
                    ·
                      rfl

theorem cell22_4094827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 1, 3].length) (baseStart_4094827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094827 prefixEnd_4094827 := by exact prefixLift 4094827
  have htrace : WordTrace (prefixWord ++ tailWord_4094827) baseStart_4094827 baseEnd_4094827 := by
    simpa [prefixWord, tailWord_4094827, baseEnd_4094827] using wordTrace_append hprefix tailTrace_4094827
  have hstable : (prefixWord ++ tailWord_4094827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094827).length < 2 ^ (prefixWord ++ tailWord_4094827).sum := by decide
  have hdescent : baseEnd_4094827 < baseStart_4094827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094846 : List Nat := [4, 2, 3, 1, 3, 1, 2, 6]
def baseStart_4094846 : Nat := 118140960795 + 4094846 * 2 ^ 59
def prefixEnd_4094846 : Nat := 4983230072969 + 3 ^ 40 * 4094846 * 2
def baseEnd_4094846 : Nat := 155749941047466009621715

theorem tailTrace_4094846 : CollatzResearch.WordTrace tailWord_4094846 prefixEnd_4094846 155749941047466009621715 := by
  unfold tailWord_4094846
  simp only [CollatzResearch.WordTrace]
  refine ⟨18668912915384970108036049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99567535548719840576192261 18668912915384970108036049)
  ·
    refine ⟨14001684686538727581027037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18668912915384970108036049 14001684686538727581027037)
    ·
      refine ⟨5250631757452022842885139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14001684686538727581027037 5250631757452022842885139)
      ·
        refine ⟨7875947636178034264327709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250631757452022842885139 7875947636178034264327709)
        ·
          refine ⟨2953480363566762849122891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7875947636178034264327709 2953480363566762849122891)
          ·
            refine ⟨4430220545350144273684337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2953480363566762849122891 4430220545350144273684337)
            ·
              refine ⟨3322665409012608205263253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4430220545350144273684337 3322665409012608205263253)
              ·
                refine ⟨155749941047466009621715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3322665409012608205263253 155749941047466009621715)
                ·
                  rfl

theorem cell22_4094846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_4094846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094846 prefixEnd_4094846 := by exact prefixLift 4094846
  have htrace : WordTrace (prefixWord ++ tailWord_4094846) baseStart_4094846 baseEnd_4094846 := by
    simpa [prefixWord, tailWord_4094846, baseEnd_4094846] using wordTrace_append hprefix tailTrace_4094846
  have hstable : (prefixWord ++ tailWord_4094846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094846).length < 2 ^ (prefixWord ++ tailWord_4094846).sum := by decide
  have hdescent : baseEnd_4094846 < baseStart_4094846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094930 : List Nat := [3, 2, 2, 3, 1, 11]
def baseStart_4094930 : Nat := 118140960795 + 4094930 * 2 ^ 59
def prefixEnd_4094930 : Nat := 4983230072969 + 3 ^ 40 * 4094930 * 2
def baseEnd_4094930 : Nat := 17305904004245010709817

theorem tailTrace_4094930 : CollatzResearch.WordTrace tailWord_4094930 prefixEnd_4094930 17305904004245010709817 := by
  unfold tailWord_4094930
  simp only [CollatzResearch.WordTrace]
  refine ⟨37338591763693860802586561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99569578036516962140230829 37338591763693860802586561)
  ·
    refine ⟨28003943822770395601939921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37338591763693860802586561 28003943822770395601939921)
    ·
      refine ⟨21002957867077796701454941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28003943822770395601939921 21002957867077796701454941)
      ·
        refine ⟨7876109200154173763045603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21002957867077796701454941 7876109200154173763045603)
        ·
          refine ⟨11814163800231260644568405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7876109200154173763045603 11814163800231260644568405)
          ·
            refine ⟨17305904004245010709817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11814163800231260644568405 17305904004245010709817)
            ·
              rfl

theorem cell22_4094930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 11].length) (baseStart_4094930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094930 prefixEnd_4094930 := by exact prefixLift 4094930
  have htrace : WordTrace (prefixWord ++ tailWord_4094930) baseStart_4094930 baseEnd_4094930 := by
    simpa [prefixWord, tailWord_4094930, baseEnd_4094930] using wordTrace_append hprefix tailTrace_4094930
  have hstable : (prefixWord ++ tailWord_4094930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094930).length < 2 ^ (prefixWord ++ tailWord_4094930).sum := by decide
  have hdescent : baseEnd_4094930 < baseStart_4094930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094932 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_4094932 : Nat := 118140960795 + 4094932 * 2 ^ 59
def prefixEnd_4094932 : Nat := 4983230072969 + 3 ^ 40 * 4094932 * 2
def baseEnd_4094932 : Nat := 1401778908984718528945171

theorem tailTrace_4094932 : CollatzResearch.WordTrace tailWord_4094932 prefixEnd_4094932 1401778908984718528945171 := by
  unfold tailWord_4094932
  simp only [CollatzResearch.WordTrace]
  refine ⟨74677220000384098775959525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99569626667178798367946033 74677220000384098775959525)
  ·
    refine ⟨14001978750072018520492411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74677220000384098775959525 14001978750072018520492411)
    ·
      refine ⟨21002968125108027780738617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14001978750072018520492411 21002968125108027780738617)
      ·
        refine ⟨15752226093831020835553963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21002968125108027780738617 15752226093831020835553963)
        ·
          refine ⟨23628339140746531253330945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15752226093831020835553963 23628339140746531253330945)
          ·
            refine ⟨17721254355559898439998209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23628339140746531253330945 17721254355559898439998209)
            ·
              refine ⟨13290940766669923829998657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17721254355559898439998209 13290940766669923829998657)
              ·
                refine ⟨9968205575002442872498993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13290940766669923829998657 9968205575002442872498993)
                ·
                  refine ⟨7476154181251832154374245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9968205575002442872498993 7476154181251832154374245)
                  ·
                    refine ⟨1401778908984718528945171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7476154181251832154374245 1401778908984718528945171)
                    ·
                      rfl

theorem cell22_4094932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_4094932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4094932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4094932 prefixEnd_4094932 := by exact prefixLift 4094932
  have htrace : WordTrace (prefixWord ++ tailWord_4094932) baseStart_4094932 baseEnd_4094932 := by
    simpa [prefixWord, tailWord_4094932, baseEnd_4094932] using wordTrace_append hprefix tailTrace_4094932
  have hstable : (prefixWord ++ tailWord_4094932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094932).length < 2 ^ (prefixWord ++ tailWord_4094932).sum := by decide
  have hdescent : baseEnd_4094932 < baseStart_4094932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095009 : List Nat := [1, 2, 3, 2, 3, 2, 3, 1, 5]
def baseStart_4095009 : Nat := 118140960795 + 4095009 * 2 ^ 59
def prefixEnd_4095009 : Nat := 4983230072969 + 3 ^ 40 * 4095009 * 2
def baseEnd_4095009 : Nat := 467268422552771998256645

theorem tailTrace_4095009 : CollatzResearch.WordTrace tailWord_4095009 prefixEnd_4095009 467268422552771998256645 := by
  unfold tailWord_4095009
  simp only [CollatzResearch.WordTrace]
  refine ⟨149357248421489239702472081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99571498947659493134981387 149357248421489239702472081)
  ·
    refine ⟨112017936316116929776854061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149357248421489239702472081 112017936316116929776854061)
    ·
      refine ⟨42006726118543848666320273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112017936316116929776854061 42006726118543848666320273)
      ·
        refine ⟨31505044588907886499740205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42006726118543848666320273 31505044588907886499740205)
        ·
          refine ⟨11814391720840457437402577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31505044588907886499740205 11814391720840457437402577)
          ·
            refine ⟨8860793790630343078051933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11814391720840457437402577 8860793790630343078051933)
            ·
              refine ⟨3322797671486378654269475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8860793790630343078051933 3322797671486378654269475)
              ·
                refine ⟨4984196507229567981404213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3322797671486378654269475 4984196507229567981404213)
                ·
                  refine ⟨467268422552771998256645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4984196507229567981404213 467268422552771998256645)
                  ·
                    rfl

theorem cell22_4095009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 5].length) (baseStart_4095009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095009 prefixEnd_4095009 := by exact prefixLift 4095009
  have htrace : WordTrace (prefixWord ++ tailWord_4095009) baseStart_4095009 baseEnd_4095009 := by
    simpa [prefixWord, tailWord_4095009, baseEnd_4095009] using wordTrace_append hprefix tailTrace_4095009
  have hstable : (prefixWord ++ tailWord_4095009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095009).length < 2 ^ (prefixWord ++ tailWord_4095009).sum := by decide
  have hdescent : baseEnd_4095009 < baseStart_4095009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095020 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 6]
def baseStart_4095020 : Nat := 118140960795 + 4095020 * 2 ^ 59
def prefixEnd_4095020 : Nat := 4983230072969 + 3 ^ 40 * 4095020 * 2
def baseEnd_4095020 : Nat := 467269677727705210914967

theorem tailTrace_4095020 : CollatzResearch.WordTrace tailWord_4095020 prefixEnd_4095020 467269677727705210914967 := by
  unfold tailWord_4095020
  simp only [CollatzResearch.WordTrace]
  refine ⟨74678824812224694290561257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99571766416299592387415009 74678824812224694290561257)
  ·
    refine ⟨56009118609168520717920943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74678824812224694290561257 56009118609168520717920943)
    ·
      refine ⟨84013677913752781076881415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56009118609168520717920943 84013677913752781076881415)
      ·
        refine ⟨126020516870629171615322123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84013677913752781076881415 126020516870629171615322123)
        ·
          refine ⟨189030775305943757422983185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126020516870629171615322123 189030775305943757422983185)
          ·
            refine ⟨141773081479457818067237389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189030775305943757422983185 141773081479457818067237389)
            ·
              refine ⟨53164905554796681775214021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141773081479457818067237389 53164905554796681775214021)
              ·
                refine ⟨9968419791524377832852629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53164905554796681775214021 9968419791524377832852629)
                ·
                  refine ⟨467269677727705210914967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9968419791524377832852629 467269677727705210914967)
                  ·
                    rfl

theorem cell22_4095020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_4095020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095020 prefixEnd_4095020 := by exact prefixLift 4095020
  have htrace : WordTrace (prefixWord ++ tailWord_4095020) baseStart_4095020 baseEnd_4095020 := by
    simpa [prefixWord, tailWord_4095020, baseEnd_4095020] using wordTrace_append hprefix tailTrace_4095020
  have hstable : (prefixWord ++ tailWord_4095020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095020).length < 2 ^ (prefixWord ++ tailWord_4095020).sum := by decide
  have hdescent : baseEnd_4095020 < baseStart_4095020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095082 : List Nat := [3, 1, 3, 2, 2, 1, 2, 8]
def baseStart_4095082 : Nat := 118140960795 + 4095082 * 2 ^ 59
def prefixEnd_4095082 : Nat := 4983230072969 + 3 ^ 40 * 4095082 * 2
def baseEnd_4095082 : Nat := 155758917450018681966079

theorem tailTrace_4095082 : CollatzResearch.WordTrace tailWord_4095082 prefixEnd_4095082 155758917450018681966079 := by
  unfold tailWord_4095082
  simp only [CollatzResearch.WordTrace]
  refine ⟨37339977737556193292469875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99573273966816515446586333 37339977737556193292469875)
  ·
    refine ⟨56009966606334289938704813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37339977737556193292469875 56009966606334289938704813)
    ·
      refine ⟨21003737477375358727014305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56009966606334289938704813 21003737477375358727014305)
      ·
        refine ⟨15752803108031519045260729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21003737477375358727014305 15752803108031519045260729)
        ·
          refine ⟨11814602331023639283945547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15752803108031519045260729 11814602331023639283945547)
          ·
            refine ⟨17721903496535458925918321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11814602331023639283945547 17721903496535458925918321)
            ·
              refine ⟨13291427622401594194438741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17721903496535458925918321 13291427622401594194438741)
              ·
                refine ⟨155758917450018681966079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13291427622401594194438741 155758917450018681966079)
                ·
                  rfl

theorem cell22_4095082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 8].length) (baseStart_4095082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095082 prefixEnd_4095082 := by exact prefixLift 4095082
  have htrace : WordTrace (prefixWord ++ tailWord_4095082) baseStart_4095082 baseEnd_4095082 := by
    simpa [prefixWord, tailWord_4095082, baseEnd_4095082] using wordTrace_append hprefix tailTrace_4095082
  have hstable : (prefixWord ++ tailWord_4095082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095082).length < 2 ^ (prefixWord ++ tailWord_4095082).sum := by decide
  have hdescent : baseEnd_4095082 < baseStart_4095082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095114 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 3, 3]
def baseStart_4095114 : Nat := 118140960795 + 4095114 * 2 ^ 59
def prefixEnd_4095114 : Nat := 4983230072969 + 3 ^ 40 * 4095114 * 2
def baseEnd_4095114 : Nat := 1401841211304130720894613

theorem tailTrace_4095114 : CollatzResearch.WordTrace tailWord_4095114 prefixEnd_4095114 1401841211304130720894613 := by
  unfold tailWord_4095114
  simp only [CollatzResearch.WordTrace]
  refine ⟨37340269521527210658761099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99574052057405895090029597 37340269521527210658761099)
  ·
    refine ⟨56010404282290815988141649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37340269521527210658761099 56010404282290815988141649)
    ·
      refine ⟨42007803211718111991106237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56010404282290815988141649 42007803211718111991106237)
      ·
        refine ⟨15752926204394291996664839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42007803211718111991106237 15752926204394291996664839)
        ·
          refine ⟨23629389306591437994997259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15752926204394291996664839 23629389306591437994997259)
          ·
            refine ⟨35444083959887156992495889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23629389306591437994997259 35444083959887156992495889)
            ·
              refine ⟨26583062969915367744371917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35444083959887156992495889 26583062969915367744371917)
              ·
                refine ⟨9968648613718262904139469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26583062969915367744371917 9968648613718262904139469)
                ·
                  refine ⟨3738243230144348589052301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9968648613718262904139469 3738243230144348589052301)
                  ·
                    refine ⟨1401841211304130720894613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3738243230144348589052301 1401841211304130720894613)
                    ·
                      rfl

theorem cell22_4095114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_4095114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095114 prefixEnd_4095114 := by exact prefixLift 4095114
  have htrace : WordTrace (prefixWord ++ tailWord_4095114) baseStart_4095114 baseEnd_4095114 := by
    simpa [prefixWord, tailWord_4095114, baseEnd_4095114] using wordTrace_append hprefix tailTrace_4095114
  have hstable : (prefixWord ++ tailWord_4095114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095114).length < 2 ^ (prefixWord ++ tailWord_4095114).sum := by decide
  have hdescent : baseEnd_4095114 < baseStart_4095114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095189 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 6]
def baseStart_4095189 : Nat := 118140960795 + 4095189 * 2 ^ 59
def prefixEnd_4095189 : Nat := 4983230072969 + 3 ^ 40 * 4095189 * 2
def baseEnd_4095189 : Nat := 467288961778951841756461

theorem tailTrace_4095189 : CollatzResearch.WordTrace tailWord_4095189 prefixEnd_4095189 467288961778951841756461 := by
  unfold tailWord_4095189
  simp only [CollatzResearch.WordTrace]
  refine ⟨149363813560837130444024621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99575875707224753629349747 149363813560837130444024621)
  ·
    refine ⟨56011430085313923916509233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149363813560837130444024621 56011430085313923916509233)
    ·
      refine ⟨42008572563985442937381925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56011430085313923916509233 42008572563985442937381925)
      ·
        refine ⟨7876607355747270550759111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42008572563985442937381925 7876607355747270550759111)
        ·
          refine ⟨11814911033620905826138667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7876607355747270550759111 11814911033620905826138667)
          ·
            refine ⟨17722366550431358739208001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11814911033620905826138667 17722366550431358739208001)
            ·
              refine ⟨13291774912823519054406001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17722366550431358739208001 13291774912823519054406001)
              ·
                refine ⟨9968831184617639290804501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13291774912823519054406001 9968831184617639290804501)
                ·
                  refine ⟨467288961778951841756461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9968831184617639290804501 467288961778951841756461)
                  ·
                    rfl

theorem cell22_4095189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_4095189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095189 prefixEnd_4095189 := by exact prefixLift 4095189
  have htrace : WordTrace (prefixWord ++ tailWord_4095189) baseStart_4095189 baseEnd_4095189 := by
    simpa [prefixWord, tailWord_4095189, baseEnd_4095189] using wordTrace_append hprefix tailTrace_4095189
  have hstable : (prefixWord ++ tailWord_4095189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095189).length < 2 ^ (prefixWord ++ tailWord_4095189).sum := by decide
  have hdescent : baseEnd_4095189 < baseStart_4095189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095204 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 4, 3]
def baseStart_4095204 : Nat := 118140960795 + 4095204 * 2 ^ 59
def prefixEnd_4095204 : Nat := 4983230072969 + 3 ^ 40 * 4095204 * 2
def baseEnd_4095204 : Nat := 1401872020143400486144337

theorem tailTrace_4095204 : CollatzResearch.WordTrace tailWord_4095204 prefixEnd_4095204 1401872020143400486144337 := by
  unfold tailWord_4095204
  simp only [CollatzResearch.WordTrace]
  refine ⟨74682180327891394002910333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99576240437188525337213777 74682180327891394002910333)
  ·
    refine ⟨28005817622959272751091375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74682180327891394002910333 28005817622959272751091375)
    ·
      refine ⟨42008726434438909126637063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28005817622959272751091375 42008726434438909126637063)
      ·
        refine ⟨63013089651658363689955595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42008726434438909126637063 63013089651658363689955595)
        ·
          refine ⟨94519634477487545534933393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63013089651658363689955595 94519634477487545534933393)
          ·
            refine ⟨70889725858115659151200045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94519634477487545534933393 70889725858115659151200045)
            ·
              refine ⟨26583647196793372181700017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70889725858115659151200045 26583647196793372181700017)
              ·
                refine ⟨19937735397595029136275013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26583647196793372181700017 19937735397595029136275013)
                ·
                  refine ⟨3738325387049067963051565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19937735397595029136275013 3738325387049067963051565)
                  ·
                    refine ⟨1401872020143400486144337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3738325387049067963051565 1401872020143400486144337)
                    ·
                      rfl

theorem cell22_4095204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_4095204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095204 prefixEnd_4095204 := by exact prefixLift 4095204
  have htrace : WordTrace (prefixWord ++ tailWord_4095204) baseStart_4095204 baseEnd_4095204 := by
    simpa [prefixWord, tailWord_4095204, baseEnd_4095204] using wordTrace_append hprefix tailTrace_4095204
  have hstable : (prefixWord ++ tailWord_4095204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095204).length < 2 ^ (prefixWord ++ tailWord_4095204).sum := by decide
  have hdescent : baseEnd_4095204 < baseStart_4095204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095219 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 2, 4]
def baseStart_4095219 : Nat := 118140960795 + 4095219 * 2 ^ 59
def prefixEnd_4095219 : Nat := 4983230072969 + 3 ^ 40 * 4095219 * 2
def baseEnd_4095219 : Nat := 1401877154949945447019291

theorem tailTrace_4095219 : CollatzResearch.WordTrace tailWord_4095219 prefixEnd_4095219 1401877154949945447019291 := by
  unfold tailWord_4095219
  simp only [CollatzResearch.WordTrace]
  refine ⟨149364907750728445567616711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99576605167152297045077807 149364907750728445567616711)
  ·
    refine ⟨224047361626092668351425067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149364907750728445567616711 224047361626092668351425067)
    ·
      refine ⟨336071042439139002527137601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224047361626092668351425067 336071042439139002527137601)
      ·
        refine ⟨252053281829354251895353201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336071042439139002527137601 252053281829354251895353201)
        ·
          refine ⟨189039961372015688921514901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252053281829354251895353201 189039961372015688921514901)
          ·
            refine ⟨8861248189313235418196011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 189039961372015688921514901 8861248189313235418196011)
            ·
              refine ⟨13291872283969853127294017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8861248189313235418196011 13291872283969853127294017)
              ·
                refine ⟨9968904212977389845470513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13291872283969853127294017 9968904212977389845470513)
                ·
                  refine ⟨7476678159733042384102885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9968904212977389845470513 7476678159733042384102885)
                  ·
                    refine ⟨1401877154949945447019291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7476678159733042384102885 1401877154949945447019291)
                    ·
                      rfl

theorem cell22_4095219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 4].length) (baseStart_4095219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095219 prefixEnd_4095219 := by exact prefixLift 4095219
  have htrace : WordTrace (prefixWord ++ tailWord_4095219) baseStart_4095219 baseEnd_4095219 := by
    simpa [prefixWord, tailWord_4095219, baseEnd_4095219] using wordTrace_append hprefix tailTrace_4095219
  have hstable : (prefixWord ++ tailWord_4095219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095219).length < 2 ^ (prefixWord ++ tailWord_4095219).sum := by decide
  have hdescent : baseEnd_4095219 < baseStart_4095219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095249 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 5, 3]
def baseStart_4095249 : Nat := 118140960795 + 4095249 * 2 ^ 59
def prefixEnd_4095249 : Nat := 4983230072969 + 3 ^ 40 * 4095249 * 2
def baseEnd_4095249 : Nat := 1401887424563035368769199

theorem tailTrace_4095249 : CollatzResearch.WordTrace tailWord_4095249 prefixEnd_4095249 1401887424563035368769199 := by
  unfold tailWord_4095249
  simp only [CollatzResearch.WordTrace]
  refine ⟨149366001940619760691208801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99577334627079840460805867 149366001940619760691208801)
  ·
    refine ⟨112024501455464820518406601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149366001940619760691208801 112024501455464820518406601)
    ·
      refine ⟨84018376091598615388804951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112024501455464820518406601 84018376091598615388804951)
      ·
        refine ⟨126027564137397923083207427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84018376091598615388804951 126027564137397923083207427)
        ·
          refine ⟨189041346206096884624811141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126027564137397923083207427 189041346206096884624811141)
          ·
            refine ⟨35445252413643165867152089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189041346206096884624811141 35445252413643165867152089)
            ·
              refine ⟨26583939310232374400364067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35445252413643165867152089 26583939310232374400364067)
              ·
                refine ⟨39875908965348561600546101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26583939310232374400364067 39875908965348561600546101)
                ·
                  refine ⟨3738366465501427650051197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39875908965348561600546101 3738366465501427650051197)
                  ·
                    refine ⟨1401887424563035368769199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3738366465501427650051197 1401887424563035368769199)
                    ·
                      rfl

theorem cell22_4095249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_4095249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095249 prefixEnd_4095249 := by exact prefixLift 4095249
  have htrace : WordTrace (prefixWord ++ tailWord_4095249) baseStart_4095249 baseEnd_4095249 := by
    simpa [prefixWord, tailWord_4095249, baseEnd_4095249] using wordTrace_append hprefix tailTrace_4095249
  have hstable : (prefixWord ++ tailWord_4095249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095249).length < 2 ^ (prefixWord ++ tailWord_4095249).sum := by decide
  have hdescent : baseEnd_4095249 < baseStart_4095249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095283 : List Nat := [1, 1, 1, 2, 5, 3, 1, 4, 1, 3]
def baseStart_4095283 : Nat := 118140960795 + 4095283 * 2 ^ 59
def prefixEnd_4095283 : Nat := 4983230072969 + 3 ^ 40 * 4095283 * 2
def baseEnd_4095283 : Nat := 1401899063457870613419095

theorem tailTrace_4095283 : CollatzResearch.WordTrace tailWord_4095283 prefixEnd_4095283 1401899063457870613419095 := by
  unfold tailWord_4095283
  simp only [CollatzResearch.WordTrace]
  refine ⟨149367242022496584497946503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99578161348331056331964335 149367242022496584497946503)
  ·
    refine ⟨224050863033744876746919755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149367242022496584497946503 224050863033744876746919755)
    ·
      refine ⟨336076294550617315120379633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224050863033744876746919755 336076294550617315120379633)
      ·
        refine ⟨252057220912962986340284725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336076294550617315120379633 252057220912962986340284725)
        ·
          refine ⟨23630364460590279969401693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252057220912962986340284725 23630364460590279969401693)
          ·
            refine ⟨8861386672721354988525635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23630364460590279969401693 8861386672721354988525635)
            ·
              refine ⟨13292080009082032482788453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8861386672721354988525635 13292080009082032482788453)
              ·
                refine ⟨2492265001702881090522835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13292080009082032482788453 2492265001702881090522835)
                ·
                  refine ⟨3738397502554321635784253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492265001702881090522835 3738397502554321635784253)
                  ·
                    refine ⟨1401899063457870613419095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3738397502554321635784253 1401899063457870613419095)
                    ·
                      rfl

theorem cell22_4095283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 1, 3].length) (baseStart_4095283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095283 prefixEnd_4095283 := by exact prefixLift 4095283
  have htrace : WordTrace (prefixWord ++ tailWord_4095283) baseStart_4095283 baseEnd_4095283 := by
    simpa [prefixWord, tailWord_4095283, baseEnd_4095283] using wordTrace_append hprefix tailTrace_4095283
  have hstable : (prefixWord ++ tailWord_4095283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095283).length < 2 ^ (prefixWord ++ tailWord_4095283).sum := by decide
  have hdescent : baseEnd_4095283 < baseStart_4095283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095341 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 6]
def baseStart_4095341 : Nat := 118140960795 + 4095341 * 2 ^ 59
def prefixEnd_4095341 : Nat := 4983230072969 + 3 ^ 40 * 4095341 * 2
def baseEnd_4095341 : Nat := 467306306014392598489639

theorem tailTrace_4095341 : CollatzResearch.WordTrace tailWord_4095341 prefixEnd_4095341 467306306014392598489639 := by
  unfold tailWord_4095341
  simp only [CollatzResearch.WordTrace]
  refine ⟨149369357456286460403557877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99579571637524306935705251 149369357456286460403557877)
  ·
    refine ⟨14003377261526855662833551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149369357456286460403557877 14003377261526855662833551)
    ·
      refine ⟨21005065892290283494250327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14003377261526855662833551 21005065892290283494250327)
      ·
        refine ⟨31507598838435425241375491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21005065892290283494250327 31507598838435425241375491)
        ·
          refine ⟨47261398257653137862063237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31507598838435425241375491 47261398257653137862063237)
          ·
            refine ⟨8861512173309963349136857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47261398257653137862063237 8861512173309963349136857)
            ·
              refine ⟨6646134129982472511852643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8861512173309963349136857 6646134129982472511852643)
              ·
                refine ⟨9969201194973708767778965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6646134129982472511852643 9969201194973708767778965)
                ·
                  refine ⟨467306306014392598489639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9969201194973708767778965 467306306014392598489639)
                  ·
                    rfl

theorem cell22_4095341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_4095341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095341 prefixEnd_4095341 := by exact prefixLift 4095341
  have htrace : WordTrace (prefixWord ++ tailWord_4095341) baseStart_4095341 baseEnd_4095341 := by
    simpa [prefixWord, tailWord_4095341, baseEnd_4095341] using wordTrace_append hprefix tailTrace_4095341
  have hstable : (prefixWord ++ tailWord_4095341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095341).length < 2 ^ (prefixWord ++ tailWord_4095341).sum := by decide
  have hdescent : baseEnd_4095341 < baseStart_4095341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095354 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 4, 4]
def baseStart_4095354 : Nat := 118140960795 + 4095354 * 2 ^ 59
def prefixEnd_4095354 : Nat := 4983230072969 + 3 ^ 40 * 4095354 * 2
def baseEnd_4095354 : Nat := 1401923368208850094893877

theorem tailTrace_4095354 : CollatzResearch.WordTrace tailWord_4095354 prefixEnd_4095354 1401923368208850094893877 := by
  unfold tailWord_4095354
  simp only [CollatzResearch.WordTrace]
  refine ⟨37342457901309840905945279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99579887736826242415854077 37342457901309840905945279)
  ·
    refine ⟨56013686851964761358917919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37342457901309840905945279 56013686851964761358917919)
    ·
      refine ⟨84020530277947142038376879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56013686851964761358917919 84020530277947142038376879)
      ·
        refine ⟨126030795416920713057565319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84020530277947142038376879 126030795416920713057565319)
        ·
          refine ⟨189046193125381069586347979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126030795416920713057565319 189046193125381069586347979)
          ·
            refine ⟨283569289688071604379521969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189046193125381069586347979 283569289688071604379521969)
            ·
              refine ⟨212676967266053703284641477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283569289688071604379521969 212676967266053703284641477)
              ·
                refine ⟨39876931362385069365870277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212676967266053703284641477 39876931362385069365870277)
                ·
                  refine ⟨7476924630447200506100677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39876931362385069365870277 7476924630447200506100677)
                  ·
                    refine ⟨1401923368208850094893877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7476924630447200506100677 1401923368208850094893877)
                    ·
                      rfl

theorem cell22_4095354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_4095354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095354 prefixEnd_4095354 := by exact prefixLift 4095354
  have htrace : WordTrace (prefixWord ++ tailWord_4095354) baseStart_4095354 baseEnd_4095354 := by
    simpa [prefixWord, tailWord_4095354, baseEnd_4095354] using wordTrace_append hprefix tailTrace_4095354
  have hstable : (prefixWord ++ tailWord_4095354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095354).length < 2 ^ (prefixWord ++ tailWord_4095354).sum := by decide
  have hdescent : baseEnd_4095354 < baseStart_4095354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095478 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_4095478 : Nat := 118140960795 + 4095478 * 2 ^ 59
def prefixEnd_4095478 : Nat := 4983230072969 + 3 ^ 40 * 4095478 * 2
def baseEnd_4095478 : Nat := 1401965815942955104793497

theorem tailTrace_4095478 : CollatzResearch.WordTrace tailWord_4095478 prefixEnd_4095478 1401965815942955104793497 := by
  unfold tailWord_4095478
  simp only [CollatzResearch.WordTrace]
  refine ⟨9335897141049383300080943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99582902837860088534196725 9335897141049383300080943)
  ·
    refine ⟨14003845711574074950121415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9335897141049383300080943 14003845711574074950121415)
    ·
      refine ⟨21005768567361112425182123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14003845711574074950121415 21005768567361112425182123)
      ·
        refine ⟨31508652851041668637773185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21005768567361112425182123 31508652851041668637773185)
        ·
          refine ⟨23631489638281251478329889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31508652851041668637773185 23631489638281251478329889)
          ·
            refine ⟨17723617228710938608747417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23631489638281251478329889 17723617228710938608747417)
            ·
              refine ⟨13292712921533203956560563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17723617228710938608747417 13292712921533203956560563)
              ·
                refine ⟨19939069382299805934840845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13292712921533203956560563 19939069382299805934840845)
                ·
                  refine ⟨7477151018362427225565317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19939069382299805934840845 7477151018362427225565317)
                  ·
                    refine ⟨1401965815942955104793497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7477151018362427225565317 1401965815942955104793497)
                    ·
                      rfl

theorem cell22_4095478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_4095478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095478 prefixEnd_4095478 := by exact prefixLift 4095478
  have htrace : WordTrace (prefixWord ++ tailWord_4095478) baseStart_4095478 baseEnd_4095478 := by
    simpa [prefixWord, tailWord_4095478, baseEnd_4095478] using wordTrace_append hprefix tailTrace_4095478
  have hstable : (prefixWord ++ tailWord_4095478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095478).length < 2 ^ (prefixWord ++ tailWord_4095478).sum := by decide
  have hdescent : baseEnd_4095478 < baseStart_4095478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095495 : List Nat := [1, 1, 4, 3, 2, 1, 4, 1, 1, 4]
def baseStart_4095495 : Nat := 118140960795 + 4095495 * 2 ^ 59
def prefixEnd_4095495 : Nat := 4983230072969 + 3 ^ 40 * 4095495 * 2
def baseEnd_4095495 : Nat := 1401971635390372727118445

theorem tailTrace_4095495 : CollatzResearch.WordTrace tailWord_4095495 prefixEnd_4095495 1401971635390372727118445 := by
  unfold tailWord_4095495
  simp only [CollatzResearch.WordTrace]
  refine ⟨149374974297728544704663939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99583316198485696469775959 149374974297728544704663939)
  ·
    refine ⟨224062461446592817056995909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149374974297728544704663939 224062461446592817056995909)
    ·
      refine ⟨42011711521236153198186733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224062461446592817056995909 42011711521236153198186733)
      ·
        refine ⟨15754391820463557449320025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42011711521236153198186733 15754391820463557449320025)
        ·
          refine ⟨11815793865347668086990019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15754391820463557449320025 11815793865347668086990019)
          ·
            refine ⟨17723690798021502130485029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11815793865347668086990019 17723690798021502130485029)
            ·
              refine ⟨3323192024629031649465943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17723690798021502130485029 3323192024629031649465943)
              ·
                refine ⟨4984788036943547474198915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3323192024629031649465943 4984788036943547474198915)
                ·
                  refine ⟨7477182055415321211298373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4984788036943547474198915 7477182055415321211298373)
                  ·
                    refine ⟨1401971635390372727118445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7477182055415321211298373 1401971635390372727118445)
                    ·
                      rfl

theorem cell22_4095495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_4095495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095495 prefixEnd_4095495 := by exact prefixLift 4095495
  have htrace : WordTrace (prefixWord ++ tailWord_4095495) baseStart_4095495 baseEnd_4095495 := by
    simpa [prefixWord, tailWord_4095495, baseEnd_4095495] using wordTrace_append hprefix tailTrace_4095495
  have hstable : (prefixWord ++ tailWord_4095495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095495).length < 2 ^ (prefixWord ++ tailWord_4095495).sum := by decide
  have hdescent : baseEnd_4095495 < baseStart_4095495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095570 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 3, 3]
def baseStart_4095570 : Nat := 118140960795 + 4095570 * 2 ^ 59
def prefixEnd_4095570 : Nat := 4983230072969 + 3 ^ 40 * 4095570 * 2
def baseEnd_4095570 : Nat := 1401997309423097531493215

theorem tailTrace_4095570 : CollatzResearch.WordTrace tailWord_4095570 prefixEnd_4095570 1401997309423097531493215 := by
  unfold tailWord_4095570
  simp only [CollatzResearch.WordTrace]
  refine ⟨37344427443114208128411041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99585139848304555009096109 37344427443114208128411041)
  ·
    refine ⟨28008320582335656096308281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37344427443114208128411041 28008320582335656096308281)
    ·
      refine ⟨21006240436751742072231211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28008320582335656096308281 21006240436751742072231211)
      ·
        refine ⟨31509360655127613108346817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21006240436751742072231211 31509360655127613108346817)
        ·
          refine ⟨23632020491345709831260113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31509360655127613108346817 23632020491345709831260113)
          ·
            refine ⟨17724015368509282373445085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23632020491345709831260113 17724015368509282373445085)
            ·
              refine ⟨6646505763190980890041907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17724015368509282373445085 6646505763190980890041907)
              ·
                refine ⟨9969758644786471335062861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6646505763190980890041907 9969758644786471335062861)
                ·
                  refine ⟨3738659491794926750648573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9969758644786471335062861 3738659491794926750648573)
                  ·
                    refine ⟨1401997309423097531493215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3738659491794926750648573 1401997309423097531493215)
                    ·
                      rfl

theorem cell22_4095570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_4095570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095570 prefixEnd_4095570 := by exact prefixLift 4095570
  have htrace : WordTrace (prefixWord ++ tailWord_4095570) baseStart_4095570 baseEnd_4095570 := by
    simpa [prefixWord, tailWord_4095570, baseEnd_4095570] using wordTrace_append hprefix tailTrace_4095570
  have hstable : (prefixWord ++ tailWord_4095570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095570).length < 2 ^ (prefixWord ++ tailWord_4095570).sum := by decide
  have hdescent : baseEnd_4095570 < baseStart_4095570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095705 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 3, 3]
def baseStart_4095705 : Nat := 118140960795 + 4095705 * 2 ^ 59
def prefixEnd_4095705 : Nat := 4983230072969 + 3 ^ 40 * 4095705 * 2
def baseEnd_4095705 : Nat := 1402043522682002179367801

theorem tailTrace_4095705 : CollatzResearch.WordTrace tailWord_4095705 prefixEnd_4095705 1402043522682002179367801 := by
  unfold tailWord_4095705
  simp only [CollatzResearch.WordTrace]
  refine ⟨149382633626967750569808569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99588422417978500379872379 149382633626967750569808569)
  ·
    refine ⟨112036975220225812927356427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149382633626967750569808569 112036975220225812927356427)
    ·
      refine ⟨168055462830338719391034641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112036975220225812927356427 168055462830338719391034641)
      ·
        refine ⟨126041597122754039543275981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168055462830338719391034641 126041597122754039543275981)
        ·
          refine ⟨47265598921032764828728493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126041597122754039543275981 47265598921032764828728493)
          ·
            refine ⟨17724599595387286810773185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47265598921032764828728493 17724599595387286810773185)
            ·
              refine ⟨13293449696540465108079889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17724599595387286810773185 13293449696540465108079889)
              ·
                refine ⟨9970087272405348831059917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13293449696540465108079889 9970087272405348831059917)
                ·
                  refine ⟨3738782727152005811647469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9970087272405348831059917 3738782727152005811647469)
                  ·
                    refine ⟨1402043522682002179367801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3738782727152005811647469 1402043522682002179367801)
                    ·
                      rfl

theorem cell22_4095705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 3].length) (baseStart_4095705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095705 prefixEnd_4095705 := by exact prefixLift 4095705
  have htrace : WordTrace (prefixWord ++ tailWord_4095705) baseStart_4095705 baseEnd_4095705 := by
    simpa [prefixWord, tailWord_4095705, baseEnd_4095705] using wordTrace_append hprefix tailTrace_4095705
  have hstable : (prefixWord ++ tailWord_4095705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095705).length < 2 ^ (prefixWord ++ tailWord_4095705).sum := by decide
  have hdescent : baseEnd_4095705 < baseStart_4095705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095765 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 3, 4]
def baseStart_4095765 : Nat := 118140960795 + 4095765 * 2 ^ 59
def prefixEnd_4095765 : Nat := 4983230072969 + 3 ^ 40 * 4095765 * 2
def baseEnd_4095765 : Nat := 1402064061908182022867617

theorem tailTrace_4095765 : CollatzResearch.WordTrace tailWord_4095765 prefixEnd_4095765 1402064061908182022867617 := by
  unfold tailWord_4095765
  simp only [CollatzResearch.WordTrace]
  refine ⟨149384822006750380816992749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99589881337833587211328499 149384822006750380816992749)
  ·
    refine ⟨56019308252531392806372281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149384822006750380816992749 56019308252531392806372281)
    ·
      refine ⟨42014481189398544604779211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56019308252531392806372281 42014481189398544604779211)
      ·
        refine ⟨63021721784097816907168817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42014481189398544604779211 63021721784097816907168817)
        ·
          refine ⟨47266291338073362680376613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63021721784097816907168817 47266291338073362680376613)
          ·
            refine ⟨8862429625888755502570615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47266291338073362680376613 8862429625888755502570615)
            ·
              refine ⟨13293644438833133253855923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8862429625888755502570615 13293644438833133253855923)
              ·
                refine ⟨19940466658249699880783885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13293644438833133253855923 19940466658249699880783885)
                ·
                  refine ⟨7477674996843637455293957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19940466658249699880783885 7477674996843637455293957)
                  ·
                    refine ⟨1402064061908182022867617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7477674996843637455293957 1402064061908182022867617)
                    ·
                      rfl

theorem cell22_4095765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_4095765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095765 prefixEnd_4095765 := by exact prefixLift 4095765
  have htrace : WordTrace (prefixWord ++ tailWord_4095765) baseStart_4095765 baseEnd_4095765 := by
    simpa [prefixWord, tailWord_4095765, baseEnd_4095765] using wordTrace_append hprefix tailTrace_4095765
  have hstable : (prefixWord ++ tailWord_4095765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095765).length < 2 ^ (prefixWord ++ tailWord_4095765).sum := by decide
  have hdescent : baseEnd_4095765 < baseStart_4095765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095790 : List Nat := [4, 1, 3, 2, 3, 1, 2, 2, 1, 3]
def baseStart_4095790 : Nat := 118140960795 + 4095790 * 2 ^ 59
def prefixEnd_4095790 : Nat := 4983230072969 + 3 ^ 40 * 4095790 * 2
def baseEnd_4095790 : Nat := 1402072619919090290992541

theorem tailTrace_4095790 : CollatzResearch.WordTrace tailWord_4095790 prefixEnd_4095790 1402072619919090290992541 := by
  unfold tailWord_4095790
  simp only [CollatzResearch.WordTrace]
  refine ⟨18673216728957476260831603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99590489221106540057768549 18673216728957476260831603)
  ·
    refine ⟨28009825093436214391247405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18673216728957476260831603 28009825093436214391247405)
    ·
      refine ⟨10503684410038580396717777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28009825093436214391247405 10503684410038580396717777)
      ·
        refine ⟨7877763307528935297538333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10503684410038580396717777 7877763307528935297538333)
        ·
          refine ⟨2954161240323350736576875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7877763307528935297538333 2954161240323350736576875)
          ·
            refine ⟨4431241860485026104865313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954161240323350736576875 4431241860485026104865313)
            ·
              refine ⟨3323431395363769578648985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4431241860485026104865313 3323431395363769578648985)
              ·
                refine ⟨2492573546522827183986739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3323431395363769578648985 2492573546522827183986739)
                ·
                  refine ⟨3738860319784240775980109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492573546522827183986739 3738860319784240775980109)
                  ·
                    refine ⟨1402072619919090290992541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3738860319784240775980109 1402072619919090290992541)
                    ·
                      rfl

theorem cell22_4095790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_4095790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095790 prefixEnd_4095790 := by exact prefixLift 4095790
  have htrace : WordTrace (prefixWord ++ tailWord_4095790) baseStart_4095790 baseEnd_4095790 := by
    simpa [prefixWord, tailWord_4095790, baseEnd_4095790] using wordTrace_append hprefix tailTrace_4095790
  have hstable : (prefixWord ++ tailWord_4095790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095790).length < 2 ^ (prefixWord ++ tailWord_4095790).sum := by decide
  have hdescent : baseEnd_4095790 < baseStart_4095790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095814 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_4095814 : Nat := 118140960795 + 4095814 * 2 ^ 59
def prefixEnd_4095814 : Nat := 4983230072969 + 3 ^ 40 * 4095814 * 2
def baseEnd_4095814 : Nat := 467360278536520742797489

theorem tailTrace_4095814 : CollatzResearch.WordTrace tailWord_4095814 prefixEnd_4095814 467360278536520742797489 := by
  unfold tailWord_4095814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4668331536986651943297703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99591072789048574790350997 4668331536986651943297703)
  ·
    refine ⟨7002497305479977914946555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4668331536986651943297703 7002497305479977914946555)
    ·
      refine ⟨10503745958219966872419833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7002497305479977914946555 10503745958219966872419833)
      ·
        refine ⟨7877809468664975154314875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10503745958219966872419833 7877809468664975154314875)
        ·
          refine ⟨11816714202997462731472313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7877809468664975154314875 11816714202997462731472313)
          ·
            refine ⟨8862535652248097048604235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11816714202997462731472313 8862535652248097048604235)
            ·
              refine ⟨13293803478372145572906353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8862535652248097048604235 13293803478372145572906353)
              ·
                refine ⟨9970352608779109179679765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13293803478372145572906353 9970352608779109179679765)
                ·
                  refine ⟨467360278536520742797489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9970352608779109179679765 467360278536520742797489)
                  ·
                    rfl

theorem cell22_4095814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_4095814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095814 prefixEnd_4095814 := by exact prefixLift 4095814
  have htrace : WordTrace (prefixWord ++ tailWord_4095814) baseStart_4095814 baseEnd_4095814 := by
    simpa [prefixWord, tailWord_4095814, baseEnd_4095814] using wordTrace_append hprefix tailTrace_4095814
  have hstable : (prefixWord ++ tailWord_4095814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095814).length < 2 ^ (prefixWord ++ tailWord_4095814).sum := by decide
  have hdescent : baseEnd_4095814 < baseStart_4095814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095857 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 3, 3]
def baseStart_4095857 : Nat := 118140960795 + 4095857 * 2 ^ 59
def prefixEnd_4095857 : Nat := 4983230072969 + 3 ^ 40 * 4095857 * 2
def baseEnd_4095857 : Nat := 1402095555388324449567335

theorem tailTrace_4095857 : CollatzResearch.WordTrace tailWord_4095857 prefixEnd_4095857 1402095555388324449567335 := by
  unfold tailWord_4095857
  simp only [CollatzResearch.WordTrace]
  refine ⟨149388177522417080529341825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99592118348278053686227883 149388177522417080529341825)
  ·
    refine ⟨112041133141812810397006369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149388177522417080529341825 112041133141812810397006369)
    ·
      refine ⟨84030849856359607797754777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112041133141812810397006369 84030849856359607797754777)
      ·
        refine ⟨63023137392269705848316083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84030849856359607797754777 63023137392269705848316083)
        ·
          refine ⟨94534706088404558772474125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63023137392269705848316083 94534706088404558772474125)
          ·
            refine ⟨35450514783151709539677797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94534706088404558772474125 35450514783151709539677797)
            ·
              refine ⟨6646971521840945538689587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35450514783151709539677797 6646971521840945538689587)
              ·
                refine ⟨9970457282761418308034381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6646971521840945538689587 9970457282761418308034381)
                ·
                  refine ⟨3738921481035531865512893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9970457282761418308034381 3738921481035531865512893)
                  ·
                    refine ⟨1402095555388324449567335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3738921481035531865512893 1402095555388324449567335)
                    ·
                      rfl

theorem cell22_4095857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_4095857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095857 prefixEnd_4095857 := by exact prefixLift 4095857
  have htrace : WordTrace (prefixWord ++ tailWord_4095857) baseStart_4095857 baseEnd_4095857 := by
    simpa [prefixWord, tailWord_4095857, baseEnd_4095857] using wordTrace_append hprefix tailTrace_4095857
  have hstable : (prefixWord ++ tailWord_4095857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095857).length < 2 ^ (prefixWord ++ tailWord_4095857).sum := by decide
  have hdescent : baseEnd_4095857 < baseStart_4095857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095934 : List Nat := [4, 2, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_4095934 : Nat := 118140960795 + 4095934 * 2 ^ 59
def prefixEnd_4095934 : Nat := 4983230072969 + 3 ^ 40 * 4095934 * 2
def baseEnd_4095934 : Nat := 1402121914061921915392099

theorem tailTrace_4095934 : CollatzResearch.WordTrace tailWord_4095934 prefixEnd_4095934 1402121914061921915392099 := by
  unfold tailWord_4095934
  simp only [CollatzResearch.WordTrace]
  refine ⟨18673873242892265334986857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99593990628758748453263237 18673873242892265334986857)
  ·
    refine ⟨14005404932169199001240143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18673873242892265334986857 14005404932169199001240143)
    ·
      refine ⟨21008107398253798501860215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14005404932169199001240143 21008107398253798501860215)
      ·
        refine ⟨31512161097380697752790323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21008107398253798501860215 31512161097380697752790323)
        ·
          refine ⟨47268241646071046629185485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31512161097380697752790323 47268241646071046629185485)
          ·
            refine ⟨17725590617276642485944557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47268241646071046629185485 17725590617276642485944557)
            ·
              refine ⟨6647096481478740932229209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17725590617276642485944557 6647096481478740932229209)
              ·
                refine ⟨4985322361109055699171907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6647096481478740932229209 4985322361109055699171907)
                ·
                  refine ⟨7477983541663583548757861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4985322361109055699171907 7477983541663583548757861)
                  ·
                    refine ⟨1402121914061921915392099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7477983541663583548757861 1402121914061921915392099)
                    ·
                      rfl

theorem cell22_4095934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_4095934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095934 prefixEnd_4095934 := by exact prefixLift 4095934
  have htrace : WordTrace (prefixWord ++ tailWord_4095934) baseStart_4095934 baseEnd_4095934 := by
    simpa [prefixWord, tailWord_4095934, baseEnd_4095934] using wordTrace_append hprefix tailTrace_4095934
  have hstable : (prefixWord ++ tailWord_4095934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095934).length < 2 ^ (prefixWord ++ tailWord_4095934).sum := by decide
  have hdescent : baseEnd_4095934 < baseStart_4095934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095945 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 6, 4]
def baseStart_4095945 : Nat := 118140960795 + 4095945 * 2 ^ 59
def prefixEnd_4095945 : Nat := 4983230072969 + 3 ^ 40 * 4095945 * 2
def baseEnd_4095945 : Nat := 1402125679586721553367065

theorem tailTrace_4095945 : CollatzResearch.WordTrace tailWord_4095945 prefixEnd_4095945 1402125679586721553367065 := by
  unfold tailWord_4095945
  simp only [CollatzResearch.WordTrace]
  refine ⟨149391387146098271558545289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99594258097398847705696859 149391387146098271558545289)
  ·
    refine ⟨112043540359573703668908967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149391387146098271558545289 112043540359573703668908967)
    ·
      refine ⟨168065310539360555503363451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112043540359573703668908967 168065310539360555503363451)
      ·
        refine ⟨252097965809040833255045177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168065310539360555503363451 252097965809040833255045177)
        ·
          refine ⟨189073474356780624941283883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252097965809040833255045177 189073474356780624941283883)
          ·
            refine ⟨283610211535170937411925825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189073474356780624941283883 283610211535170937411925825)
            ·
              refine ⟨212707658651378203058944369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283610211535170937411925825 212707658651378203058944369)
              ·
                refine ⟨159530743988533652294208277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212707658651378203058944369 159530743988533652294208277)
                ·
                  refine ⟨7478003624462514951291013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159530743988533652294208277 7478003624462514951291013)
                  ·
                    refine ⟨1402125679586721553367065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7478003624462514951291013 1402125679586721553367065)
                    ·
                      rfl

theorem cell22_4095945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_4095945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095945 prefixEnd_4095945 := by exact prefixLift 4095945
  have htrace : WordTrace (prefixWord ++ tailWord_4095945) baseStart_4095945 baseEnd_4095945 := by
    simpa [prefixWord, tailWord_4095945, baseEnd_4095945] using wordTrace_append hprefix tailTrace_4095945
  have hstable : (prefixWord ++ tailWord_4095945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095945).length < 2 ^ (prefixWord ++ tailWord_4095945).sum := by decide
  have hdescent : baseEnd_4095945 < baseStart_4095945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095981 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_4095981 : Nat := 118140960795 + 4095981 * 2 ^ 59
def prefixEnd_4095981 : Nat := 4983230072969 + 3 ^ 40 * 4095981 * 2
def baseEnd_4095981 : Nat := 1402138003122429459466955

theorem tailTrace_4095981 : CollatzResearch.WordTrace tailWord_4095981 prefixEnd_4095981 1402138003122429459466955 := by
  unfold tailWord_4095981
  simp only [CollatzResearch.WordTrace]
  refine ⟨149392700173967849706855797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99595133449311899804570531 149392700173967849706855797)
  ·
    refine ⟨14005565641309485910017731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149392700173967849706855797 14005565641309485910017731)
    ·
      refine ⟨21008348461964228865026597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14005565641309485910017731 21008348461964228865026597)
      ·
        refine ⟨3939065336618292912192487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21008348461964228865026597 3939065336618292912192487)
        ·
          refine ⟨5908598004927439368288731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3939065336618292912192487 5908598004927439368288731)
          ·
            refine ⟨8862897007391159052433097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5908598004927439368288731 8862897007391159052433097)
            ·
              refine ⟨6647172755543369289324823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8862897007391159052433097 6647172755543369289324823)
              ·
                refine ⟨9970759133315053933987235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6647172755543369289324823 9970759133315053933987235)
                ·
                  refine ⟨14956138699972580900980853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9970759133315053933987235 14956138699972580900980853)
                  ·
                    refine ⟨1402138003122429459466955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14956138699972580900980853 1402138003122429459466955)
                    ·
                      rfl

theorem cell22_4095981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_4095981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095981 prefixEnd_4095981 := by exact prefixLift 4095981
  have htrace : WordTrace (prefixWord ++ tailWord_4095981) baseStart_4095981 baseEnd_4095981 := by
    simpa [prefixWord, tailWord_4095981, baseEnd_4095981] using wordTrace_append hprefix tailTrace_4095981
  have hstable : (prefixWord ++ tailWord_4095981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095981).length < 2 ^ (prefixWord ++ tailWord_4095981).sum := by decide
  have hdescent : baseEnd_4095981 < baseStart_4095981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095992 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 5, 3]
def baseStart_4095992 : Nat := 118140960795 + 4095992 * 2 ^ 59
def prefixEnd_4095992 : Nat := 4983230072969 + 3 ^ 40 * 4095992 * 2
def baseEnd_4095992 : Nat := 1402141768647229097441921

theorem tailTrace_4095992 : CollatzResearch.WordTrace tailWord_4095992 prefixEnd_4095992 1402141768647229097441921 := by
  unfold tailWord_4095992
  simp only [CollatzResearch.WordTrace]
  refine ⟨74696550688463999292753115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99595400917951999057004153 74696550688463999292753115)
  ·
    refine ⟨112044826032695998939129673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74696550688463999292753115 112044826032695998939129673)
    ·
      refine ⟨84033619524521999204347255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112044826032695998939129673 84033619524521999204347255)
      ·
        refine ⟨126050429286782998806520883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84033619524521999204347255 126050429286782998806520883)
        ·
          refine ⟨189075643930174498209781325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126050429286782998806520883 189075643930174498209781325)
          ·
            refine ⟨70903366473815436828667997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189075643930174498209781325 70903366473815436828667997)
            ·
              refine ⟨26588762427680788810750499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70903366473815436828667997 26588762427680788810750499)
              ·
                refine ⟨39883143641521183216125749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26588762427680788810750499 39883143641521183216125749)
                ·
                  refine ⟨3739044716392610926511789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39883143641521183216125749 3739044716392610926511789)
                  ·
                    refine ⟨1402141768647229097441921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3739044716392610926511789 1402141768647229097441921)
                    ·
                      rfl

theorem cell22_4095992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_4095992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4095992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4095992 prefixEnd_4095992 := by exact prefixLift 4095992
  have htrace : WordTrace (prefixWord ++ tailWord_4095992) baseStart_4095992 baseEnd_4095992 := by
    simpa [prefixWord, tailWord_4095992, baseEnd_4095992] using wordTrace_append hprefix tailTrace_4095992
  have hstable : (prefixWord ++ tailWord_4095992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095992).length < 2 ^ (prefixWord ++ tailWord_4095992).sum := by decide
  have hdescent : baseEnd_4095992 < baseStart_4095992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096026 : List Nat := [3, 1, 1, 3, 1, 3, 2, 4, 1, 3]
def baseStart_4096026 : Nat := 118140960795 + 4096026 * 2 ^ 59
def prefixEnd_4096026 : Nat := 4983230072969 + 3 ^ 40 * 4096026 * 2
def baseEnd_4096026 : Nat := 1402153407542064342091817

theorem tailTrace_4096026 : CollatzResearch.WordTrace tailWord_4096026 prefixEnd_4096026 1402153407542064342091817 := by
  unfold tailWord_4096026
  simp only [CollatzResearch.WordTrace]
  refine ⟨37348585364701205598060983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99596227639203214928162621 37348585364701205598060983)
  ·
    refine ⟨56022878047051808397091475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37348585364701205598060983 56022878047051808397091475)
    ·
      refine ⟨84034317070577712595637213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56022878047051808397091475 84034317070577712595637213)
      ·
        refine ⟨31512868901466642223363955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84034317070577712595637213 31512868901466642223363955)
        ·
          refine ⟨47269303352199963335045933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31512868901466642223363955 47269303352199963335045933)
          ·
            refine ⟨17725988757074986250642225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47269303352199963335045933 17725988757074986250642225)
            ·
              refine ⟨13294491567806239687981669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17725988757074986250642225 13294491567806239687981669)
              ·
                refine ⟨2492717168963669941496563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13294491567806239687981669 2492717168963669941496563)
                ·
                  refine ⟨3739075753445504912244845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492717168963669941496563 3739075753445504912244845)
                  ·
                    refine ⟨1402153407542064342091817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3739075753445504912244845 1402153407542064342091817)
                    ·
                      rfl

theorem cell22_4096026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_4096026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096026 prefixEnd_4096026 := by exact prefixLift 4096026
  have htrace : WordTrace (prefixWord ++ tailWord_4096026) baseStart_4096026 baseEnd_4096026 := by
    simpa [prefixWord, tailWord_4096026, baseEnd_4096026] using wordTrace_append hprefix tailTrace_4096026
  have hstable : (prefixWord ++ tailWord_4096026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096026).length < 2 ^ (prefixWord ++ tailWord_4096026).sum := by decide
  have hdescent : baseEnd_4096026 < baseStart_4096026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096037 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 2, 5]
def baseStart_4096037 : Nat := 118140960795 + 4096037 * 2 ^ 59
def prefixEnd_4096037 : Nat := 4983230072969 + 3 ^ 40 * 4096037 * 2
def baseEnd_4096037 : Nat := 1402157173066863980066783

theorem tailTrace_4096037 : CollatzResearch.WordTrace tailWord_4096037 prefixEnd_4096037 1402157173066863980066783 := by
  unfold tailWord_4096037
  simp only [CollatzResearch.WordTrace]
  refine ⟨149394742661764971270894365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99596495107843314180596243 149394742661764971270894365)
  ·
    refine ⟨56023028498161864226585387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149394742661764971270894365 56023028498161864226585387)
    ·
      refine ⟨84034542747242796339878081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56023028498161864226585387 84034542747242796339878081)
      ·
        refine ⟨63025907060432097254908561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84034542747242796339878081 63025907060432097254908561)
        ·
          refine ⟨47269430295324072941181421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63025907060432097254908561 47269430295324072941181421)
          ·
            refine ⟨17726036360746527352943033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47269430295324072941181421 17726036360746527352943033)
            ·
              refine ⟨13294527270559895514707275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17726036360746527352943033 13294527270559895514707275)
              ·
                refine ⟨19941790905839843272060913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13294527270559895514707275 19941790905839843272060913)
                ·
                  refine ⟨14956343179379882454045685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19941790905839843272060913 14956343179379882454045685)
                  ·
                    refine ⟨1402157173066863980066783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14956343179379882454045685 1402157173066863980066783)
                    ·
                      rfl

theorem cell22_4096037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_4096037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096037 prefixEnd_4096037 := by exact prefixLift 4096037
  have htrace : WordTrace (prefixWord ++ tailWord_4096037) baseStart_4096037 baseEnd_4096037 := by
    simpa [prefixWord, tailWord_4096037, baseEnd_4096037] using wordTrace_append hprefix tailTrace_4096037
  have hstable : (prefixWord ++ tailWord_4096037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096037).length < 2 ^ (prefixWord ++ tailWord_4096037).sum := by decide
  have hdescent : baseEnd_4096037 < baseStart_4096037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096097 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 6, 4]
def baseStart_4096097 : Nat := 118140960795 + 4096097 * 2 ^ 59
def prefixEnd_4096097 : Nat := 4983230072969 + 3 ^ 40 * 4096097 * 2
def baseEnd_4096097 : Nat := 1402177712293043823566599

theorem tailTrace_4096097 : CollatzResearch.WordTrace tailWord_4096097 prefixEnd_4096097 1402177712293043823566599 := by
  unfold tailWord_4096097
  simp only [CollatzResearch.WordTrace]
  refine ⟨149396931041547601518078545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99597954027698401012052363 149396931041547601518078545)
  ·
    refine ⟨112047698281160701138558909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149396931041547601518078545 112047698281160701138558909)
    ·
      refine ⟨42017886855435262926959591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112047698281160701138558909 42017886855435262926959591)
      ·
        refine ⟨63026830283152894390439387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42017886855435262926959591 63026830283152894390439387)
        ·
          refine ⟨94540245424729341585659081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63026830283152894390439387 94540245424729341585659081)
          ·
            refine ⟨70905184068547006189244311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94540245424729341585659081 70905184068547006189244311)
            ·
              refine ⟨106357776102820509283866467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70905184068547006189244311 106357776102820509283866467)
              ·
                refine ⟨159536664154230763925799701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106357776102820509283866467 159536664154230763925799701)
                ·
                  refine ⟨7478281132229567059021861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159536664154230763925799701 7478281132229567059021861)
                  ·
                    refine ⟨1402177712293043823566599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7478281132229567059021861 1402177712293043823566599)
                    ·
                      rfl

theorem cell22_4096097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_4096097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096097 prefixEnd_4096097 := by exact prefixLift 4096097
  have htrace : WordTrace (prefixWord ++ tailWord_4096097) baseStart_4096097 baseEnd_4096097 := by
    simpa [prefixWord, tailWord_4096097, baseEnd_4096097] using wordTrace_append hprefix tailTrace_4096097
  have hstable : (prefixWord ++ tailWord_4096097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096097).length < 2 ^ (prefixWord ++ tailWord_4096097).sum := by decide
  have hdescent : baseEnd_4096097 < baseStart_4096097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096112 : List Nat := [2, 1, 1, 1, 5, 2, 2, 8]
def baseStart_4096112 : Nat := 118140960795 + 4096112 * 2 ^ 59
def prefixEnd_4096112 : Nat := 4983230072969 + 3 ^ 40 * 4096112 * 2
def baseEnd_4096112 : Nat := 155798094122176531604617

theorem tailTrace_4096112 : CollatzResearch.WordTrace tailWord_4096112 prefixEnd_4096112 155798094122176531604617 := by
  unfold tailWord_4096112
  simp only [CollatzResearch.WordTrace]
  refine ⟨74698739068246629539937295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99598318757662172719916393 74698739068246629539937295)
  ·
    refine ⟨112048108602369944309905943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74698739068246629539937295 112048108602369944309905943)
    ·
      refine ⟨168072162903554916464858915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112048108602369944309905943 168072162903554916464858915)
      ·
        refine ⟨252108244355332374697288373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168072162903554916464858915 252108244355332374697288373)
        ·
          refine ⟨23635147908312410127870785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252108244355332374697288373 23635147908312410127870785)
          ·
            refine ⟨17726360931234307595903089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23635147908312410127870785 17726360931234307595903089)
            ·
              refine ⟨13294770698425730696927317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17726360931234307595903089 13294770698425730696927317)
              ·
                refine ⟨155798094122176531604617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13294770698425730696927317 155798094122176531604617)
                ·
                  rfl

theorem cell22_4096112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 8].length) (baseStart_4096112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096112 prefixEnd_4096112 := by exact prefixLift 4096112
  have htrace : WordTrace (prefixWord ++ tailWord_4096112) baseStart_4096112 baseEnd_4096112 := by
    simpa [prefixWord, tailWord_4096112, baseEnd_4096112] using wordTrace_append hprefix tailTrace_4096112
  have hstable : (prefixWord ++ tailWord_4096112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096112).length < 2 ^ (prefixWord ++ tailWord_4096112).sum := by decide
  have hdescent : baseEnd_4096112 < baseStart_4096112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096114 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_4096114 : Nat := 118140960795 + 4096114 * 2 ^ 59
def prefixEnd_4096114 : Nat := 4983230072969 + 3 ^ 40 * 4096114 * 2
def baseEnd_4096114 : Nat := 1402183531740461445891547

theorem tailTrace_4096114 : CollatzResearch.WordTrace tailWord_4096114 prefixEnd_4096114 1402183531740461445891547 := by
  unfold tailWord_4096114
  simp only [CollatzResearch.WordTrace]
  refine ⟨37349387770621503355361849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99598367388324008947631597 37349387770621503355361849)
  ·
    refine ⟨28012040827966127516521387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37349387770621503355361849 28012040827966127516521387)
    ·
      refine ⟨42018061241949191274782081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28012040827966127516521387 42018061241949191274782081)
      ·
        refine ⟨31513545931461893456086561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42018061241949191274782081 31513545931461893456086561)
        ·
          refine ⟨23635159448596420092064921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31513545931461893456086561 23635159448596420092064921)
          ·
            refine ⟨17726369586447315069048691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23635159448596420092064921 17726369586447315069048691)
            ·
              refine ⟨26589554379670972603573037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17726369586447315069048691 26589554379670972603573037)
              ·
                refine ⟨9971082892376614726339889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26589554379670972603573037 9971082892376614726339889)
                ·
                  refine ⟨7478312169282461044754917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9971082892376614726339889 7478312169282461044754917)
                  ·
                    refine ⟨1402183531740461445891547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7478312169282461044754917 1402183531740461445891547)
                    ·
                      rfl

theorem cell22_4096114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_4096114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096114 prefixEnd_4096114 := by exact prefixLift 4096114
  have htrace : WordTrace (prefixWord ++ tailWord_4096114) baseStart_4096114 baseEnd_4096114 := by
    simpa [prefixWord, tailWord_4096114, baseEnd_4096114] using wordTrace_append hprefix tailTrace_4096114
  have hstable : (prefixWord ++ tailWord_4096114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096114).length < 2 ^ (prefixWord ++ tailWord_4096114).sum := by decide
  have hdescent : baseEnd_4096114 < baseStart_4096114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096129 : List Nat := [1, 2, 4, 2, 4, 9]
def baseStart_4096129 : Nat := 118140960795 + 4096129 * 2 ^ 59
def prefixEnd_4096129 : Nat := 4983230072969 + 3 ^ 40 * 4096129 * 2
def baseEnd_4096129 : Nat := 17310971191938350700821

theorem tailTrace_4096129 : CollatzResearch.WordTrace tailWord_4096129 prefixEnd_4096129 17310971191938350700821 := by
  unfold tailWord_4096129
  simp only [CollatzResearch.WordTrace]
  refine ⟨149398098177431670983243441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99598732118287780655495627 149398098177431670983243441)
  ·
    refine ⟨112048573633073753237432581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149398098177431670983243441 112048573633073753237432581)
    ·
      refine ⟨21009107556201328732018609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112048573633073753237432581 21009107556201328732018609)
      ·
        refine ⟨15756830667150996549013957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21009107556201328732018609 15756830667150996549013957)
        ·
          refine ⟨2954405750090811852940117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15756830667150996549013957 2954405750090811852940117)
          ·
            refine ⟨17310971191938350700821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2954405750090811852940117 17310971191938350700821)
            ·
              rfl

theorem cell22_4096129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 9].length) (baseStart_4096129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096129 prefixEnd_4096129 := by exact prefixLift 4096129
  have htrace : WordTrace (prefixWord ++ tailWord_4096129) baseStart_4096129 baseEnd_4096129 := by
    simpa [prefixWord, tailWord_4096129, baseEnd_4096129] using wordTrace_append hprefix tailTrace_4096129
  have hstable : (prefixWord ++ tailWord_4096129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096129).length < 2 ^ (prefixWord ++ tailWord_4096129).sum := by decide
  have hdescent : baseEnd_4096129 < baseStart_4096129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096144 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 3, 3]
def baseStart_4096144 : Nat := 118140960795 + 4096144 * 2 ^ 59
def prefixEnd_4096144 : Nat := 4983230072969 + 3 ^ 40 * 4096144 * 2
def baseEnd_4096144 : Nat := 1402193801353551367641455

theorem tailTrace_4096144 : CollatzResearch.WordTrace tailWord_4096144 prefixEnd_4096144 1402193801353551367641455 := by
  unfold tailWord_4096144
  simp only [CollatzResearch.WordTrace]
  refine ⟨74699322636188664272519743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99599096848251552363359657 74699322636188664272519743)
  ·
    refine ⟨112048983954282996408779615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74699322636188664272519743 112048983954282996408779615)
    ·
      refine ⟨168073475931424494613169423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112048983954282996408779615 168073475931424494613169423)
      ·
        refine ⟨252110213897136741919754135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168073475931424494613169423 252110213897136741919754135)
        ·
          refine ⟨378165320845705112879631203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252110213897136741919754135 378165320845705112879631203)
          ·
            refine ⟨567247981268557669319446805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378165320845705112879631203 567247981268557669319446805)
            ·
              refine ⟨26589749121963640749349069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 567247981268557669319446805 26589749121963640749349069)
              ·
                refine ⟨9971155920736365281005901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26589749121963640749349069 9971155920736365281005901)
                ·
                  refine ⟨3739183470276136980377213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9971155920736365281005901 3739183470276136980377213)
                  ·
                    refine ⟨1402193801353551367641455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3739183470276136980377213 1402193801353551367641455)
                    ·
                      rfl

theorem cell22_4096144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 3, 3].length) (baseStart_4096144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096144 prefixEnd_4096144 := by exact prefixLift 4096144
  have htrace : WordTrace (prefixWord ++ tailWord_4096144) baseStart_4096144 baseEnd_4096144 := by
    simpa [prefixWord, tailWord_4096144, baseEnd_4096144] using wordTrace_append hprefix tailTrace_4096144
  have hstable : (prefixWord ++ tailWord_4096144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096144).length < 2 ^ (prefixWord ++ tailWord_4096144).sum := by decide
  have hdescent : baseEnd_4096144 < baseStart_4096144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096161 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 3, 3]
def baseStart_4096161 : Nat := 118140960795 + 4096161 * 2 ^ 59
def prefixEnd_4096161 : Nat := 4983230072969 + 3 ^ 40 * 4096161 * 2
def baseEnd_4096161 : Nat := 1402199620800968989966403

theorem tailTrace_4096161 : CollatzResearch.WordTrace tailWord_4096161 prefixEnd_4096161 1402199620800968989966403 := by
  unfold tailWord_4096161
  simp only [CollatzResearch.WordTrace]
  refine ⟨149399265313315740448408337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99599510208877160298938891 149399265313315740448408337)
  ·
    refine ⟨112049448984986805336306253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149399265313315740448408337 112049448984986805336306253)
    ·
      refine ⟨42018543369370052001114845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112049448984986805336306253 42018543369370052001114845)
      ·
        refine ⟨15756953763513769500418067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42018543369370052001114845 15756953763513769500418067)
        ·
          refine ⟨23635430645270654250627101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15756953763513769500418067 23635430645270654250627101)
          ·
            refine ⟨8863286491976495343985163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23635430645270654250627101 8863286491976495343985163)
            ·
              refine ⟨13294929737964743015977745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8863286491976495343985163 13294929737964743015977745)
              ·
                refine ⟨9971197303473557261983309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13294929737964743015977745 9971197303473557261983309)
                ·
                  refine ⟨3739198988802583973243741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9971197303473557261983309 3739198988802583973243741)
                  ·
                    refine ⟨1402199620800968989966403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3739198988802583973243741 1402199620800968989966403)
                    ·
                      rfl

theorem cell22_4096161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_4096161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096161 prefixEnd_4096161 := by exact prefixLift 4096161
  have htrace : WordTrace (prefixWord ++ tailWord_4096161) baseStart_4096161 baseEnd_4096161 := by
    simpa [prefixWord, tailWord_4096161, baseEnd_4096161] using wordTrace_append hprefix tailTrace_4096161
  have hstable : (prefixWord ++ tailWord_4096161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096161).length < 2 ^ (prefixWord ++ tailWord_4096161).sum := by decide
  have hdescent : baseEnd_4096161 < baseStart_4096161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096178 : List Nat := [3, 2, 1, 1, 1, 3, 4, 3, 1, 3]
def baseStart_4096178 : Nat := 118140960795 + 4096178 * 2 ^ 59
def prefixEnd_4096178 : Nat := 4983230072969 + 3 ^ 40 * 4096178 * 2
def baseEnd_4096178 : Nat := 1402205440248386612291351

theorem tailTrace_4096178 : CollatzResearch.WordTrace tailWord_4096178 prefixEnd_4096178 1402205440248386612291351 := by
  unfold tailWord_4096178
  simp only [CollatzResearch.WordTrace]
  refine ⟨37349971338563538087944297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99599923569502768234518125 37349971338563538087944297)
  ·
    refine ⟨28012478503922653565958223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37349971338563538087944297 28012478503922653565958223)
    ·
      refine ⟨42018717755883980348937335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28012478503922653565958223 42018717755883980348937335)
      ·
        refine ⟨63028076633825970523406003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42018717755883980348937335 63028076633825970523406003)
        ·
          refine ⟨94542114950738955785109005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63028076633825970523406003 94542114950738955785109005)
          ·
            refine ⟨35453293106527108419415877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94542114950738955785109005 35453293106527108419415877)
            ·
              refine ⟨6647492457473832828640477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35453293106527108419415877 6647492457473832828640477)
              ·
                refine ⟨2492809671552687310740179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6647492457473832828640477 2492809671552687310740179)
                ·
                  refine ⟨3739214507329030966110269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492809671552687310740179 3739214507329030966110269)
                  ·
                    refine ⟨1402205440248386612291351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3739214507329030966110269 1402205440248386612291351)
                    ·
                      rfl

theorem cell22_4096178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_4096178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096178 prefixEnd_4096178 := by exact prefixLift 4096178
  have htrace : WordTrace (prefixWord ++ tailWord_4096178) baseStart_4096178 baseEnd_4096178 := by
    simpa [prefixWord, tailWord_4096178, baseEnd_4096178] using wordTrace_append hprefix tailTrace_4096178
  have hstable : (prefixWord ++ tailWord_4096178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096178).length < 2 ^ (prefixWord ++ tailWord_4096178).sum := by decide
  have hdescent : baseEnd_4096178 < baseStart_4096178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096234 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_4096234 : Nat := 118140960795 + 4096234 * 2 ^ 59
def prefixEnd_4096234 : Nat := 4983230072969 + 3 ^ 40 * 4096234 * 2
def baseEnd_4096234 : Nat := 1402224610192821132891179

theorem tailTrace_4096234 : CollatzResearch.WordTrace tailWord_4096234 prefixEnd_4096234 1402224610192821132891179 := by
  unfold tailWord_4096234
  simp only [CollatzResearch.WordTrace]
  refine ⟨37350481960512818478953939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99601285228034182610543837 37350481960512818478953939)
  ·
    refine ⟨56025722940769227718430909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37350481960512818478953939 56025722940769227718430909)
    ·
      refine ⟨21009646102788460394411591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56025722940769227718430909 21009646102788460394411591)
      ·
        refine ⟨31514469154182690591617387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21009646102788460394411591 31514469154182690591617387)
        ·
          refine ⟨47271703731274035887426081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31514469154182690591617387 47271703731274035887426081)
          ·
            refine ⟨35453777798455526915569561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47271703731274035887426081 35453777798455526915569561)
            ·
              refine ⟨26590333348841645186677171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35453777798455526915569561 26590333348841645186677171)
              ·
                refine ⟨39885500023262467780015757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26590333348841645186677171 39885500023262467780015757)
                ·
                  refine ⟨14957062508723425417505909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39885500023262467780015757 14957062508723425417505909)
                  ·
                    refine ⟨1402224610192821132891179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14957062508723425417505909 1402224610192821132891179)
                    ·
                      rfl

theorem cell22_4096234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_4096234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096234 prefixEnd_4096234 := by exact prefixLift 4096234
  have htrace : WordTrace (prefixWord ++ tailWord_4096234) baseStart_4096234 baseEnd_4096234 := by
    simpa [prefixWord, tailWord_4096234, baseEnd_4096234] using wordTrace_append hprefix tailTrace_4096234
  have hstable : (prefixWord ++ tailWord_4096234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096234).length < 2 ^ (prefixWord ++ tailWord_4096234).sum := by decide
  have hdescent : baseEnd_4096234 < baseStart_4096234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096264 : List Nat := [2, 1, 3, 2, 3, 1, 1, 9]
def baseStart_4096264 : Nat := 118140960795 + 4096264 * 2 ^ 59
def prefixEnd_4096264 : Nat := 4983230072969 + 3 ^ 40 * 4096264 * 2
def baseEnd_4096264 : Nat := 155803875533990117182343

theorem tailTrace_4096264 : CollatzResearch.WordTrace tailWord_4096264 prefixEnd_4096264 155803875533990117182343 := by
  unfold tailWord_4096264
  simp only [CollatzResearch.WordTrace]
  refine ⟨74701511015971294519703923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99602014687961726026271897 74701511015971294519703923)
  ·
    refine ⟨112052266523956941779555885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74701511015971294519703923 112052266523956941779555885)
    ·
      refine ⟨42019599946483853167333457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112052266523956941779555885 42019599946483853167333457)
      ·
        refine ⟨31514699959862889875500093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42019599946483853167333457 31514699959862889875500093)
        ·
          refine ⟨11818012484948583703312535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31514699959862889875500093 11818012484948583703312535)
          ·
            refine ⟨17727018727422875554968803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11818012484948583703312535 17727018727422875554968803)
            ·
              refine ⟨26590528091134313332453205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17727018727422875554968803 26590528091134313332453205)
              ·
                refine ⟨155803875533990117182343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26590528091134313332453205 155803875533990117182343)
                ·
                  rfl

theorem cell22_4096264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 9].length) (baseStart_4096264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096264 prefixEnd_4096264 := by exact prefixLift 4096264
  have htrace : WordTrace (prefixWord ++ tailWord_4096264) baseStart_4096264 baseEnd_4096264 := by
    simpa [prefixWord, tailWord_4096264, baseEnd_4096264] using wordTrace_append hprefix tailTrace_4096264
  have hstable : (prefixWord ++ tailWord_4096264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096264).length < 2 ^ (prefixWord ++ tailWord_4096264).sum := by decide
  have hdescent : baseEnd_4096264 < baseStart_4096264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096302 : List Nat := [4, 1, 3, 3, 1, 1, 2, 2, 2, 3]
def baseStart_4096302 : Nat := 118140960795 + 4096302 * 2 ^ 59
def prefixEnd_4096302 : Nat := 4983230072969 + 3 ^ 40 * 4096302 * 2
def baseEnd_4096302 : Nat := 1402247887982491622190971

theorem tailTrace_4096302 : CollatzResearch.WordTrace tailWord_4096302 prefixEnd_4096302 1402247887982491622190971 := by
  unfold tailWord_4096302
  simp only [CollatzResearch.WordTrace]
  refine ⟨18675551000725615191161395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99602938670536614352860773 18675551000725615191161395)
  ·
    refine ⟨28013326501088422786742093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18675551000725615191161395 28013326501088422786742093)
    ·
      refine ⟨10504997437908158545028285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28013326501088422786742093 10504997437908158545028285)
      ·
        refine ⟨3939374039215559454385607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10504997437908158545028285 3939374039215559454385607)
        ·
          refine ⟨5909061058823339181578411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3939374039215559454385607 5909061058823339181578411)
          ·
            refine ⟨8863591588235008772367617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5909061058823339181578411 8863591588235008772367617)
            ·
              refine ⟨6647693691176256579275713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8863591588235008772367617 6647693691176256579275713)
              ·
                refine ⟨4985770268382192434456785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6647693691176256579275713 4985770268382192434456785)
                ·
                  refine ⟨3739327701286644325842589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4985770268382192434456785 3739327701286644325842589)
                  ·
                    refine ⟨1402247887982491622190971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3739327701286644325842589 1402247887982491622190971)
                    ·
                      rfl

theorem cell22_4096302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_4096302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096302 prefixEnd_4096302 := by exact prefixLift 4096302
  have htrace : WordTrace (prefixWord ++ tailWord_4096302) baseStart_4096302 baseEnd_4096302 := by
    simpa [prefixWord, tailWord_4096302, baseEnd_4096302] using wordTrace_append hprefix tailTrace_4096302
  have hstable : (prefixWord ++ tailWord_4096302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096302).length < 2 ^ (prefixWord ++ tailWord_4096302).sum := by decide
  have hdescent : baseEnd_4096302 < baseStart_4096302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096416 : List Nat := [2, 1, 1, 4, 1, 5, 8]
def baseStart_4096416 : Nat := 118140960795 + 4096416 * 2 ^ 59
def prefixEnd_4096416 : Nat := 4983230072969 + 3 ^ 40 * 4096416 * 2
def baseEnd_4096416 : Nat := 51936552315267900920023

theorem tailTrace_4096416 : CollatzResearch.WordTrace tailWord_4096416 prefixEnd_4096416 51936552315267900920023 := by
  unfold tailWord_4096416
  simp only [CollatzResearch.WordTrace]
  refine ⟨74704282963695959499470551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99605710618261279332627401 74704282963695959499470551)
  ·
    refine ⟨112056424445543939249205827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74704282963695959499470551 112056424445543939249205827)
    ·
      refine ⟨168084636668315908873808741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112056424445543939249205827 168084636668315908873808741)
      ·
        refine ⟨31515869375309232913839139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168084636668315908873808741 31515869375309232913839139)
        ·
          refine ⟨47273804062963849370758709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31515869375309232913839139 47273804062963849370758709)
          ·
            refine ⟨4431919130902860878508629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47273804062963849370758709 4431919130902860878508629)
            ·
              refine ⟨51936552315267900920023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4431919130902860878508629 51936552315267900920023)
              ·
                rfl

theorem cell22_4096416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 8].length) (baseStart_4096416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096416 prefixEnd_4096416 := by exact prefixLift 4096416
  have htrace : WordTrace (prefixWord ++ tailWord_4096416) baseStart_4096416 baseEnd_4096416 := by
    simpa [prefixWord, tailWord_4096416, baseEnd_4096416] using wordTrace_append hprefix tailTrace_4096416
  have hstable : (prefixWord ++ tailWord_4096416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096416).length < 2 ^ (prefixWord ++ tailWord_4096416).sum := by decide
  have hdescent : baseEnd_4096416 < baseStart_4096416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096418 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_4096418 : Nat := 118140960795 + 4096418 * 2 ^ 59
def prefixEnd_4096418 : Nat := 4983230072969 + 3 ^ 40 * 4096418 * 2
def baseEnd_4096418 : Nat := 1402287597153105986290615

theorem tailTrace_4096418 : CollatzResearch.WordTrace tailWord_4096418 prefixEnd_4096418 1402287597153105986290615 := by
  unfold tailWord_4096418
  simp only [CollatzResearch.WordTrace]
  refine ⟨37352159718346168335128477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99605759248923115560342605 37352159718346168335128477)
  ·
    refine ⟨14007059894379813125673179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37352159718346168335128477 14007059894379813125673179)
    ·
      refine ⟨21010589841569719688509769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14007059894379813125673179 21010589841569719688509769)
      ·
        refine ⟨15757942381177289766382327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21010589841569719688509769 15757942381177289766382327)
        ·
          refine ⟨23636913571765934649573491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15757942381177289766382327 23636913571765934649573491)
          ·
            refine ⟨35455370357648901974360237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23636913571765934649573491 35455370357648901974360237)
            ·
              refine ⟨13295763884118338240385089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35455370357648901974360237 13295763884118338240385089)
              ·
                refine ⟨9971822913088753680288817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13295763884118338240385089 9971822913088753680288817)
                ·
                  refine ⟨7478867184816565260216613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9971822913088753680288817 7478867184816565260216613)
                  ·
                    refine ⟨1402287597153105986290615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7478867184816565260216613 1402287597153105986290615)
                    ·
                      rfl

theorem cell22_4096418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_4096418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096418 prefixEnd_4096418 := by exact prefixLift 4096418
  have htrace : WordTrace (prefixWord ++ tailWord_4096418) baseStart_4096418 baseEnd_4096418 := by
    simpa [prefixWord, tailWord_4096418, baseEnd_4096418] using wordTrace_append hprefix tailTrace_4096418
  have hstable : (prefixWord ++ tailWord_4096418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096418).length < 2 ^ (prefixWord ++ tailWord_4096418).sum := by decide
  have hdescent : baseEnd_4096418 < baseStart_4096418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096491 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 5, 4]
def baseStart_4096491 : Nat := 118140960795 + 4096491 * 2 ^ 59
def prefixEnd_4096491 : Nat := 4983230072969 + 3 ^ 40 * 4096491 * 2
def baseEnd_4096491 : Nat := 1402312586544958129215391

theorem tailTrace_4096491 : CollatzResearch.WordTrace tailWord_4096491 prefixEnd_4096491 1402312586544958129215391 := by
  unfold tailWord_4096491
  simp only [CollatzResearch.WordTrace]
  refine ⟨149411301402120206807921327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99607534268080137871947551 149411301402120206807921327)
  ·
    refine ⟨224116952103180310211881991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149411301402120206807921327 224116952103180310211881991)
    ·
      refine ⟨336175428154770465317822987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224116952103180310211881991 336175428154770465317822987)
      ·
        refine ⟨504263142232155697976734481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336175428154770465317822987 504263142232155697976734481)
        ·
          refine ⟨378197356674116773482550861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504263142232155697976734481 378197356674116773482550861)
          ·
            refine ⟨141824008752793790055956573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378197356674116773482550861 141824008752793790055956573)
            ·
              refine ⟨53184003282297671270983715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141824008752793790055956573 53184003282297671270983715)
              ·
                refine ⟨79776004923446506906475573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53184003282297671270983715 79776004923446506906475573)
                ·
                  refine ⟨7479000461573110022482085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79776004923446506906475573 7479000461573110022482085)
                  ·
                    refine ⟨1402312586544958129215391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7479000461573110022482085 1402312586544958129215391)
                    ·
                      rfl

theorem cell22_4096491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 4].length) (baseStart_4096491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096491 prefixEnd_4096491 := by exact prefixLift 4096491
  have htrace : WordTrace (prefixWord ++ tailWord_4096491) baseStart_4096491 baseEnd_4096491 := by
    simpa [prefixWord, tailWord_4096491, baseEnd_4096491] using wordTrace_append hprefix tailTrace_4096491
  have hstable : (prefixWord ++ tailWord_4096491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096491).length < 2 ^ (prefixWord ++ tailWord_4096491).sum := by decide
  have hdescent : baseEnd_4096491 < baseStart_4096491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096493 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_4096493 : Nat := 118140960795 + 4096493 * 2 ^ 59
def prefixEnd_4096493 : Nat := 4983230072969 + 3 ^ 40 * 4096493 * 2
def baseEnd_4096493 : Nat := 1402313271185830790665385

theorem tailTrace_4096493 : CollatzResearch.WordTrace tailWord_4096493 prefixEnd_4096493 1402313271185830790665385 := by
  unfold tailWord_4096493
  simp only [CollatzResearch.WordTrace]
  refine ⟨149411374348112961149494133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99607582898741974099662755 149411374348112961149494133)
  ·
    refine ⟨14007316345135590107765075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149411374348112961149494133 14007316345135590107765075)
    ·
      refine ⟨21010974517703385161647613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14007316345135590107765075 21010974517703385161647613)
      ·
        refine ⟨7879115444138769435617855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21010974517703385161647613 7879115444138769435617855)
        ·
          refine ⟨11818673166208154153426783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7879115444138769435617855 11818673166208154153426783)
          ·
            refine ⟨17728009749312231230140175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11818673166208154153426783 17728009749312231230140175)
            ·
              refine ⟨26592014623968346845210263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17728009749312231230140175 26592014623968346845210263)
              ·
                refine ⟨39888021935952520267815395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26592014623968346845210263 39888021935952520267815395)
                ·
                  refine ⟨59832032903928780401723093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39888021935952520267815395 59832032903928780401723093)
                  ·
                    refine ⟨1402313271185830790665385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59832032903928780401723093 1402313271185830790665385)
                    ·
                      rfl

theorem cell22_4096493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_4096493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096493 prefixEnd_4096493 := by exact prefixLift 4096493
  have htrace : WordTrace (prefixWord ++ tailWord_4096493) baseStart_4096493 baseEnd_4096493 := by
    simpa [prefixWord, tailWord_4096493, baseEnd_4096493] using wordTrace_append hprefix tailTrace_4096493
  have hstable : (prefixWord ++ tailWord_4096493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096493).length < 2 ^ (prefixWord ++ tailWord_4096493).sum := by decide
  have hdescent : baseEnd_4096493 < baseStart_4096493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096508 : List Nat := [2, 2, 2, 1, 2, 1, 1, 6, 1, 4]
def baseStart_4096508 : Nat := 118140960795 + 4096508 * 2 ^ 59
def prefixEnd_4096508 : Nat := 4983230072969 + 3 ^ 40 * 4096508 * 2
def baseEnd_4096508 : Nat := 1402318405992375751540339

theorem tailTrace_4096508 : CollatzResearch.WordTrace tailWord_4096508 prefixEnd_4096508 1402318405992375751540339 := by
  unfold tailWord_4096508
  simp only [CollatzResearch.WordTrace]
  refine ⟨74705960721529309355645089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99607947628705745807526785 74705960721529309355645089)
  ·
    refine ⟨56029470541146982016733817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74705960721529309355645089 56029470541146982016733817)
    ·
      refine ⟨42022102905860236512550363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56029470541146982016733817 42022102905860236512550363)
      ·
        refine ⟨63033154358790354768825545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42022102905860236512550363 63033154358790354768825545)
        ·
          refine ⟨47274865769092766076619159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63033154358790354768825545 47274865769092766076619159)
          ·
            refine ⟨70912298653639149114928739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47274865769092766076619159 70912298653639149114928739)
            ·
              refine ⟨106368447980458723672393109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70912298653639149114928739 106368447980458723672393109)
              ·
                refine ⟨4986020999084002672143427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106368447980458723672393109 4986020999084002672143427)
                ·
                  refine ⟨7479031498626004008215141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4986020999084002672143427 7479031498626004008215141)
                  ·
                    refine ⟨1402318405992375751540339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7479031498626004008215141 1402318405992375751540339)
                    ·
                      rfl

theorem cell22_4096508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_4096508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096508 prefixEnd_4096508 := by exact prefixLift 4096508
  have htrace : WordTrace (prefixWord ++ tailWord_4096508) baseStart_4096508 baseEnd_4096508 := by
    simpa [prefixWord, tailWord_4096508, baseEnd_4096508] using wordTrace_append hprefix tailTrace_4096508
  have hstable : (prefixWord ++ tailWord_4096508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096508).length < 2 ^ (prefixWord ++ tailWord_4096508).sum := by decide
  have hdescent : baseEnd_4096508 < baseStart_4096508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096521 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 3, 5]
def baseStart_4096521 : Nat := 118140960795 + 4096521 * 2 ^ 59
def prefixEnd_4096521 : Nat := 4983230072969 + 3 ^ 40 * 4096521 * 2
def baseEnd_4096521 : Nat := 1402322856158048050965299

theorem tailTrace_4096521 : CollatzResearch.WordTrace tailWord_4096521 prefixEnd_4096521 1402322856158048050965299 := by
  unfold tailWord_4096521
  simp only [CollatzResearch.WordTrace]
  refine ⟨149412395592011521931513417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99608263728007681287675611 149412395592011521931513417)
  ·
    refine ⟨112059296694008641448635063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149412395592011521931513417 112059296694008641448635063)
    ·
      refine ⟨168088945041012962172952595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112059296694008641448635063 168088945041012962172952595)
      ·
        refine ⟨252133417561519443259428893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168088945041012962172952595 252133417561519443259428893)
        ·
          refine ⟨94550031585569791222285835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252133417561519443259428893 94550031585569791222285835)
          ·
            refine ⟨141825047378354686833428753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94550031585569791222285835 141825047378354686833428753)
            ·
              refine ⟨106368785533766015125071565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141825047378354686833428753 106368785533766015125071565)
              ·
                refine ⟨39888294575162255671901837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106368785533766015125071565 39888294575162255671901837)
                ·
                  refine ⟨14958110465685845876963189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39888294575162255671901837 14958110465685845876963189)
                  ·
                    refine ⟨1402322856158048050965299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14958110465685845876963189 1402322856158048050965299)
                    ·
                      rfl

theorem cell22_4096521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_4096521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096521 prefixEnd_4096521 := by exact prefixLift 4096521
  have htrace : WordTrace (prefixWord ++ tailWord_4096521) baseStart_4096521 baseEnd_4096521 := by
    simpa [prefixWord, tailWord_4096521, baseEnd_4096521] using wordTrace_append hprefix tailTrace_4096521
  have hstable : (prefixWord ++ tailWord_4096521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096521).length < 2 ^ (prefixWord ++ tailWord_4096521).sum := by decide
  have hdescent : baseEnd_4096521 < baseStart_4096521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096540 : List Nat := [2, 2, 3, 1, 2, 2, 2, 4, 4]
def baseStart_4096540 : Nat := 118140960795 + 4096540 * 2 ^ 59
def prefixEnd_4096540 : Nat := 4983230072969 + 3 ^ 40 * 4096540 * 2
def baseEnd_4096540 : Nat := 467443120082112778246747

theorem tailTrace_4096540 : CollatzResearch.WordTrace tailWord_4096540 prefixEnd_4096540 467443120082112778246747 := by
  unfold tailWord_4096540
  simp only [CollatzResearch.WordTrace]
  refine ⟨74706544289471344088227537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99608725719295125450970049 74706544289471344088227537)
  ·
    refine ⟨56029908217103508066170653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74706544289471344088227537 56029908217103508066170653)
    ·
      refine ⟨21011215581413815524813995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56029908217103508066170653 21011215581413815524813995)
      ·
        refine ⟨31516823372120723287220993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21011215581413815524813995 31516823372120723287220993)
        ·
          refine ⟨23637617529090542465415745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31516823372120723287220993 23637617529090542465415745)
          ·
            refine ⟨17728213146817906849061809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23637617529090542465415745 17728213146817906849061809)
            ·
              refine ⟨13296159860113430136796357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17728213146817906849061809 13296159860113430136796357)
              ·
                refine ⟨2493029973771268150649317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13296159860113430136796357 2493029973771268150649317)
                ·
                  refine ⟨467443120082112778246747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2493029973771268150649317 467443120082112778246747)
                  ·
                    rfl

theorem cell22_4096540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_4096540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096540 prefixEnd_4096540 := by exact prefixLift 4096540
  have htrace : WordTrace (prefixWord ++ tailWord_4096540) baseStart_4096540 baseEnd_4096540 := by
    simpa [prefixWord, tailWord_4096540, baseEnd_4096540] using wordTrace_append hprefix tailTrace_4096540
  have hstable : (prefixWord ++ tailWord_4096540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096540).length < 2 ^ (prefixWord ++ tailWord_4096540).sum := by decide
  have hdescent : baseEnd_4096540 < baseStart_4096540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096600 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 3, 3]
def baseStart_4096600 : Nat := 118140960795 + 4096600 * 2 ^ 59
def prefixEnd_4096600 : Nat := 4983230072969 + 3 ^ 40 * 4096600 * 2
def baseEnd_4096600 : Nat := 1402349899472518178240057

theorem tailTrace_4096600 : CollatzResearch.WordTrace tailWord_4096600 prefixEnd_4096600 1402349899472518178240057 := by
  unfold tailWord_4096600
  simp only [CollatzResearch.WordTrace]
  refine ⟨74707638479362659211819627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99610184639150212282426169 74707638479362659211819627)
  ·
    refine ⟨112061457719043988817729441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74707638479362659211819627 112061457719043988817729441)
    ·
      refine ⟨84046093289282991613297081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112061457719043988817729441 84046093289282991613297081)
      ·
        refine ⟨63034569966962243709972811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84046093289282991613297081 63034569966962243709972811)
        ·
          refine ⟨94551854950443365564959217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63034569966962243709972811 94551854950443365564959217)
          ·
            refine ⟨70913891212832524173719413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94551854950443365564959217 70913891212832524173719413)
            ·
              refine ⟨6648177301203049141286195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70913891212832524173719413 6648177301203049141286195)
              ·
                refine ⟨9972265951804573711929293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6648177301203049141286195 9972265951804573711929293)
                ·
                  refine ⟨3739599731926715141973485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9972265951804573711929293 3739599731926715141973485)
                  ·
                    refine ⟨1402349899472518178240057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3739599731926715141973485 1402349899472518178240057)
                    ·
                      rfl

theorem cell22_4096600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_4096600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096600 prefixEnd_4096600 := by exact prefixLift 4096600
  have htrace : WordTrace (prefixWord ++ tailWord_4096600) baseStart_4096600 baseEnd_4096600 := by
    simpa [prefixWord, tailWord_4096600, baseEnd_4096600] using wordTrace_append hprefix tailTrace_4096600
  have hstable : (prefixWord ++ tailWord_4096600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096600).length < 2 ^ (prefixWord ++ tailWord_4096600).sum := by decide
  have hdescent : baseEnd_4096600 < baseStart_4096600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096690 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 4, 3]
def baseStart_4096690 : Nat := 118140960795 + 4096690 * 2 ^ 59
def prefixEnd_4096690 : Nat := 4983230072969 + 3 ^ 40 * 4096690 * 2
def baseEnd_4096690 : Nat := 1402380708311787943489781

theorem tailTrace_4096690 : CollatzResearch.WordTrace tailWord_4096690 prefixEnd_4096690 1402380708311787943489781 := by
  unfold tailWord_4096690
  simp only [CollatzResearch.WordTrace]
  refine ⟨37354639882099815948603881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99612373018932842529610349 37354639882099815948603881)
  ·
    refine ⟨28015979911574861961452911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37354639882099815948603881 28015979911574861961452911)
    ·
      refine ⟨42023969867362292942179367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28015979911574861961452911 42023969867362292942179367)
      ·
        refine ⟨63035954801043439413269051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42023969867362292942179367 63035954801043439413269051)
        ·
          refine ⟨94553932201565159119903577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63035954801043439413269051 94553932201565159119903577)
          ·
            refine ⟨70915449151173869339927683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94553932201565159119903577 70915449151173869339927683)
            ·
              refine ⟨106373173726760804009891525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70915449151173869339927683 106373173726760804009891525)
              ·
                refine ⟨19944970073767650751854661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106373173726760804009891525 19944970073767650751854661)
                ·
                  refine ⟨3739681888831434515972749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19944970073767650751854661 3739681888831434515972749)
                  ·
                    refine ⟨1402380708311787943489781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3739681888831434515972749 1402380708311787943489781)
                    ·
                      rfl

theorem cell22_4096690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_4096690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096690 prefixEnd_4096690 := by exact prefixLift 4096690
  have htrace : WordTrace (prefixWord ++ tailWord_4096690) baseStart_4096690 baseEnd_4096690 := by
    simpa [prefixWord, tailWord_4096690, baseEnd_4096690] using wordTrace_append hprefix tailTrace_4096690
  have hstable : (prefixWord ++ tailWord_4096690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096690).length < 2 ^ (prefixWord ++ tailWord_4096690).sum := by decide
  have hdescent : baseEnd_4096690 < baseStart_4096690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096703 : List Nat := [1, 1, 2, 2, 2, 5, 9]
def baseStart_4096703 : Nat := 118140960795 + 4096703 * 2 ^ 59
def prefixEnd_4096703 : Nat := 4983230072969 + 3 ^ 40 * 4096703 * 2
def baseEnd_4096703 : Nat := 51940191054720749737583

theorem tailTrace_4096703 : CollatzResearch.WordTrace tailWord_4096703 prefixEnd_4096703 51940191054720749737583 := by
  unfold tailWord_4096703
  simp only [CollatzResearch.WordTrace]
  refine ⟨149419033677352167014638763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99612689118234778009759175 149419033677352167014638763)
  ·
    refine ⟨224128550516028250521958145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149419033677352167014638763 224128550516028250521958145)
    ·
      refine ⟨168096412887021187891468609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224128550516028250521958145 168096412887021187891468609)
      ·
        refine ⟨126072309665265890918601457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168096412887021187891468609 126072309665265890918601457)
        ·
          refine ⟨94554232248949418188951093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126072309665265890918601457 94554232248949418188951093)
          ·
            refine ⟨8864459273339007955214165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94554232248949418188951093 8864459273339007955214165)
            ·
              refine ⟨51940191054720749737583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8864459273339007955214165 51940191054720749737583)
              ·
                rfl

theorem cell22_4096703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 9].length) (baseStart_4096703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096703 prefixEnd_4096703 := by exact prefixLift 4096703
  have htrace : WordTrace (prefixWord ++ tailWord_4096703) baseStart_4096703 baseEnd_4096703 := by
    simpa [prefixWord, tailWord_4096703, baseEnd_4096703] using wordTrace_append hprefix tailTrace_4096703
  have hstable : (prefixWord ++ tailWord_4096703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096703).length < 2 ^ (prefixWord ++ tailWord_4096703).sum := by decide
  have hdescent : baseEnd_4096703 < baseStart_4096703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096724 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_4096724 : Nat := 118140960795 + 4096724 * 2 ^ 59
def prefixEnd_4096724 : Nat := 4983230072969 + 3 ^ 40 * 4096724 * 2
def baseEnd_4096724 : Nat := 1402392347206623188139677

theorem tailTrace_4096724 : CollatzResearch.WordTrace tailWord_4096724 prefixEnd_4096724 1402392347206623188139677 := by
  unfold tailWord_4096724
  simp only [CollatzResearch.WordTrace]
  refine ⟨74709899805138043800576613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99613199740184058400768817 74709899805138043800576613)
  ·
    refine ⟨14008106213463383212608115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74709899805138043800576613 14008106213463383212608115)
    ·
      refine ⟨21012159320195074818912173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14008106213463383212608115 21012159320195074818912173)
      ·
        refine ⟨7879559745073153057092065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21012159320195074818912173 7879559745073153057092065)
        ·
          refine ⟨5909669808804864792819049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7879559745073153057092065 5909669808804864792819049)
          ·
            refine ⟨4432252356603648594614287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5909669808804864792819049 4432252356603648594614287)
            ·
              refine ⟨6648378534905472891921431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4432252356603648594614287 6648378534905472891921431)
              ·
                refine ⟨9972567802358209337882147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6648378534905472891921431 9972567802358209337882147)
                ·
                  refine ⟨14958851703537314006823221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9972567802358209337882147 14958851703537314006823221)
                  ·
                    refine ⟨1402392347206623188139677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14958851703537314006823221 1402392347206623188139677)
                    ·
                      rfl

theorem cell22_4096724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_4096724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096724 prefixEnd_4096724 := by exact prefixLift 4096724
  have htrace : WordTrace (prefixWord ++ tailWord_4096724) baseStart_4096724 baseEnd_4096724 := by
    simpa [prefixWord, tailWord_4096724, baseEnd_4096724] using wordTrace_append hprefix tailTrace_4096724
  have hstable : (prefixWord ++ tailWord_4096724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096724).length < 2 ^ (prefixWord ++ tailWord_4096724).sum := by decide
  have hdescent : baseEnd_4096724 < baseStart_4096724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096737 : List Nat := [1, 2, 3, 1, 4, 3, 2, 6]
def baseStart_4096737 : Nat := 118140960795 + 4096737 * 2 ^ 59
def prefixEnd_4096737 : Nat := 4983230072969 + 3 ^ 40 * 4096737 * 2
def baseEnd_4096737 : Nat := 155821866374699498618293

theorem tailTrace_4096737 : CollatzResearch.WordTrace tailWord_4096737 prefixEnd_4096737 155821866374699498618293 := by
  unfold tailWord_4096737
  simp only [CollatzResearch.WordTrace]
  refine ⟨149420273759228990821376465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99613515839485993880917643 149420273759228990821376465)
  ·
    refine ⟨112065205319421743116032349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149420273759228990821376465 112065205319421743116032349)
    ·
      refine ⟨42024451994783153668512131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112065205319421743116032349 42024451994783153668512131)
      ·
        refine ⟨63036677992174730502768197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42024451994783153668512131 63036677992174730502768197)
        ·
          refine ⟨11819377123532761969269037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63036677992174730502768197 11819377123532761969269037)
          ·
            refine ⟨4432266421324785738475889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11819377123532761969269037 4432266421324785738475889)
            ·
              refine ⟨3324199815993589303856917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4432266421324785738475889 3324199815993589303856917)
              ·
                refine ⟨155821866374699498618293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3324199815993589303856917 155821866374699498618293)
                ·
                  rfl

theorem cell22_4096737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 6].length) (baseStart_4096737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096737 prefixEnd_4096737 := by exact prefixLift 4096737
  have htrace : WordTrace (prefixWord ++ tailWord_4096737) baseStart_4096737 baseEnd_4096737 := by
    simpa [prefixWord, tailWord_4096737, baseEnd_4096737] using wordTrace_append hprefix tailTrace_4096737
  have hstable : (prefixWord ++ tailWord_4096737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096737).length < 2 ^ (prefixWord ++ tailWord_4096737).sum := by decide
  have hdescent : baseEnd_4096737 < baseStart_4096737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096756 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4096756 : Nat := 118140960795 + 4096756 * 2 ^ 59
def prefixEnd_4096756 : Nat := 4983230072969 + 3 ^ 40 * 4096756 * 2
def baseEnd_4096756 : Nat := 1402403301460585771339579

theorem tailTrace_4096756 : CollatzResearch.WordTrace tailWord_4096756 prefixEnd_4096756 1402403301460585771339579 := by
  unfold tailWord_4096756
  simp only [CollatzResearch.WordTrace]
  refine ⟨74710483373080078533159061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99613977830773438044212081 74710483373080078533159061)
  ·
    refine ⟨3502053908113128681241831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74710483373080078533159061 3502053908113128681241831)
    ·
      refine ⟨5253080862169693021862747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3502053908113128681241831 5253080862169693021862747)
      ·
        refine ⟨7879621293254539532794121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5253080862169693021862747 7879621293254539532794121)
        ·
          refine ⟨5909715969940904649595591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7879621293254539532794121 5909715969940904649595591)
          ·
            refine ⟨8864573954911356974393387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5909715969940904649595591 8864573954911356974393387)
            ·
              refine ⟨13296860932367035461590081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8864573954911356974393387 13296860932367035461590081)
              ·
                refine ⟨9972645699275276596192561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13296860932367035461590081 9972645699275276596192561)
                ·
                  refine ⟨7479484274456457447144421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9972645699275276596192561 7479484274456457447144421)
                  ·
                    refine ⟨1402403301460585771339579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7479484274456457447144421 1402403301460585771339579)
                    ·
                      rfl

theorem cell22_4096756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4096756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096756 prefixEnd_4096756 := by exact prefixLift 4096756
  have htrace : WordTrace (prefixWord ++ tailWord_4096756) baseStart_4096756 baseEnd_4096756 := by
    simpa [prefixWord, tailWord_4096756, baseEnd_4096756] using wordTrace_append hprefix tailTrace_4096756
  have hstable : (prefixWord ++ tailWord_4096756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096756).length < 2 ^ (prefixWord ++ tailWord_4096756).sum := by decide
  have hdescent : baseEnd_4096756 < baseStart_4096756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096765 : List Nat := [1, 4, 1, 1, 1, 1, 4, 4, 5]
def baseStart_4096765 : Nat := 118140960795 + 4096765 * 2 ^ 59
def prefixEnd_4096765 : Nat := 4983230072969 + 3 ^ 40 * 4096765 * 2
def baseEnd_4096765 : Nat := 467468794114837582621517

theorem tailTrace_4096765 : CollatzResearch.WordTrace tailWord_4096765 prefixEnd_4096765 467468794114837582621517 := by
  unfold tailWord_4096765
  simp only [CollatzResearch.WordTrace]
  refine ⟨149421295003127551603395749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99614196668751701068930499 149421295003127551603395749)
  ·
    refine ⟨28016492813086415925636703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149421295003127551603395749 28016492813086415925636703)
    ·
      refine ⟨42024739219629623888455055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28016492813086415925636703 42024739219629623888455055)
      ·
        refine ⟨63037108829444435832682583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42024739219629623888455055 63037108829444435832682583)
        ·
          refine ⟨94555663244166653749023875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63037108829444435832682583 94555663244166653749023875)
          ·
            refine ⟨141833494866249980623535813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94555663244166653749023875 141833494866249980623535813)
            ·
              refine ⟨26593780287421871366912965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141833494866249980623535813 26593780287421871366912965)
              ·
                refine ⟨4986333803891600881296181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26593780287421871366912965 4986333803891600881296181)
                ·
                  refine ⟨467468794114837582621517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4986333803891600881296181 467468794114837582621517)
                  ·
                    rfl

theorem cell22_4096765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_4096765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096765 prefixEnd_4096765 := by exact prefixLift 4096765
  have htrace : WordTrace (prefixWord ++ tailWord_4096765) baseStart_4096765 baseEnd_4096765 := by
    simpa [prefixWord, tailWord_4096765, baseEnd_4096765] using wordTrace_append hprefix tailTrace_4096765
  have hstable : (prefixWord ++ tailWord_4096765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096765).length < 2 ^ (prefixWord ++ tailWord_4096765).sum := by decide
  have hdescent : baseEnd_4096765 < baseStart_4096765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096820 : List Nat := [2, 5, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_4096820 : Nat := 118140960795 + 4096820 * 2 ^ 59
def prefixEnd_4096820 : Nat := 4983230072969 + 3 ^ 40 * 4096820 * 2
def baseEnd_4096820 : Nat := 1402425209968510937739383

theorem tailTrace_4096820 : CollatzResearch.WordTrace tailWord_4096820 prefixEnd_4096820 1402425209968510937739383 := by
  unfold tailWord_4096820
  simp only [CollatzResearch.WordTrace]
  refine ⟨74711650508964147998323957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99615534011952197331098609 74711650508964147998323957)
  ·
    refine ⟨7004217235215388874842871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74711650508964147998323957 7004217235215388874842871)
    ·
      refine ⟨10506325852823083312264307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7004217235215388874842871 10506325852823083312264307)
      ·
        refine ⟨15759488779234624968396461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10506325852823083312264307 15759488779234624968396461)
        ·
          refine ⟨5909808292212984363148673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15759488779234624968396461 5909808292212984363148673)
          ·
            refine ⟨4432356219159738272361505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5909808292212984363148673 4432356219159738272361505)
            ·
              refine ⟨3324267164369803704271129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4432356219159738272361505 3324267164369803704271129)
              ·
                refine ⟨2493200373277352778203347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3324267164369803704271129 2493200373277352778203347)
                ·
                  refine ⟨3739800559916029167305021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2493200373277352778203347 3739800559916029167305021)
                  ·
                    refine ⟨1402425209968510937739383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3739800559916029167305021 1402425209968510937739383)
                    ·
                      rfl

theorem cell22_4096820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_4096820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096820 prefixEnd_4096820 := by exact prefixLift 4096820
  have htrace : WordTrace (prefixWord ++ tailWord_4096820) baseStart_4096820 baseEnd_4096820 := by
    simpa [prefixWord, tailWord_4096820, baseEnd_4096820] using wordTrace_append hprefix tailTrace_4096820
  have hstable : (prefixWord ++ tailWord_4096820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096820).length < 2 ^ (prefixWord ++ tailWord_4096820).sum := by decide
  have hdescent : baseEnd_4096820 < baseStart_4096820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096840 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 1, 6]
def baseStart_4096840 : Nat := 118140960795 + 4096840 * 2 ^ 59
def prefixEnd_4096840 : Nat := 4983230072969 + 3 ^ 40 * 4096840 * 2
def baseEnd_4096840 : Nat := 1402432056377237552239321

theorem tailTrace_4096840 : CollatzResearch.WordTrace tailWord_4096840 prefixEnd_4096840 1402432056377237552239321 := by
  unfold tailWord_4096840
  simp only [CollatzResearch.WordTrace]
  refine ⟨74712015238927919706187987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99616020318570559608250649 74712015238927919706187987)
  ·
    refine ⟨112068022858391879559281981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74712015238927919706187987 112068022858391879559281981)
    ·
      refine ⟨42025508571896954834730743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112068022858391879559281981 42025508571896954834730743)
      ·
        refine ⟨63038262857845432252096115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42025508571896954834730743 63038262857845432252096115)
        ·
          refine ⟨94557394286768148378144173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63038262857845432252096115 94557394286768148378144173)
          ·
            refine ⟨35459022857538055641804065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94557394286768148378144173 35459022857538055641804065)
            ·
              refine ⟨26594267143153541731353049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35459022857538055641804065 26594267143153541731353049)
              ·
                refine ⟨19945700357365156298514787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26594267143153541731353049 19945700357365156298514787)
                ·
                  refine ⟨29918550536047734447772181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19945700357365156298514787 29918550536047734447772181)
                  ·
                    refine ⟨1402432056377237552239321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29918550536047734447772181 1402432056377237552239321)
                    ·
                      rfl

theorem cell22_4096840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_4096840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096840 prefixEnd_4096840 := by exact prefixLift 4096840
  have htrace : WordTrace (prefixWord ++ tailWord_4096840) baseStart_4096840 baseEnd_4096840 := by
    simpa [prefixWord, tailWord_4096840, baseEnd_4096840] using wordTrace_append hprefix tailTrace_4096840
  have hstable : (prefixWord ++ tailWord_4096840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096840).length < 2 ^ (prefixWord ++ tailWord_4096840).sum := by decide
  have hdescent : baseEnd_4096840 < baseStart_4096840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096857 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 2, 4]
def baseStart_4096857 : Nat := 118140960795 + 4096857 * 2 ^ 59
def prefixEnd_4096857 : Nat := 4983230072969 + 3 ^ 40 * 4096857 * 2
def baseEnd_4096857 : Nat := 1402437875824655174564269

theorem tailTrace_4096857 : CollatzResearch.WordTrace tailWord_4096857 prefixEnd_4096857 1402437875824655174564269 := by
  unfold tailWord_4096857
  simp only [CollatzResearch.WordTrace]
  refine ⟨149424650518794251315744825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99616433679196167543829883 149424650518794251315744825)
  ·
    refine ⟨112068487889095688486808619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149424650518794251315744825 112068487889095688486808619)
    ·
      refine ⟨168102731833643532730212929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112068487889095688486808619 168102731833643532730212929)
      ·
        refine ⟨126077048875232649547659697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168102731833643532730212929 126077048875232649547659697)
        ·
          refine ⟨94557786656424487160744773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126077048875232649547659697 94557786656424487160744773)
          ·
            refine ⟨17729584998079591342639645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94557786656424487160744773 17729584998079591342639645)
            ·
              refine ⟨6648594374279846753489867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17729584998079591342639645 6648594374279846753489867)
              ·
                refine ⟨9972891561419770130234801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6648594374279846753489867 9972891561419770130234801)
                ·
                  refine ⟨7479668671064827597676101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9972891561419770130234801 7479668671064827597676101)
                  ·
                    refine ⟨1402437875824655174564269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7479668671064827597676101 1402437875824655174564269)
                    ·
                      rfl

theorem cell22_4096857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_4096857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096857 prefixEnd_4096857 := by exact prefixLift 4096857
  have htrace : WordTrace (prefixWord ++ tailWord_4096857) baseStart_4096857 baseEnd_4096857 := by
    simpa [prefixWord, tailWord_4096857, baseEnd_4096857] using wordTrace_append hprefix tailTrace_4096857
  have hstable : (prefixWord ++ tailWord_4096857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096857).length < 2 ^ (prefixWord ++ tailWord_4096857).sum := by decide
  have hdescent : baseEnd_4096857 < baseStart_4096857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096904 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 3, 3]
def baseStart_4096904 : Nat := 118140960795 + 4096904 * 2 ^ 59
def prefixEnd_4096904 : Nat := 4983230072969 + 3 ^ 40 * 4096904 * 2
def baseEnd_4096904 : Nat := 1402453964885162718639125

theorem tailTrace_4096904 : CollatzResearch.WordTrace tailWord_4096904 prefixEnd_4096904 1402453964885162718639125 := by
  unfold tailWord_4096904
  simp only [CollatzResearch.WordTrace]
  refine ⟨74713182374811989171352883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99617576499749318895137177 74713182374811989171352883)
  ·
    refine ⟨112069773562217983757029325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74713182374811989171352883 112069773562217983757029325)
    ·
      refine ⟨42026165085831743908885997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112069773562217983757029325 42026165085831743908885997)
      ·
        refine ⟨15759811907186903965832249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42026165085831743908885997 15759811907186903965832249)
        ·
          refine ⟨11819858930390177974374187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15759811907186903965832249 11819858930390177974374187)
          ·
            refine ⟨17729788395585266961561281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11819858930390177974374187 17729788395585266961561281)
            ·
              refine ⟨13297341296688950221170961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17729788395585266961561281 13297341296688950221170961)
              ·
                refine ⟨9973005972516712665878221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13297341296688950221170961 9973005972516712665878221)
                ·
                  refine ⟨3739877239693767249704333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9973005972516712665878221 3739877239693767249704333)
                  ·
                    refine ⟨1402453964885162718639125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3739877239693767249704333 1402453964885162718639125)
                    ·
                      rfl

theorem cell22_4096904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_4096904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096904 prefixEnd_4096904 := by exact prefixLift 4096904
  have htrace : WordTrace (prefixWord ++ tailWord_4096904) baseStart_4096904 baseEnd_4096904 := by
    simpa [prefixWord, tailWord_4096904, baseEnd_4096904] using wordTrace_append hprefix tailTrace_4096904
  have hstable : (prefixWord ++ tailWord_4096904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096904).length < 2 ^ (prefixWord ++ tailWord_4096904).sum := by decide
  have hdescent : baseEnd_4096904 < baseStart_4096904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096915 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 4, 5]
def baseStart_4096915 : Nat := 118140960795 + 4096915 * 2 ^ 59
def prefixEnd_4096915 : Nat := 4983230072969 + 3 ^ 40 * 4096915 * 2
def baseEnd_4096915 : Nat := 1402457730409962356614091

theorem tailTrace_4096915 : CollatzResearch.WordTrace tailWord_4096915 prefixEnd_4096915 1402457730409962356614091 := by
  unfold tailWord_4096915
  simp only [CollatzResearch.WordTrace]
  refine ⟨149426765952584127221356199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99617843968389418147570799 149426765952584127221356199)
  ·
    refine ⟨224140148928876190832034299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149426765952584127221356199 224140148928876190832034299)
    ·
      refine ⟨336210223393314286248051449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224140148928876190832034299 336210223393314286248051449)
      ·
        refine ⟨252157667544985714686038587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336210223393314286248051449 252157667544985714686038587)
        ·
          refine ⟨378236501317478572029057881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252157667544985714686038587 378236501317478572029057881)
          ·
            refine ⟨283677375988108929021793411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378236501317478572029057881 283677375988108929021793411)
            ·
              refine ⟨425516063982163393532690117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283677375988108929021793411 425516063982163393532690117)
              ·
                refine ⟨79784261996655636287379397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425516063982163393532690117 79784261996655636287379397)
                ·
                  refine ⟨14959549124372931803883637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79784261996655636287379397 14959549124372931803883637)
                  ·
                    refine ⟨1402457730409962356614091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14959549124372931803883637 1402457730409962356614091)
                    ·
                      rfl

theorem cell22_4096915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 5].length) (baseStart_4096915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096915 prefixEnd_4096915 := by exact prefixLift 4096915
  have htrace : WordTrace (prefixWord ++ tailWord_4096915) baseStart_4096915 baseEnd_4096915 := by
    simpa [prefixWord, tailWord_4096915, baseEnd_4096915] using wordTrace_append hprefix tailTrace_4096915
  have hstable : (prefixWord ++ tailWord_4096915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096915).length < 2 ^ (prefixWord ++ tailWord_4096915).sum := by decide
  have hdescent : baseEnd_4096915 < baseStart_4096915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096977 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 1, 5]
def baseStart_4096977 : Nat := 118140960795 + 4096977 * 2 ^ 59
def prefixEnd_4096977 : Nat := 4983230072969 + 3 ^ 40 * 4096977 * 2
def baseEnd_4096977 : Nat := 1402478954277014861563901

theorem tailTrace_4096977 : CollatzResearch.WordTrace tailWord_4096977 prefixEnd_4096977 1402478954277014861563901 := by
  unfold tailWord_4096977
  simp only [CollatzResearch.WordTrace]
  refine ⟨149429027278359511810113185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99619351518906341206742123 149429027278359511810113185)
  ·
    refine ⟨112071770458769633857584889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149429027278359511810113185 112071770458769633857584889)
    ·
      refine ⟨84053827844077225393188667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112071770458769633857584889 84053827844077225393188667)
      ·
        refine ⟨126080741766115838089783001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84053827844077225393188667 126080741766115838089783001)
        ·
          refine ⟨94560556324586878567337251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126080741766115838089783001 94560556324586878567337251)
          ·
            refine ⟨141840834486880317851005877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94560556324586878567337251 141840834486880317851005877)
            ·
              refine ⟨13297578233145029798531801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141840834486880317851005877 13297578233145029798531801)
              ·
                refine ⟨9973183674858772348898851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13297578233145029798531801 9973183674858772348898851)
                ·
                  refine ⟨14959775512288158523348277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9973183674858772348898851 14959775512288158523348277)
                  ·
                    refine ⟨1402478954277014861563901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14959775512288158523348277 1402478954277014861563901)
                    ·
                      rfl

theorem cell22_4096977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_4096977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4096977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4096977 prefixEnd_4096977 := by exact prefixLift 4096977
  have htrace : WordTrace (prefixWord ++ tailWord_4096977) baseStart_4096977 baseEnd_4096977 := by
    simpa [prefixWord, tailWord_4096977, baseEnd_4096977] using wordTrace_append hprefix tailTrace_4096977
  have hstable : (prefixWord ++ tailWord_4096977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096977).length < 2 ^ (prefixWord ++ tailWord_4096977).sum := by decide
  have hdescent : baseEnd_4096977 < baseStart_4096977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097007 : List Nat := [1, 1, 2, 1, 4, 3, 3, 7]
def baseStart_4097007 : Nat := 118140960795 + 4097007 * 2 ^ 59
def prefixEnd_4097007 : Nat := 4983230072969 + 3 ^ 40 * 4097007 * 2
def baseEnd_4097007 : Nat := 155832135987789420368201

theorem tailTrace_4097007 : CollatzResearch.WordTrace tailWord_4097007 prefixEnd_4097007 155832135987789420368201 := by
  unfold tailWord_4097007
  simp only [CollatzResearch.WordTrace]
  refine ⟨149430121468250826933705275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99620080978833884622470183 149430121468250826933705275)
  ·
    refine ⟨224145182202376240400557913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149430121468250826933705275 224145182202376240400557913)
    ·
      refine ⟨168108886651782180300418435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224145182202376240400557913 168108886651782180300418435)
      ·
        refine ⟨252163329977673270450627653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168108886651782180300418435 252163329977673270450627653)
        ·
          refine ⟨47280624370813738209492685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252163329977673270450627653 47280624370813738209492685)
          ·
            refine ⟨17730234139055151828559757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47280624370813738209492685 17730234139055151828559757)
            ·
              refine ⟨6648837802145681935709909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17730234139055151828559757 6648837802145681935709909)
              ·
                refine ⟨155832135987789420368201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6648837802145681935709909 155832135987789420368201)
                ·
                  rfl

theorem cell22_4097007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 7].length) (baseStart_4097007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097007 prefixEnd_4097007 := by exact prefixLift 4097007
  have htrace : WordTrace (prefixWord ++ tailWord_4097007) baseStart_4097007 baseEnd_4097007 := by
    simpa [prefixWord, tailWord_4097007, baseEnd_4097007] using wordTrace_append hprefix tailTrace_4097007
  have hstable : (prefixWord ++ tailWord_4097007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097007).length < 2 ^ (prefixWord ++ tailWord_4097007).sum := by decide
  have hdescent : baseEnd_4097007 < baseStart_4097007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097067 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 2, 5]
def baseStart_4097067 : Nat := 118140960795 + 4097067 * 2 ^ 59
def prefixEnd_4097067 : Nat := 4983230072969 + 3 ^ 40 * 4097067 * 2
def baseEnd_4097067 : Nat := 1402509763116284626813625

theorem tailTrace_4097067 : CollatzResearch.WordTrace tailWord_4097067 prefixEnd_4097067 1402509763116284626813625 := by
  unfold tailWord_4097067
  simp only [CollatzResearch.WordTrace]
  refine ⟨149432309848033457180889455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99621539898688971453926303 149432309848033457180889455)
  ·
    refine ⟨224148464772050185771334183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149432309848033457180889455 224148464772050185771334183)
    ·
      refine ⟨336222697158075278657001275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224148464772050185771334183 336222697158075278657001275)
      ·
        refine ⟨504334045737112917985501913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336222697158075278657001275 504334045737112917985501913)
        ·
          refine ⟨378250534302834688489126435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504334045737112917985501913 378250534302834688489126435)
          ·
            refine ⟨567375801454252032733689653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378250534302834688489126435 567375801454252032733689653)
            ·
              refine ⟨53191481386336128068783405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 567375801454252032733689653 53191481386336128068783405)
              ·
                refine ⟨19946805519876048025793777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53191481386336128068783405 19946805519876048025793777)
                ·
                  refine ⟨14960104139907036019345333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19946805519876048025793777 14960104139907036019345333)
                  ·
                    refine ⟨1402509763116284626813625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14960104139907036019345333 1402509763116284626813625)
                    ·
                      rfl

theorem cell22_4097067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 5].length) (baseStart_4097067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097067 prefixEnd_4097067 := by exact prefixLift 4097067
  have htrace : WordTrace (prefixWord ++ tailWord_4097067) baseStart_4097067 baseEnd_4097067 := by
    simpa [prefixWord, tailWord_4097067, baseEnd_4097067] using wordTrace_append hprefix tailTrace_4097067
  have hstable : (prefixWord ++ tailWord_4097067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097067).length < 2 ^ (prefixWord ++ tailWord_4097067).sum := by decide
  have hdescent : baseEnd_4097067 < baseStart_4097067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097133 : List Nat := [1, 5, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_4097133 : Nat := 118140960795 + 4097133 * 2 ^ 59
def prefixEnd_4097133 : Nat := 4983230072969 + 3 ^ 40 * 4097133 * 2
def baseEnd_4097133 : Nat := 1402532356265082454663423

theorem tailTrace_4097133 : CollatzResearch.WordTrace tailWord_4097133 prefixEnd_4097133 1402532356265082454663423 := by
  unfold tailWord_4097133
  simp only [CollatzResearch.WordTrace]
  refine ⟨149434717065794350452792053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99623144710529566968528035 149434717065794350452792053)
  ·
    refine ⟨14009504724918220354949255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149434717065794350452792053 14009504724918220354949255)
    ·
      refine ⟨21014257087377330532423883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14009504724918220354949255 21014257087377330532423883)
      ·
        refine ⟨31521385631065995798635825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21014257087377330532423883 31521385631065995798635825)
        ·
          refine ⟨23641039223299496848976869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31521385631065995798635825 23641039223299496848976869)
          ·
            refine ⟨4432694854368655659183163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23641039223299496848976869 4432694854368655659183163)
            ·
              refine ⟨6649042281552983488774745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4432694854368655659183163 6649042281552983488774745)
              ·
                refine ⟨4986781711164737616581059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6649042281552983488774745 4986781711164737616581059)
                ·
                  refine ⟨7480172566747106424871589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4986781711164737616581059 7480172566747106424871589)
                  ·
                    refine ⟨1402532356265082454663423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7480172566747106424871589 1402532356265082454663423)
                    ·
                      rfl

theorem cell22_4097133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_4097133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097133 prefixEnd_4097133 := by exact prefixLift 4097133
  have htrace : WordTrace (prefixWord ++ tailWord_4097133) baseStart_4097133 baseEnd_4097133 := by
    simpa [prefixWord, tailWord_4097133, baseEnd_4097133] using wordTrace_append hprefix tailTrace_4097133
  have hstable : (prefixWord ++ tailWord_4097133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097133).length < 2 ^ (prefixWord ++ tailWord_4097133).sum := by decide
  have hdescent : baseEnd_4097133 < baseStart_4097133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097144 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 2, 4]
def baseStart_4097144 : Nat := 118140960795 + 4097144 * 2 ^ 59
def prefixEnd_4097144 : Nat := 4983230072969 + 3 ^ 40 * 4097144 * 2
def baseEnd_4097144 : Nat := 1402536121789882092638389

theorem tailTrace_4097144 : CollatzResearch.WordTrace tailWord_4097144 prefixEnd_4097144 1402536121789882092638389 := by
  unfold tailWord_4097144
  simp only [CollatzResearch.WordTrace]
  refine ⟨74717559134377249665721243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99623412179169666220961657 74717559134377249665721243)
  ·
    refine ⟨112076338701565874498581865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74717559134377249665721243 112076338701565874498581865)
    ·
      refine ⟨84057254026174405873936399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112076338701565874498581865 84057254026174405873936399)
      ·
        refine ⟨126085881039261608810904599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84057254026174405873936399 126085881039261608810904599)
        ·
          refine ⟨189128821558892413216356899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126085881039261608810904599 189128821558892413216356899)
          ·
            refine ⟨283693232338338619824535349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189128821558892413216356899 283693232338338619824535349)
            ·
              refine ⟨26596240531719245608550189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283693232338338619824535349 26596240531719245608550189)
              ·
                refine ⟨9973590199394717103206321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26596240531719245608550189 9973590199394717103206321)
                ·
                  refine ⟨7480192649546037827404741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9973590199394717103206321 7480192649546037827404741)
                  ·
                    refine ⟨1402536121789882092638389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7480192649546037827404741 1402536121789882092638389)
                    ·
                      rfl

theorem cell22_4097144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_4097144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097144 prefixEnd_4097144 := by exact prefixLift 4097144
  have htrace : WordTrace (prefixWord ++ tailWord_4097144) baseStart_4097144 baseEnd_4097144 := by
    simpa [prefixWord, tailWord_4097144, baseEnd_4097144] using wordTrace_append hprefix tailTrace_4097144
  have hstable : (prefixWord ++ tailWord_4097144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097144).length < 2 ^ (prefixWord ++ tailWord_4097144).sum := by decide
  have hdescent : baseEnd_4097144 < baseStart_4097144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097176 : List Nat := [2, 1, 2, 4, 2, 3, 1, 7]
def baseStart_4097176 : Nat := 118140960795 + 4097176 * 2 ^ 59
def prefixEnd_4097176 : Nat := 4983230072969 + 3 ^ 40 * 4097176 * 2
def baseEnd_4097176 : Nat := 155838564004871630648699

theorem tailTrace_4097176 : CollatzResearch.WordTrace tailWord_4097176 prefixEnd_4097176 155838564004871630648699 := by
  unfold tailWord_4097176
  simp only [CollatzResearch.WordTrace]
  refine ⟨74718142702319284398303691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99624190269759045864404921 74718142702319284398303691)
  ·
    refine ⟨112077214053478926597455537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74718142702319284398303691 112077214053478926597455537)
    ·
      refine ⟨84057910540109194948091653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112077214053478926597455537 84057910540109194948091653)
      ·
        refine ⟨15760858226270474052767185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84057910540109194948091653 15760858226270474052767185)
        ·
          refine ⟨11820643669702855539575389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15760858226270474052767185 11820643669702855539575389)
          ·
            refine ⟨4432741376138570827340771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11820643669702855539575389 4432741376138570827340771)
            ·
              refine ⟨6649112064207856241011157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4432741376138570827340771 6649112064207856241011157)
              ·
                refine ⟨155838564004871630648699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6649112064207856241011157 155838564004871630648699)
                ·
                  rfl

theorem cell22_4097176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 7].length) (baseStart_4097176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097176 prefixEnd_4097176 := by exact prefixLift 4097176
  have htrace : WordTrace (prefixWord ++ tailWord_4097176) baseStart_4097176 baseEnd_4097176 := by
    simpa [prefixWord, tailWord_4097176, baseEnd_4097176] using wordTrace_append hprefix tailTrace_4097176
  have hstable : (prefixWord ++ tailWord_4097176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097176).length < 2 ^ (prefixWord ++ tailWord_4097176).sum := by decide
  have hdescent : baseEnd_4097176 < baseStart_4097176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097339 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 13]
def baseStart_4097339 : Nat := 118140960795 + 4097339 * 2 ^ 59
def prefixEnd_4097339 : Nat := 4983230072969 + 3 ^ 40 * 4097339 * 2
def baseEnd_4097339 : Nat := 467534291424988861337597

theorem tailTrace_4097339 : CollatzResearch.WordTrace tailWord_4097339 prefixEnd_4097339 467534291424988861337597 := by
  unfold tailWord_4097339
  simp only [CollatzResearch.WordTrace]
  refine ⟨149442230503048047634791071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99628153668698698423194047 149442230503048047634791071)
  ·
    refine ⟨224163345754572071452186607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149442230503048047634791071 224163345754572071452186607)
    ·
      refine ⟨336245018631858107178279911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224163345754572071452186607 336245018631858107178279911)
      ·
        refine ⟨504367527947787160767419867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336245018631858107178279911 504367527947787160767419867)
        ·
          refine ⟨756551291921680741151129801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504367527947787160767419867 756551291921680741151129801)
          ·
            refine ⟨567413468941260555863347351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756551291921680741151129801 567413468941260555863347351)
            ·
              refine ⟨851120203411890833795021027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567413468941260555863347351 851120203411890833795021027)
              ·
                refine ⟨1276680305117836250692531541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851120203411890833795021027 1276680305117836250692531541)
                ·
                  refine ⟨467534291424988861337597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 1276680305117836250692531541 467534291424988861337597)
                  ·
                    rfl

theorem cell22_4097339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 13].length) (baseStart_4097339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097339 prefixEnd_4097339 := by exact prefixLift 4097339
  have htrace : WordTrace (prefixWord ++ tailWord_4097339) baseStart_4097339 baseEnd_4097339 := by
    simpa [prefixWord, tailWord_4097339, baseEnd_4097339] using wordTrace_append hprefix tailTrace_4097339
  have hstable : (prefixWord ++ tailWord_4097339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097339).length < 2 ^ (prefixWord ++ tailWord_4097339).sum := by decide
  have hdescent : baseEnd_4097339 < baseStart_4097339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097390 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 7]
def baseStart_4097390 : Nat := 118140960795 + 4097390 * 2 ^ 59
def prefixEnd_4097390 : Nat := 4983230072969 + 3 ^ 40 * 4097390 * 2
def baseEnd_4097390 : Nat := 467540110872406483662545

theorem tailTrace_4097390 : CollatzResearch.WordTrace tailWord_4097390 prefixEnd_4097390 467540110872406483662545 := by
  unfold tailWord_4097390
  simp only [CollatzResearch.WordTrace]
  refine ⟨18680511328232910418112203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99629393750575522229931749 18680511328232910418112203)
  ·
    refine ⟨28020766992349365627168305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18680511328232910418112203 28020766992349365627168305)
    ·
      refine ⟨21015575244262024220376229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28020766992349365627168305 21015575244262024220376229)
      ·
        refine ⟨3940420358299129541320543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21015575244262024220376229 3940420358299129541320543)
        ·
          refine ⟨5910630537448694311980815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3940420358299129541320543 5910630537448694311980815)
          ·
            refine ⟨8865945806173041467971223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5910630537448694311980815 8865945806173041467971223)
            ·
              refine ⟨13298918709259562201956835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8865945806173041467971223 13298918709259562201956835)
              ·
                refine ⟨19948378063889343302935253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13298918709259562201956835 19948378063889343302935253)
                ·
                  refine ⟨467540110872406483662545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19948378063889343302935253 467540110872406483662545)
                  ·
                    rfl

theorem cell22_4097390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_4097390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097390 prefixEnd_4097390 := by exact prefixLift 4097390
  have htrace : WordTrace (prefixWord ++ tailWord_4097390) baseStart_4097390 baseEnd_4097390 := by
    simpa [prefixWord, tailWord_4097390, baseEnd_4097390] using wordTrace_append hprefix tailTrace_4097390
  have hstable : (prefixWord ++ tailWord_4097390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097390).length < 2 ^ (prefixWord ++ tailWord_4097390).sum := by decide
  have hdescent : baseEnd_4097390 < baseStart_4097390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097401 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 6]
def baseStart_4097401 : Nat := 118140960795 + 4097401 * 2 ^ 59
def prefixEnd_4097401 : Nat := 4983230072969 + 3 ^ 40 * 4097401 * 2
def baseEnd_4097401 : Nat := 467541366047339696320867

theorem tailTrace_4097401 : CollatzResearch.WordTrace tailWord_4097401 prefixEnd_4097401 467541366047339696320867 := by
  unfold tailWord_4097401
  simp only [CollatzResearch.WordTrace]
  refine ⟨149444491828823432223548057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99629661219215621482365371 149444491828823432223548057)
  ·
    refine ⟨112083368871617574167661043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149444491828823432223548057 112083368871617574167661043)
    ·
      refine ⟨168125053307426361251491565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112083368871617574167661043 168125053307426361251491565)
      ·
        refine ⟨63046894990284885469309337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168125053307426361251491565 63046894990284885469309337)
        ·
          refine ⟨47285171242713664101982003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63046894990284885469309337 47285171242713664101982003)
          ·
            refine ⟨70927756864070496152973005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47285171242713664101982003 70927756864070496152973005)
            ·
              refine ⟨26597908824026436057364877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70927756864070496152973005 26597908824026436057364877)
              ·
                refine ⟨9974215809009913521511829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26597908824026436057364877 9974215809009913521511829)
                ·
                  refine ⟨467541366047339696320867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9974215809009913521511829 467541366047339696320867)
                  ·
                    rfl

theorem cell22_4097401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 6].length) (baseStart_4097401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097401 prefixEnd_4097401 := by exact prefixLift 4097401
  have htrace : WordTrace (prefixWord ++ tailWord_4097401) baseStart_4097401 baseEnd_4097401 := by
    simpa [prefixWord, tailWord_4097401, baseEnd_4097401] using wordTrace_append hprefix tailTrace_4097401
  have hstable : (prefixWord ++ tailWord_4097401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097401).length < 2 ^ (prefixWord ++ tailWord_4097401).sum := by decide
  have hdescent : baseEnd_4097401 < baseStart_4097401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097433 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 4, 3]
def baseStart_4097433 : Nat := 118140960795 + 4097433 * 2 ^ 59
def prefixEnd_4097433 : Nat := 4983230072969 + 3 ^ 40 * 4097433 * 2
def baseEnd_4097433 : Nat := 1402635052395981672162503

theorem tailTrace_4097433 : CollatzResearch.WordTrace tailWord_4097433 prefixEnd_4097433 1402635052395981672162503 := by
  unfold tailWord_4097433
  simp only [CollatzResearch.WordTrace]
  refine ⟨149445658964707501688712953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99630439309805001125808635 149445658964707501688712953)
  ·
    refine ⟨112084244223530626266534715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149445658964707501688712953 112084244223530626266534715)
    ·
      refine ⟨168126366335295939399802073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112084244223530626266534715 168126366335295939399802073)
      ·
        refine ⟨126094774751471954549851555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168126366335295939399802073 126094774751471954549851555)
        ·
          refine ⟨189142162127207931824777333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126094774751471954549851555 189142162127207931824777333)
          ·
            refine ⟨17732077699425743608572875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189142162127207931824777333 17732077699425743608572875)
            ·
              refine ⟨26598116549138615412859313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17732077699425743608572875 26598116549138615412859313)
              ·
                refine ⟨19948587411853961559644485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26598116549138615412859313 19948587411853961559644485)
                ·
                  refine ⟨3740360139722617792433341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19948587411853961559644485 3740360139722617792433341)
                  ·
                    refine ⟨1402635052395981672162503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3740360139722617792433341 1402635052395981672162503)
                    ·
                      rfl

theorem cell22_4097433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 3].length) (baseStart_4097433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097433 prefixEnd_4097433 := by exact prefixLift 4097433
  have htrace : WordTrace (prefixWord ++ tailWord_4097433) baseStart_4097433 baseEnd_4097433 := by
    simpa [prefixWord, tailWord_4097433, baseEnd_4097433] using wordTrace_append hprefix tailTrace_4097433
  have hstable : (prefixWord ++ tailWord_4097433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097433).length < 2 ^ (prefixWord ++ tailWord_4097433).sum := by decide
  have hdescent : baseEnd_4097433 < baseStart_4097433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097512 : List Nat := [2, 1, 4, 1, 1, 2, 3, 4, 1, 3]
def baseStart_4097512 : Nat := 118140960795 + 4097512 * 2 ^ 59
def prefixEnd_4097512 : Nat := 4983230072969 + 3 ^ 40 * 4097512 * 2
def baseEnd_4097512 : Nat := 1402662095710451799437261

theorem tailTrace_4097512 : CollatzResearch.WordTrace tailWord_4097512 prefixEnd_4097512 1402662095710451799437261 := by
  unfold tailWord_4097512
  simp only [CollatzResearch.WordTrace]
  refine ⟨74724270165710649090419395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99632360220947532120559193 74724270165710649090419395)
  ·
    refine ⟨112086405248565973635629093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74724270165710649090419395 112086405248565973635629093)
    ·
      refine ⟨21016200984106120056680455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112086405248565973635629093 21016200984106120056680455)
      ·
        refine ⟨31524301476159180085020683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21016200984106120056680455 31524301476159180085020683)
        ·
          refine ⟨47286452214238770127531025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31524301476159180085020683 47286452214238770127531025)
          ·
            refine ⟨35464839160679077595648269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47286452214238770127531025 35464839160679077595648269)
            ·
              refine ⟨13299314685254654098368101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35464839160679077595648269 13299314685254654098368101)
              ·
                refine ⟨2493621503485247643444019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13299314685254654098368101 2493621503485247643444019)
                ·
                  refine ⟨3740432255227871465166029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2493621503485247643444019 3740432255227871465166029)
                  ·
                    refine ⟨1402662095710451799437261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3740432255227871465166029 1402662095710451799437261)
                    ·
                      rfl

theorem cell22_4097512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_4097512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097512 prefixEnd_4097512 := by exact prefixLift 4097512
  have htrace : WordTrace (prefixWord ++ tailWord_4097512) baseStart_4097512 baseEnd_4097512 := by
    simpa [prefixWord, tailWord_4097512, baseEnd_4097512] using wordTrace_append hprefix tailTrace_4097512
  have hstable : (prefixWord ++ tailWord_4097512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097512).length < 2 ^ (prefixWord ++ tailWord_4097512).sum := by decide
  have hdescent : baseEnd_4097512 < baseStart_4097512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097555 : List Nat := [1, 1, 1, 2, 1, 7, 1, 3, 1, 4]
def baseStart_4097555 : Nat := 118140960795 + 4097555 * 2 ^ 59
def prefixEnd_4097555 : Nat := 4983230072969 + 3 ^ 40 * 4097555 * 2
def baseEnd_4097555 : Nat := 1402676815489214020612129

theorem tailTrace_4097555 : CollatzResearch.WordTrace tailWord_4097555 prefixEnd_4097555 1402676815489214020612129 := by
  unfold tailWord_4097555
  simp only [CollatzResearch.WordTrace]
  refine ⟨149450108670265516524654119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99633405780177011016436079 149450108670265516524654119)
  ·
    refine ⟨224175163005398274786981179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149450108670265516524654119 224175163005398274786981179)
    ·
      refine ⟨336262744508097412180471769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224175163005398274786981179 336262744508097412180471769)
      ·
        refine ⟨252197058381073059135353827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336262744508097412180471769 252197058381073059135353827)
        ·
          refine ⟨378295587571609588703030741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252197058381073059135353827 378295587571609588703030741)
          ·
            refine ⟨8866302833709599735227283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 378295587571609588703030741 8866302833709599735227283)
            ·
              refine ⟨13299454250564399602840925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8866302833709599735227283 13299454250564399602840925)
              ·
                refine ⟨4987295343961649851065347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13299454250564399602840925 4987295343961649851065347)
                ·
                  refine ⟨7480943015942474776598021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4987295343961649851065347 7480943015942474776598021)
                  ·
                    refine ⟨1402676815489214020612129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7480943015942474776598021 1402676815489214020612129)
                    ·
                      rfl

theorem cell22_4097555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 4].length) (baseStart_4097555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097555 prefixEnd_4097555 := by exact prefixLift 4097555
  have htrace : WordTrace (prefixWord ++ tailWord_4097555) baseStart_4097555 baseEnd_4097555 := by
    simpa [prefixWord, tailWord_4097555, baseEnd_4097555] using wordTrace_append hprefix tailTrace_4097555
  have hstable : (prefixWord ++ tailWord_4097555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097555).length < 2 ^ (prefixWord ++ tailWord_4097555).sum := by decide
  have hdescent : baseEnd_4097555 < baseStart_4097555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097658 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_4097658 : Nat := 118140960795 + 4097658 * 2 ^ 59
def prefixEnd_4097658 : Nat := 4983230072969 + 3 ^ 40 * 4097658 * 2
def baseEnd_4097658 : Nat := 1402712074494156085286813

theorem tailTrace_4097658 : CollatzResearch.WordTrace tailWord_4097658 prefixEnd_4097658 1402712074494156085286813 := by
  unfold tailWord_4097658
  simp only [CollatzResearch.WordTrace]
  refine ⟨37363466347223091278913407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99635910259261576743769085 37363466347223091278913407)
  ·
    refine ⟨56045199520834636918370111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37363466347223091278913407 56045199520834636918370111)
    ·
      refine ⟨84067799281251955377555167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56045199520834636918370111 84067799281251955377555167)
      ·
        refine ⟨126101698921877933066332751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84067799281251955377555167 126101698921877933066332751)
        ·
          refine ⟨189152548382816899599499127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126101698921877933066332751 189152548382816899599499127)
          ·
            refine ⟨283728822574225349399248691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189152548382816899599499127 283728822574225349399248691)
            ·
              refine ⟨425593233861338024098873037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283728822574225349399248691 425593233861338024098873037)
              ·
                refine ⟨159597462698001759037077389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 425593233861338024098873037 159597462698001759037077389)
                ·
                  refine ⟨59849048511750659638904021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159597462698001759037077389 59849048511750659638904021)
                  ·
                    refine ⟨1402712074494156085286813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59849048511750659638904021 1402712074494156085286813)
                    ·
                      rfl

theorem cell22_4097658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_4097658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097658 prefixEnd_4097658 := by exact prefixLift 4097658
  have htrace : WordTrace (prefixWord ++ tailWord_4097658) baseStart_4097658 baseEnd_4097658 := by
    simpa [prefixWord, tailWord_4097658, baseEnd_4097658] using wordTrace_append hprefix tailTrace_4097658
  have hstable : (prefixWord ++ tailWord_4097658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097658).length < 2 ^ (prefixWord ++ tailWord_4097658).sum := by decide
  have hdescent : baseEnd_4097658 < baseStart_4097658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097692 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 2, 5]
def baseStart_4097692 : Nat := 118140960795 + 4097692 * 2 ^ 59
def prefixEnd_4097692 : Nat := 4983230072969 + 3 ^ 40 * 4097692 * 2
def baseEnd_4097692 : Nat := 1402723713388991329936709

theorem tailTrace_4097692 : CollatzResearch.WordTrace tailWord_4097692 prefixEnd_4097692 1402723713388991329936709 := by
  unfold tailWord_4097692
  simp only [CollatzResearch.WordTrace]
  refine ⟨74727552735384594461195665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99636736980512792614927553 74727552735384594461195665)
  ·
    refine ⟨56045664551538445845896749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74727552735384594461195665 56045664551538445845896749)
    ·
      refine ⟨21017124206826917192211281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56045664551538445845896749 21017124206826917192211281)
      ·
        refine ⟨15762843155120187894158461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21017124206826917192211281 15762843155120187894158461)
        ·
          refine ⟨5911066183170070460309423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15762843155120187894158461 5911066183170070460309423)
          ·
            refine ⟨8866599274755105690464135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911066183170070460309423 8866599274755105690464135)
            ·
              refine ⟨13299898912132658535696203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8866599274755105690464135 13299898912132658535696203)
              ·
                refine ⟨19949848368198987803544305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13299898912132658535696203 19949848368198987803544305)
                ·
                  refine ⟨14962386276149240852658229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19949848368198987803544305 14962386276149240852658229)
                  ·
                    refine ⟨1402723713388991329936709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14962386276149240852658229 1402723713388991329936709)
                    ·
                      rfl

theorem cell22_4097692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_4097692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097692 prefixEnd_4097692 := by exact prefixLift 4097692
  have htrace : WordTrace (prefixWord ++ tailWord_4097692) baseStart_4097692 baseEnd_4097692 := by
    simpa [prefixWord, tailWord_4097692, baseEnd_4097692] using wordTrace_append hprefix tailTrace_4097692
  have hstable : (prefixWord ++ tailWord_4097692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097692).length < 2 ^ (prefixWord ++ tailWord_4097692).sum := by decide
  have hdescent : baseEnd_4097692 < baseStart_4097692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097722 : List Nat := [3, 1, 1, 1, 2, 4, 1, 5, 4]
def baseStart_4097722 : Nat := 118140960795 + 4097722 * 2 ^ 59
def prefixEnd_4097722 : Nat := 4983230072969 + 3 ^ 40 * 4097722 * 2
def baseEnd_4097722 : Nat := 467577994334027083895539

theorem tailTrace_4097722 : CollatzResearch.WordTrace tailWord_4097722 prefixEnd_4097722 467577994334027083895539 := by
  unfold tailWord_4097722
  simp only [CollatzResearch.WordTrace]
  refine ⟨37364049915165126011495855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99637466440440336030655613 37364049915165126011495855)
  ·
    refine ⟨56046074872747689017243783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37364049915165126011495855 56046074872747689017243783)
    ·
      refine ⟨84069112309121533525865675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56046074872747689017243783 84069112309121533525865675)
      ·
        refine ⟨126103668463682300288798513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84069112309121533525865675 126103668463682300288798513)
        ·
          refine ⟨94577751347761725216598885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126103668463682300288798513 94577751347761725216598885)
          ·
            refine ⟨17733328377705323478112291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94577751347761725216598885 17733328377705323478112291)
            ·
              refine ⟨26599992566557985217168437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17733328377705323478112291 26599992566557985217168437)
              ·
                refine ⟨2493749303114811114109541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26599992566557985217168437 2493749303114811114109541)
                ·
                  refine ⟨467577994334027083895539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2493749303114811114109541 467577994334027083895539)
                  ·
                    rfl

theorem cell22_4097722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_4097722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097722 prefixEnd_4097722 := by exact prefixLift 4097722
  have htrace : WordTrace (prefixWord ++ tailWord_4097722) baseStart_4097722 baseEnd_4097722 := by
    simpa [prefixWord, tailWord_4097722, baseEnd_4097722] using wordTrace_append hprefix tailTrace_4097722
  have hstable : (prefixWord ++ tailWord_4097722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097722).length < 2 ^ (prefixWord ++ tailWord_4097722).sum := by decide
  have hdescent : baseEnd_4097722 < baseStart_4097722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097724 : List Nat := [2, 2, 2, 3, 1, 2, 4, 1, 1, 4]
def baseStart_4097724 : Nat := 118140960795 + 4097724 * 2 ^ 59
def prefixEnd_4097724 : Nat := 4983230072969 + 3 ^ 40 * 4097724 * 2
def baseEnd_4097724 : Nat := 1402734667642953913136611

theorem tailTrace_4097724 : CollatzResearch.WordTrace tailWord_4097724 prefixEnd_4097724 1402734667642953913136611 := by
  unfold tailWord_4097724
  simp only [CollatzResearch.WordTrace]
  refine ⟨74728136303326629193778113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99637515071102172258370817 74728136303326629193778113)
  ·
    refine ⟨56046102227494971895333585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74728136303326629193778113 56046102227494971895333585)
    ·
      refine ⟨42034576670621228921500189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56046102227494971895333585 42034576670621228921500189)
      ·
        refine ⟨15762966251482960845562571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42034576670621228921500189 15762966251482960845562571)
        ·
          refine ⟨23644449377224441268343857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15762966251482960845562571 23644449377224441268343857)
          ·
            refine ⟨17733337032918330951257893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23644449377224441268343857 17733337032918330951257893)
            ·
              refine ⟨3325000693672187053360855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17733337032918330951257893 3325000693672187053360855)
              ·
                refine ⟨4987501040508280580041283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3325000693672187053360855 4987501040508280580041283)
                ·
                  refine ⟨7481251560762420870061925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4987501040508280580041283 7481251560762420870061925)
                  ·
                    refine ⟨1402734667642953913136611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7481251560762420870061925 1402734667642953913136611)
                    ·
                      rfl

theorem cell22_4097724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_4097724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097724 prefixEnd_4097724 := by exact prefixLift 4097724
  have htrace : WordTrace (prefixWord ++ tailWord_4097724) baseStart_4097724 baseEnd_4097724 := by
    simpa [prefixWord, tailWord_4097724, baseEnd_4097724] using wordTrace_append hprefix tailTrace_4097724
  have hstable : (prefixWord ++ tailWord_4097724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097724).length < 2 ^ (prefixWord ++ tailWord_4097724).sum := by decide
  have hdescent : baseEnd_4097724 < baseStart_4097724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097735 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 4, 4]
def baseStart_4097735 : Nat := 118140960795 + 4097735 * 2 ^ 59
def prefixEnd_4097735 : Nat := 4983230072969 + 3 ^ 40 * 4097735 * 2
def baseEnd_4097735 : Nat := 1402738433167753551111577

theorem tailTrace_4097735 : CollatzResearch.WordTrace tailWord_4097735 prefixEnd_4097735 1402738433167753551111577 := by
  unfold tailWord_4097735
  simp only [CollatzResearch.WordTrace]
  refine ⟨149456673809613407266206659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99637782539742271510804439 149456673809613407266206659)
  ·
    refine ⟨224185010714420110899309989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149456673809613407266206659 224185010714420110899309989)
    ·
      refine ⟨42034689508953770793620623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224185010714420110899309989 42034689508953770793620623)
      ·
        refine ⟨63052034263430656190430935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42034689508953770793620623 63052034263430656190430935)
        ·
          refine ⟨94578051395145984285646403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63052034263430656190430935 94578051395145984285646403)
          ·
            refine ⟨141867077092718976428469605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94578051395145984285646403 141867077092718976428469605)
            ·
              refine ⟨26600076954884808080338051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141867077092718976428469605 26600076954884808080338051)
              ·
                refine ⟨39900115432327212120507077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26600076954884808080338051 39900115432327212120507077)
                ·
                  refine ⟨7481271643561352272595077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39900115432327212120507077 7481271643561352272595077)
                  ·
                    refine ⟨1402738433167753551111577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7481271643561352272595077 1402738433167753551111577)
                    ·
                      rfl

theorem cell22_4097735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_4097735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097735 prefixEnd_4097735 := by exact prefixLift 4097735
  have htrace : WordTrace (prefixWord ++ tailWord_4097735) baseStart_4097735 baseEnd_4097735 := by
    simpa [prefixWord, tailWord_4097735, baseEnd_4097735] using wordTrace_append hprefix tailTrace_4097735
  have hstable : (prefixWord ++ tailWord_4097735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097735).length < 2 ^ (prefixWord ++ tailWord_4097735).sum := by decide
  have hdescent : baseEnd_4097735 < baseStart_4097735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097765 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_4097765 : Nat := 118140960795 + 4097765 * 2 ^ 59
def prefixEnd_4097765 : Nat := 4983230072969 + 3 ^ 40 * 4097765 * 2
def baseEnd_4097765 : Nat := 1402748702780843472861485

theorem tailTrace_4097765 : CollatzResearch.WordTrace tailWord_4097765 prefixEnd_4097765 1402748702780843472861485 := by
  unfold tailWord_4097765
  simp only [CollatzResearch.WordTrace]
  refine ⟨149457767999504722389798749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99638511999669814926532499 149457767999504722389798749)
  ·
    refine ⟨56046662999814270896174531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149457767999504722389798749 56046662999814270896174531)
    ·
      refine ⟨84069994499721406344261797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56046662999814270896174531 84069994499721406344261797)
      ·
        refine ⟨15763123968697763689549087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84069994499721406344261797 15763123968697763689549087)
        ·
          refine ⟨23644685953046645534323631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15763123968697763689549087 23644685953046645534323631)
          ·
            refine ⟨35467028929569968301485447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23644685953046645534323631 35467028929569968301485447)
            ·
              refine ⟨53200543394354952452228171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35467028929569968301485447 53200543394354952452228171)
              ·
                refine ⟨79800815091532428678342257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53200543394354952452228171 79800815091532428678342257)
                ·
                  refine ⟨59850611318649321508756693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79800815091532428678342257 59850611318649321508756693)
                  ·
                    refine ⟨1402748702780843472861485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59850611318649321508756693 1402748702780843472861485)
                    ·
                      rfl

theorem cell22_4097765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_4097765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097765 prefixEnd_4097765 := by exact prefixLift 4097765
  have htrace : WordTrace (prefixWord ++ tailWord_4097765) baseStart_4097765 baseEnd_4097765 := by
    simpa [prefixWord, tailWord_4097765, baseEnd_4097765] using wordTrace_append hprefix tailTrace_4097765
  have hstable : (prefixWord ++ tailWord_4097765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097765).length < 2 ^ (prefixWord ++ tailWord_4097765).sum := by decide
  have hdescent : baseEnd_4097765 < baseStart_4097765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097795 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 7]
def baseStart_4097795 : Nat := 118140960795 + 4097795 * 2 ^ 59
def prefixEnd_4097795 : Nat := 4983230072969 + 3 ^ 40 * 4097795 * 2
def baseEnd_4097795 : Nat := 467586324131311131537131

theorem tailTrace_4097795 : CollatzResearch.WordTrace tailWord_4097795 prefixEnd_4097795 467586324131311131537131 := by
  unfold tailWord_4097795
  simp only [CollatzResearch.WordTrace]
  refine ⟨149458862189396037513390839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99639241459597358342260559 149458862189396037513390839)
  ·
    refine ⟨224188293284094056270086259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149458862189396037513390839 224188293284094056270086259)
    ·
      refine ⟨336282439926141084405129389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224188293284094056270086259 336282439926141084405129389)
      ·
        refine ⟨126105914972302906651923521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336282439926141084405129389 126105914972302906651923521)
        ·
          refine ⟨94579436229227179988942641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126105914972302906651923521 94579436229227179988942641)
          ·
            refine ⟨70934577171920384991706981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94579436229227179988942641 70934577171920384991706981)
            ·
              refine ⟨13300233219735072185945059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70934577171920384991706981 13300233219735072185945059)
              ·
                refine ⟨19950349829602608278917589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13300233219735072185945059 19950349829602608278917589)
                ·
                  refine ⟨467586324131311131537131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19950349829602608278917589 467586324131311131537131)
                  ·
                    rfl

theorem cell22_4097795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 7].length) (baseStart_4097795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097795 prefixEnd_4097795 := by exact prefixLift 4097795
  have htrace : WordTrace (prefixWord ++ tailWord_4097795) baseStart_4097795 baseEnd_4097795 := by
    simpa [prefixWord, tailWord_4097795, baseEnd_4097795] using wordTrace_append hprefix tailTrace_4097795
  have hstable : (prefixWord ++ tailWord_4097795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097795).length < 2 ^ (prefixWord ++ tailWord_4097795).sum := by decide
  have hdescent : baseEnd_4097795 < baseStart_4097795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097846 : List Nat := [5, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_4097846 : Nat := 118140960795 + 4097846 * 2 ^ 59
def prefixEnd_4097846 : Nat := 4983230072969 + 3 ^ 40 * 4097846 * 2
def baseEnd_4097846 : Nat := 467592143578728753862079

theorem tailTrace_4097846 : CollatzResearch.WordTrace tailWord_4097846 prefixEnd_4097846 467592143578728753862079 := by
  unfold tailWord_4097846
  simp only [CollatzResearch.WordTrace]
  refine ⟨9341295144513204576468587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99640481541474182148998261 9341295144513204576468587)
  ·
    refine ⟨14011942716769806864702881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9341295144513204576468587 14011942716769806864702881)
    ·
      refine ⟨10508957037577355148527161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14011942716769806864702881 10508957037577355148527161)
      ·
        refine ⟨7881717778183016361395371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10508957037577355148527161 7881717778183016361395371)
        ·
          refine ⟨11822576667274524542093057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7881717778183016361395371 11822576667274524542093057)
          ·
            refine ⟨8866932500455893406569793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11822576667274524542093057 8866932500455893406569793)
            ·
              refine ⟨6650199375341920054927345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8866932500455893406569793 6650199375341920054927345)
              ·
                refine ⟨4987649531506440041195509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6650199375341920054927345 4987649531506440041195509)
                ·
                  refine ⟨467592143578728753862079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4987649531506440041195509 467592143578728753862079)
                  ·
                    rfl

theorem cell22_4097846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_4097846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097846 prefixEnd_4097846 := by exact prefixLift 4097846
  have htrace : WordTrace (prefixWord ++ tailWord_4097846) baseStart_4097846 baseEnd_4097846 := by
    simpa [prefixWord, tailWord_4097846, baseEnd_4097846] using wordTrace_append hprefix tailTrace_4097846
  have hstable : (prefixWord ++ tailWord_4097846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097846).length < 2 ^ (prefixWord ++ tailWord_4097846).sum := by decide
  have hdescent : baseEnd_4097846 < baseStart_4097846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097872 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 6, 3]
def baseStart_4097872 : Nat := 118140960795 + 4097872 * 2 ^ 59
def prefixEnd_4097872 : Nat := 4983230072969 + 3 ^ 40 * 4097872 * 2
def baseEnd_4097872 : Nat := 1402785331067530860436157

theorem tailTrace_4097872 : CollatzResearch.WordTrace tailWord_4097872 prefixEnd_4097872 1402785331067530860436157 := by
  unfold tailWord_4097872
  simp only [CollatzResearch.WordTrace]
  refine ⟨74730835305058539831971935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99641113740078053109295913 74730835305058539831971935)
  ·
    refine ⟨112096252957587809747957903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74730835305058539831971935 112096252957587809747957903)
    ·
      refine ⟨168144379436381714621936855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112096252957587809747957903 168144379436381714621936855)
      ·
        refine ⟨252216569154572571932905283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168144379436381714621936855 252216569154572571932905283)
        ·
          refine ⟨378324853731858857899357925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252216569154572571932905283 378324853731858857899357925)
          ·
            refine ⟨70935910074723535856129611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 378324853731858857899357925 70935910074723535856129611)
            ·
              refine ⟨106403865112085303784194417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70935910074723535856129611 106403865112085303784194417)
              ·
                refine ⟨79802898834063977838145813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106403865112085303784194417 79802898834063977838145813)
                ·
                  refine ⟨3740760882846748961163085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79802898834063977838145813 3740760882846748961163085)
                  ·
                    refine ⟨1402785331067530860436157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3740760882846748961163085 1402785331067530860436157)
                    ·
                      rfl

theorem cell22_4097872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 6, 3].length) (baseStart_4097872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097872 prefixEnd_4097872 := by exact prefixLift 4097872
  have htrace : WordTrace (prefixWord ++ tailWord_4097872) baseStart_4097872 baseEnd_4097872 := by
    simpa [prefixWord, tailWord_4097872, baseEnd_4097872] using wordTrace_append hprefix tailTrace_4097872
  have hstable : (prefixWord ++ tailWord_4097872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097872).length < 2 ^ (prefixWord ++ tailWord_4097872).sum := by decide
  have hdescent : baseEnd_4097872 < baseStart_4097872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097887 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 1, 6]
def baseStart_4097887 : Nat := 118140960795 + 4097887 * 2 ^ 59
def prefixEnd_4097887 : Nat := 4983230072969 + 3 ^ 40 * 4097887 * 2
def baseEnd_4097887 : Nat := 1402790465874075821311111

theorem tailTrace_4097887 : CollatzResearch.WordTrace tailWord_4097887 prefixEnd_4097887 1402790465874075821311111 := by
  unfold tailWord_4097887
  simp only [CollatzResearch.WordTrace]
  refine ⟨149462217705062737225739915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99641478470041824817159943 149462217705062737225739915)
  ·
    refine ⟨224193326557594105838609873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149462217705062737225739915 224193326557594105838609873)
    ·
      refine ⟨168144994918195579378957405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224193326557594105838609873 168144994918195579378957405)
      ·
        refine ⟨63054373094323342267109027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168144994918195579378957405 63054373094323342267109027)
        ·
          refine ⟨94581559641485013400663541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63054373094323342267109027 94581559641485013400663541)
          ·
            refine ⟨8867021216389220006312207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94581559641485013400663541 8867021216389220006312207)
            ·
              refine ⟨13300531824583830009468311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8867021216389220006312207 13300531824583830009468311)
              ·
                refine ⟨19950797736875745014202467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13300531824583830009468311 19950797736875745014202467)
                ·
                  refine ⟨29926196605313617521303701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19950797736875745014202467 29926196605313617521303701)
                  ·
                    refine ⟨1402790465874075821311111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29926196605313617521303701 1402790465874075821311111)
                    ·
                      rfl

theorem cell22_4097887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_4097887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097887 prefixEnd_4097887 := by exact prefixLift 4097887
  have htrace : WordTrace (prefixWord ++ tailWord_4097887) baseStart_4097887 baseEnd_4097887 := by
    simpa [prefixWord, tailWord_4097887, baseEnd_4097887] using wordTrace_append hprefix tailTrace_4097887
  have hstable : (prefixWord ++ tailWord_4097887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097887).length < 2 ^ (prefixWord ++ tailWord_4097887).sum := by decide
  have hdescent : baseEnd_4097887 < baseStart_4097887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097891 : List Nat := [1, 1, 1, 5, 4, 1, 2, 3, 4]
def baseStart_4097891 : Nat := 118140960795 + 4097891 * 2 ^ 59
def prefixEnd_4097891 : Nat := 4983230072969 + 3 ^ 40 * 4097891 * 2
def baseEnd_4097891 : Nat := 467597278385273714737033

theorem tailTrace_4097891 : CollatzResearch.WordTrace tailWord_4097891 prefixEnd_4097891 467597278385273714737033 := by
  unfold tailWord_4097891
  simp only [CollatzResearch.WordTrace]
  refine ⟨149462363597048245908885527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99641575731365497272590351 149462363597048245908885527)
  ·
    refine ⟨224193545395572368863328291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149462363597048245908885527 224193545395572368863328291)
    ·
      refine ⟨336290318093358553294992437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224193545395572368863328291 336290318093358553294992437)
      ·
        refine ⟨31527217321252364371405541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 336290318093358553294992437 31527217321252364371405541)
        ·
          refine ⟨5911353247734818319638539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31527217321252364371405541 5911353247734818319638539)
          ·
            refine ⟨8867029871602227479457809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911353247734818319638539 8867029871602227479457809)
            ·
              refine ⟨6650272403701670609593357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8867029871602227479457809 6650272403701670609593357)
              ·
                refine ⟨2493852151388126478597509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6650272403701670609593357 2493852151388126478597509)
                ·
                  refine ⟨467597278385273714737033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2493852151388126478597509 467597278385273714737033)
                  ·
                    rfl

theorem cell22_4097891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 4].length) (baseStart_4097891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097891 prefixEnd_4097891 := by exact prefixLift 4097891
  have htrace : WordTrace (prefixWord ++ tailWord_4097891) baseStart_4097891 baseEnd_4097891 := by
    simpa [prefixWord, tailWord_4097891, baseEnd_4097891] using wordTrace_append hprefix tailTrace_4097891
  have hstable : (prefixWord ++ tailWord_4097891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097891).length < 2 ^ (prefixWord ++ tailWord_4097891).sum := by decide
  have hdescent : baseEnd_4097891 < baseStart_4097891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097942 : List Nat := [5, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_4097942 : Nat := 118140960795 + 4097942 * 2 ^ 59
def prefixEnd_4097942 : Nat := 4983230072969 + 3 ^ 40 * 4097942 * 2
def baseEnd_4097942 : Nat := 467603097832691337061981

theorem tailTrace_4097942 : CollatzResearch.WordTrace tailWord_4097942 prefixEnd_4097942 467603097832691337061981 := by
  unfold tailWord_4097942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9341513982491467601187005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99642815813242321079328053 9341513982491467601187005)
  ·
    refine ⟨3503067743434300350445127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9341513982491467601187005 3503067743434300350445127)
    ·
      refine ⟨5254601615151450525667691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3503067743434300350445127 5254601615151450525667691)
      ·
        refine ⟨7881902422727175788501537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5254601615151450525667691 7881902422727175788501537)
        ·
          refine ⟨5911426817045381841376153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7881902422727175788501537 5911426817045381841376153)
          ·
            refine ⟨4433570112784036381032115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5911426817045381841376153 4433570112784036381032115)
            ·
              refine ⟨6650355169176054571548173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4433570112784036381032115 6650355169176054571548173)
              ·
                refine ⟨2493883188441020464330565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6650355169176054571548173 2493883188441020464330565)
                ·
                  refine ⟨467603097832691337061981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2493883188441020464330565 467603097832691337061981)
                  ·
                    rfl

theorem cell22_4097942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_4097942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097942 prefixEnd_4097942 := by exact prefixLift 4097942
  have htrace : WordTrace (prefixWord ++ tailWord_4097942) baseStart_4097942 baseEnd_4097942 := by
    simpa [prefixWord, tailWord_4097942, baseEnd_4097942] using wordTrace_append hprefix tailTrace_4097942
  have hstable : (prefixWord ++ tailWord_4097942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097942).length < 2 ^ (prefixWord ++ tailWord_4097942).sum := by decide
  have hdescent : baseEnd_4097942 < baseStart_4097942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097981 : List Nat := [1, 4, 1, 2, 3, 1, 4, 1, 5]
def baseStart_4097981 : Nat := 118140960795 + 4097981 * 2 ^ 59
def prefixEnd_4097981 : Nat := 4983230072969 + 3 ^ 40 * 4097981 * 2
def baseEnd_4097981 : Nat := 467607547998363636486941

theorem tailTrace_4097981 : CollatzResearch.WordTrace tailWord_4097981 prefixEnd_4097981 467607547998363636486941 := by
  unfold tailWord_4097981
  simp only [CollatzResearch.WordTrace]
  refine ⟨149465646166722191279661797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99643764111148127519774531 149465646166722191279661797)
  ·
    refine ⟨28024808656260410864936587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149465646166722191279661797 28024808656260410864936587)
    ·
      refine ⟨42037212984390616297404881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28024808656260410864936587 42037212984390616297404881)
      ·
        refine ⟨31527909738292962223053661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42037212984390616297404881 31527909738292962223053661)
        ·
          refine ⟨11822966151859860833645123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31527909738292962223053661 11822966151859860833645123)
          ·
            refine ⟨17734449227789791250467685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11822966151859860833645123 17734449227789791250467685)
            ·
              refine ⟨3325209230210585859462691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17734449227789791250467685 3325209230210585859462691)
              ·
                refine ⟨4987813845315878789194037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3325209230210585859462691 4987813845315878789194037)
                ·
                  refine ⟨467607547998363636486941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4987813845315878789194037 467607547998363636486941)
                  ·
                    rfl

theorem cell22_4097981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_4097981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4097981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4097981 prefixEnd_4097981 := by exact prefixLift 4097981
  have htrace : WordTrace (prefixWord ++ tailWord_4097981) baseStart_4097981 baseEnd_4097981 := by
    simpa [prefixWord, tailWord_4097981, baseEnd_4097981] using wordTrace_append hprefix tailTrace_4097981
  have hstable : (prefixWord ++ tailWord_4097981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097981).length < 2 ^ (prefixWord ++ tailWord_4097981).sum := by decide
  have hdescent : baseEnd_4097981 < baseStart_4097981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098026 : List Nat := [3, 1, 3, 1, 2, 1, 3, 4, 4]
def baseStart_4098026 : Nat := 118140960795 + 4098026 * 2 ^ 59
def prefixEnd_4098026 : Nat := 4983230072969 + 3 ^ 40 * 4098026 * 2
def baseEnd_4098026 : Nat := 467612682804908597361895

theorem tailTrace_4098026 : CollatzResearch.WordTrace tailWord_4098026 prefixEnd_4098026 467612682804908597361895 := by
  unfold tailWord_4098026
  simp only [CollatzResearch.WordTrace]
  refine ⟨37366821862889790991262483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99644858301039442643366621 37366821862889790991262483)
  ·
    refine ⟨56050232794334686486893725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37366821862889790991262483 56050232794334686486893725)
    ·
      refine ⟨21018837297875507432585147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56050232794334686486893725 21018837297875507432585147)
      ·
        refine ⟨31528255946813261148877721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21018837297875507432585147 31528255946813261148877721)
        ·
          refine ⟨23646191960109945861658291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31528255946813261148877721 23646191960109945861658291)
          ·
            refine ⟨35469287940164918792487437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23646191960109945861658291 35469287940164918792487437)
            ·
              refine ⟨13300982977561844547182789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35469287940164918792487437 13300982977561844547182789)
              ·
                refine ⟨2493934308292845852596773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13300982977561844547182789 2493934308292845852596773)
                ·
                  refine ⟨467612682804908597361895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2493934308292845852596773 467612682804908597361895)
                  ·
                    rfl

theorem cell22_4098026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_4098026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098026 prefixEnd_4098026 := by exact prefixLift 4098026
  have htrace : WordTrace (prefixWord ++ tailWord_4098026) baseStart_4098026 baseEnd_4098026 := by
    simpa [prefixWord, tailWord_4098026, baseEnd_4098026] using wordTrace_append hprefix tailTrace_4098026
  have hstable : (prefixWord ++ tailWord_4098026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098026).length < 2 ^ (prefixWord ++ tailWord_4098026).sum := by decide
  have hdescent : baseEnd_4098026 < baseStart_4098026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098041 : List Nat := [1, 2, 1, 3, 1, 4, 2, 3, 2, 3]
def baseStart_4098041 : Nat := 118140960795 + 4098041 * 2 ^ 59
def prefixEnd_4098041 : Nat := 4983230072969 + 3 ^ 40 * 4098041 * 2
def baseEnd_4098041 : Nat := 1402843183221270752960639

theorem tailTrace_4098041 : CollatzResearch.WordTrace tailWord_4098041 prefixEnd_4098041 1402843183221270752960639 := by
  unfold tailWord_4098041
  simp only [CollatzResearch.WordTrace]
  refine ⟨149467834546504821526845977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99645223031003214351230651 149467834546504821526845977)
  ·
    refine ⟨112100875909878616145134483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149467834546504821526845977 112100875909878616145134483)
    ·
      refine ⟨168151313864817924217701725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112100875909878616145134483 168151313864817924217701725)
      ·
        refine ⟨63056742699306721581638147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168151313864817924217701725 63056742699306721581638147)
        ·
          refine ⟨94585114048960082372457221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63056742699306721581638147 94585114048960082372457221)
          ·
            refine ⟨17734708884180015444835729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94585114048960082372457221 17734708884180015444835729)
            ·
              refine ⟨13301031663135011583626797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17734708884180015444835729 13301031663135011583626797)
              ·
                refine ⟨4987886873675629343860049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13301031663135011583626797 4987886873675629343860049)
                ·
                  refine ⟨3740915155256722007895037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4987886873675629343860049 3740915155256722007895037)
                  ·
                    refine ⟨1402843183221270752960639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3740915155256722007895037 1402843183221270752960639)
                    ·
                      rfl

theorem cell22_4098041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 3].length) (baseStart_4098041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098041 prefixEnd_4098041 := by exact prefixLift 4098041
  have htrace : WordTrace (prefixWord ++ tailWord_4098041) baseStart_4098041 baseEnd_4098041 := by
    simpa [prefixWord, tailWord_4098041, baseEnd_4098041] using wordTrace_append hprefix tailTrace_4098041
  have hstable : (prefixWord ++ tailWord_4098041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098041).length < 2 ^ (prefixWord ++ tailWord_4098041).sum := by decide
  have hdescent : baseEnd_4098041 < baseStart_4098041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098099 : List Nat := [1, 1, 1, 2, 4, 1, 2, 5, 5]
def baseStart_4098099 : Nat := 118140960795 + 4098099 * 2 ^ 59
def prefixEnd_4098099 : Nat := 4983230072969 + 3 ^ 40 * 4098099 * 2
def baseEnd_4098099 : Nat := 467621012602192645003487

theorem tailTrace_4098099 : CollatzResearch.WordTrace tailWord_4098099 prefixEnd_4098099 467621012602192645003487 := by
  unfold tailWord_4098099
  simp only [CollatzResearch.WordTrace]
  refine ⟨149469949980294697432457351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99646633320196464954971567 149469949980294697432457351)
  ·
    refine ⟨224204924970442046148686027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149469949980294697432457351 224204924970442046148686027)
    ·
      refine ⟨336307387455663069223029041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224204924970442046148686027 336307387455663069223029041)
      ·
        refine ⟨252230540591747301917271781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336307387455663069223029041 252230540591747301917271781)
        ·
          refine ⟨47293226360952619109488459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252230540591747301917271781 47293226360952619109488459)
          ·
            refine ⟨70939839541428928664232689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47293226360952619109488459 70939839541428928664232689)
            ·
              refine ⟨53204879656071696498174517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70939839541428928664232689 53204879656071696498174517)
              ·
                refine ⟨4987957467756721546703861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53204879656071696498174517 4987957467756721546703861)
                ·
                  refine ⟨467621012602192645003487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4987957467756721546703861 467621012602192645003487)
                  ·
                    rfl

theorem cell22_4098099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 5].length) (baseStart_4098099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098099 prefixEnd_4098099 := by exact prefixLift 4098099
  have htrace : WordTrace (prefixWord ++ tailWord_4098099) baseStart_4098099 baseEnd_4098099 := by
    simpa [prefixWord, tailWord_4098099, baseEnd_4098099] using wordTrace_append hprefix tailTrace_4098099
  have hstable : (prefixWord ++ tailWord_4098099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098099).length < 2 ^ (prefixWord ++ tailWord_4098099).sum := by decide
  have hdescent : baseEnd_4098099 < baseStart_4098099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098129 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 5, 4]
def baseStart_4098129 : Nat := 118140960795 + 4098129 * 2 ^ 59
def prefixEnd_4098129 : Nat := 4983230072969 + 3 ^ 40 * 4098129 * 2
def baseEnd_4098129 : Nat := 1402873307419667856760369

theorem tailTrace_4098129 : CollatzResearch.WordTrace tailWord_4098129 prefixEnd_4098129 1402873307419667856760369 := by
  unfold tailWord_4098129
  simp only [CollatzResearch.WordTrace]
  refine ⟨149471044170186012556049441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99647362780124008370699627 149471044170186012556049441)
  ·
    refine ⟨112103283127639509417037081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149471044170186012556049441 112103283127639509417037081)
    ·
      refine ⟨84077462345729632062777811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112103283127639509417037081 84077462345729632062777811)
      ·
        refine ⟨126116193518594448094166717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84077462345729632062777811 126116193518594448094166717)
        ·
          refine ⟨47293572569472918035312519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126116193518594448094166717 47293572569472918035312519)
          ·
            refine ⟨70940358854209377052968779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47293572569472918035312519 70940358854209377052968779)
            ·
              refine ⟨106410538281314065579453169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70940358854209377052968779 106410538281314065579453169)
              ·
                refine ⟨79807903710985549184589877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106410538281314065579453169 79807903710985549184589877)
                ·
                  refine ⟨7481990972904895236055301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79807903710985549184589877 7481990972904895236055301)
                  ·
                    refine ⟨1402873307419667856760369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7481990972904895236055301 1402873307419667856760369)
                    ·
                      rfl

theorem cell22_4098129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_4098129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098129 prefixEnd_4098129 := by exact prefixLift 4098129
  have htrace : WordTrace (prefixWord ++ tailWord_4098129) baseStart_4098129 baseEnd_4098129 := by
    simpa [prefixWord, tailWord_4098129, baseEnd_4098129] using wordTrace_append hprefix tailTrace_4098129
  have hstable : (prefixWord ++ tailWord_4098129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098129).length < 2 ^ (prefixWord ++ tailWord_4098129).sum := by decide
  have hdescent : baseEnd_4098129 < baseStart_4098129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098210 : List Nat := [3, 3, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_4098210 : Nat := 118140960795 + 4098210 * 2 ^ 59
def prefixEnd_4098210 : Nat := 4983230072969 + 3 ^ 40 * 4098210 * 2
def baseEnd_4098210 : Nat := 1402901035375010645485121

theorem tailTrace_4098210 : CollatzResearch.WordTrace tailWord_4098210 prefixEnd_4098210 1402901035375010645485121 := by
  unfold tailWord_4098210
  simp only [CollatzResearch.WordTrace]
  refine ⟨37368499620723140847437021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99649332321928375593165389 37368499620723140847437021)
  ·
    refine ⟨14013187357771177817788883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37368499620723140847437021 14013187357771177817788883)
    ·
      refine ⟨21019781036656766726683325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14013187357771177817788883 21019781036656766726683325)
      ·
        refine ⟨7882417888746287522506247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21019781036656766726683325 7882417888746287522506247)
        ·
          refine ⟨11823626833119431283759371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7882417888746287522506247 11823626833119431283759371)
          ·
            refine ⟨17735440249679146925639057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11823626833119431283759371 17735440249679146925639057)
            ·
              refine ⟨13301580187259360194229293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17735440249679146925639057 13301580187259360194229293)
              ·
                refine ⟨4988092570222260072835985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13301580187259360194229293 4988092570222260072835985)
                ·
                  refine ⟨3741069427666695054626989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4988092570222260072835985 3741069427666695054626989)
                  ·
                    refine ⟨1402901035375010645485121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3741069427666695054626989 1402901035375010645485121)
                    ·
                      rfl

theorem cell22_4098210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_4098210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098210 prefixEnd_4098210 := by exact prefixLift 4098210
  have htrace : WordTrace (prefixWord ++ tailWord_4098210) baseStart_4098210 baseEnd_4098210 := by
    simpa [prefixWord, tailWord_4098210, baseEnd_4098210] using wordTrace_append hprefix tailTrace_4098210
  have hstable : (prefixWord ++ tailWord_4098210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098210).length < 2 ^ (prefixWord ++ tailWord_4098210).sum := by decide
  have hdescent : baseEnd_4098210 < baseStart_4098210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098225 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 2, 4]
def baseStart_4098225 : Nat := 118140960795 + 4098225 * 2 ^ 59
def prefixEnd_4098225 : Nat := 4983230072969 + 3 ^ 40 * 4098225 * 2
def baseEnd_4098225 : Nat := 1402906170181555606360075

theorem tailTrace_4098225 : CollatzResearch.WordTrace tailWord_4098225 prefixEnd_4098225 1402906170181555606360075 := by
  unfold tailWord_4098225
  simp only [CollatzResearch.WordTrace]
  refine ⟨149474545577838220951544129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99649697051892147301029419 149474545577838220951544129)
  ·
    refine ⟨112105909183378665713658097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149474545577838220951544129 112105909183378665713658097)
    ·
      refine ⟨84079431887533999285243573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112105909183378665713658097 84079431887533999285243573)
      ·
        refine ⟨7882446739456312432991585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84079431887533999285243573 7882446739456312432991585)
        ·
          refine ⟨5911835054592234324743689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7882446739456312432991585 5911835054592234324743689)
          ·
            refine ⟨4433876290944175743557767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5911835054592234324743689 4433876290944175743557767)
            ·
              refine ⟨6650814436416263615336651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4433876290944175743557767 6650814436416263615336651)
              ·
                refine ⟨9976221654624395423004977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6650814436416263615336651 9976221654624395423004977)
                ·
                  refine ⟨7482166240968296567253733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9976221654624395423004977 7482166240968296567253733)
                  ·
                    refine ⟨1402906170181555606360075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7482166240968296567253733 1402906170181555606360075)
                    ·
                      rfl

theorem cell22_4098225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_4098225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098225 prefixEnd_4098225 := by exact prefixLift 4098225
  have htrace : WordTrace (prefixWord ++ tailWord_4098225) baseStart_4098225 baseEnd_4098225 := by
    simpa [prefixWord, tailWord_4098225, baseEnd_4098225] using wordTrace_append hprefix tailTrace_4098225
  have hstable : (prefixWord ++ tailWord_4098225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098225).length < 2 ^ (prefixWord ++ tailWord_4098225).sum := by decide
  have hdescent : baseEnd_4098225 < baseStart_4098225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098266 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 2, 5]
def baseStart_4098266 : Nat := 118140960795 + 4098266 * 2 ^ 59
def prefixEnd_4098266 : Nat := 4983230072969 + 3 ^ 40 * 4098266 * 2
def baseEnd_4098266 : Nat := 1402920205319445166084949

theorem tailTrace_4098266 : CollatzResearch.WordTrace tailWord_4098266 prefixEnd_4098266 1402920205319445166084949 := by
  unfold tailWord_4098266
  simp only [CollatzResearch.WordTrace]
  refine ⟨37369010242672421238446663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99650693980459789969191101 37369010242672421238446663)
  ·
    refine ⟨56053515364008631857669995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37369010242672421238446663 56053515364008631857669995)
    ·
      refine ⟨84080273046012947786504993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56053515364008631857669995 84080273046012947786504993)
      ·
        refine ⟨63060204784509710839878745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84080273046012947786504993 63060204784509710839878745)
        ·
          refine ⟨47295153588382283129909059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63060204784509710839878745 47295153588382283129909059)
          ·
            refine ⟨70942730382573424694863589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47295153588382283129909059 70942730382573424694863589)
            ·
              refine ⟨13301761946732517130286923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70942730382573424694863589 13301761946732517130286923)
              ·
                refine ⟨19952642920098775695430385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13301761946732517130286923 19952642920098775695430385)
                ·
                  refine ⟨14964482190074081771572789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19952642920098775695430385 14964482190074081771572789)
                  ·
                    refine ⟨1402920205319445166084949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14964482190074081771572789 1402920205319445166084949)
                    ·
                      rfl

theorem cell22_4098266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_4098266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098266 prefixEnd_4098266 := by exact prefixLift 4098266
  have htrace : WordTrace (prefixWord ++ tailWord_4098266) baseStart_4098266 baseEnd_4098266 := by
    simpa [prefixWord, tailWord_4098266, baseEnd_4098266] using wordTrace_append hprefix tailTrace_4098266
  have hstable : (prefixWord ++ tailWord_4098266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098266).length < 2 ^ (prefixWord ++ tailWord_4098266).sum := by decide
  have hdescent : baseEnd_4098266 < baseStart_4098266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098274 : List Nat := [3, 3, 4, 1, 1, 2, 2, 6]
def baseStart_4098274 : Nat := 118140960795 + 4098274 * 2 ^ 59
def prefixEnd_4098274 : Nat := 4983230072969 + 3 ^ 40 * 4098274 * 2
def baseEnd_4098274 : Nat := 155880327098103979098325

theorem tailTrace_4098274 : CollatzResearch.WordTrace tailWord_4098274 prefixEnd_4098274 155880327098103979098325 := by
  unfold tailWord_4098274
  simp only [CollatzResearch.WordTrace]
  refine ⟨37369083188665175580019469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99650888503107134880051917 37369083188665175580019469)
  ·
    refine ⟨14013406195749440842507301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37369083188665175580019469 14013406195749440842507301)
    ·
      refine ⟨2627513661703020157970119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14013406195749440842507301 2627513661703020157970119)
      ·
        refine ⟨3941270492554530236955179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2627513661703020157970119 3941270492554530236955179)
        ·
          refine ⟨5911905738831795355432769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3941270492554530236955179 5911905738831795355432769)
          ·
            refine ⟨4433929304123846516574577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5911905738831795355432769 4433929304123846516574577)
            ·
              refine ⟨3325446978092884887430933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4433929304123846516574577 3325446978092884887430933)
              ·
                refine ⟨155880327098103979098325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3325446978092884887430933 155880327098103979098325)
                ·
                  rfl

theorem cell22_4098274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 6].length) (baseStart_4098274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098274 prefixEnd_4098274 := by exact prefixLift 4098274
  have htrace : WordTrace (prefixWord ++ tailWord_4098274) baseStart_4098274 baseEnd_4098274 := by
    simpa [prefixWord, tailWord_4098274, baseEnd_4098274] using wordTrace_append hprefix tailTrace_4098274
  have hstable : (prefixWord ++ tailWord_4098274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098274).length < 2 ^ (prefixWord ++ tailWord_4098274).sum := by decide
  have hdescent : baseEnd_4098274 < baseStart_4098274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098298 : List Nat := [3, 1, 1, 1, 1, 5, 2, 3, 1, 4]
def baseStart_4098298 : Nat := 118140960795 + 4098298 * 2 ^ 59
def prefixEnd_4098298 : Nat := 4983230072969 + 3 ^ 40 * 4098298 * 2
def baseEnd_4098298 : Nat := 1402931159573407749284851

theorem tailTrace_4098298 : CollatzResearch.WordTrace tailWord_4098298 prefixEnd_4098298 1402931159573407749284851 := by
  unfold tailWord_4098298
  simp only [CollatzResearch.WordTrace]
  refine ⟨37369302026643438604737887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99651472071049169612634365 37369302026643438604737887)
  ·
    refine ⟨56053953039965157907106831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37369302026643438604737887 56053953039965157907106831)
    ·
      refine ⟨84080929559947736860660247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56053953039965157907106831 84080929559947736860660247)
      ·
        refine ⟨126121394339921605290990371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84080929559947736860660247 126121394339921605290990371)
        ·
          refine ⟨189182091509882407936485557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126121394339921605290990371 189182091509882407936485557)
          ·
            refine ⟨17735821079051475744045521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189182091509882407936485557 17735821079051475744045521)
            ·
              refine ⟨13301865809288606808034141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17735821079051475744045521 13301865809288606808034141)
              ·
                refine ⟨4988199678483227553012803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13301865809288606808034141 4988199678483227553012803)
                ·
                  refine ⟨7482299517724841329519205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988199678483227553012803 7482299517724841329519205)
                  ·
                    refine ⟨1402931159573407749284851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7482299517724841329519205 1402931159573407749284851)
                    ·
                      rfl

theorem cell22_4098298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_4098298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098298 prefixEnd_4098298 := by exact prefixLift 4098298
  have htrace : WordTrace (prefixWord ++ tailWord_4098298) baseStart_4098298 baseEnd_4098298 := by
    simpa [prefixWord, tailWord_4098298, baseEnd_4098298] using wordTrace_append hprefix tailTrace_4098298
  have hstable : (prefixWord ++ tailWord_4098298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098298).length < 2 ^ (prefixWord ++ tailWord_4098298).sum := by decide
  have hdescent : baseEnd_4098298 < baseStart_4098298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098313 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 6]
def baseStart_4098313 : Nat := 118140960795 + 4098313 * 2 ^ 59
def prefixEnd_4098313 : Nat := 4983230072969 + 3 ^ 40 * 4098313 * 2
def baseEnd_4098313 : Nat := 467645431459984236719935

theorem tailTrace_4098313 : CollatzResearch.WordTrace tailWord_4098313 prefixEnd_4098313 467645431459984236719935 := by
  unfold tailWord_4098313
  simp only [CollatzResearch.WordTrace]
  refine ⟨149477755201519411980747593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99651836801012941320498395 149477755201519411980747593)
  ·
    refine ⟨112108316401139558985560695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149477755201519411980747593 112108316401139558985560695)
    ·
      refine ⟨168162474601709338478341043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112108316401139558985560695 168162474601709338478341043)
      ·
        refine ⟨252243711902564007717511565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168162474601709338478341043 252243711902564007717511565)
        ·
          refine ⟨94591391963461502894066837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252243711902564007717511565 94591391963461502894066837)
          ·
            refine ⟨4433971498287257948159383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94591391963461502894066837 4433971498287257948159383)
            ·
              refine ⟨6650957247430886922239075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4433971498287257948159383 6650957247430886922239075)
              ·
                refine ⟨9976435871146330383358613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6650957247430886922239075 9976435871146330383358613)
                ·
                  refine ⟨467645431459984236719935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9976435871146330383358613 467645431459984236719935)
                  ·
                    rfl

theorem cell22_4098313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 6].length) (baseStart_4098313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098313 prefixEnd_4098313 := by exact prefixLift 4098313
  have htrace : WordTrace (prefixWord ++ tailWord_4098313) baseStart_4098313 baseEnd_4098313 := by
    simpa [prefixWord, tailWord_4098313, baseEnd_4098313] using wordTrace_append hprefix tailTrace_4098313
  have hstable : (prefixWord ++ tailWord_4098313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098313).length < 2 ^ (prefixWord ++ tailWord_4098313).sum := by decide
  have hdescent : baseEnd_4098313 < baseStart_4098313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098349 : List Nat := [1, 5, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_4098349 : Nat := 118140960795 + 4098349 * 2 ^ 59
def prefixEnd_4098349 : Nat := 4983230072969 + 3 ^ 40 * 4098349 * 2
def baseEnd_4098349 : Nat := 1402948617915660616259695

theorem tailTrace_4098349 : CollatzResearch.WordTrace tailWord_4098349 prefixEnd_4098349 1402948617915660616259695 := by
  unfold tailWord_4098349
  simp only [CollatzResearch.WordTrace]
  refine ⟨149479068229388990129058101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99652712152925993419372067 149479068229388990129058101)
  ·
    refine ⟨14013662646505217824599197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149479068229388990129058101 14013662646505217824599197)
    ·
      refine ⟨5255123492439456684224699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14013662646505217824599197 5255123492439456684224699)
      ·
        refine ⟨7882685238659185026337049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5255123492439456684224699 7882685238659185026337049)
        ·
          refine ⟨5912013928994388769752787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7882685238659185026337049 5912013928994388769752787)
          ·
            refine ⟨8868020893491583154629181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5912013928994388769752787 8868020893491583154629181)
            ·
              refine ⟨3325507835059343682985943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8868020893491583154629181 3325507835059343682985943)
              ·
                refine ⟨4988261752589015524478915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3325507835059343682985943 4988261752589015524478915)
                ·
                  refine ⟨7482392628883523286718373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988261752589015524478915 7482392628883523286718373)
                  ·
                    refine ⟨1402948617915660616259695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7482392628883523286718373 1402948617915660616259695)
                    ·
                      rfl

theorem cell22_4098349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_4098349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098349 prefixEnd_4098349 := by exact prefixLift 4098349
  have htrace : WordTrace (prefixWord ++ tailWord_4098349) baseStart_4098349 baseEnd_4098349 := by
    simpa [prefixWord, tailWord_4098349, baseEnd_4098349] using wordTrace_append hprefix tailTrace_4098349
  have hstable : (prefixWord ++ tailWord_4098349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098349).length < 2 ^ (prefixWord ++ tailWord_4098349).sum := by decide
  have hdescent : baseEnd_4098349 < baseStart_4098349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098371 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 2, 6]
def baseStart_4098371 : Nat := 118140960795 + 4098371 * 2 ^ 59
def prefixEnd_4098371 : Nat := 4983230072969 + 3 ^ 40 * 4098371 * 2
def baseEnd_4098371 : Nat := 1402956148965259892209627

theorem tailTrace_4098371 : CollatzResearch.WordTrace tailWord_4098371 prefixEnd_4098371 1402956148965259892209627 := by
  unfold tailWord_4098371
  simp only [CollatzResearch.WordTrace]
  refine ⟨149479870635309287886358967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99653247090206191924239311 149479870635309287886358967)
  ·
    refine ⟨224219805952963931829538451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149479870635309287886358967 224219805952963931829538451)
    ·
      refine ⟨336329708929445897744307677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224219805952963931829538451 336329708929445897744307677)
      ·
        refine ⟨126123640848542211654115379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336329708929445897744307677 126123640848542211654115379)
        ·
          refine ⟨189185461272813317481173069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126123640848542211654115379 189185461272813317481173069)
          ·
            refine ⟨70944547977304994055439901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189185461272813317481173069 70944547977304994055439901)
            ·
              refine ⟨26604205491489372770789963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70944547977304994055439901 26604205491489372770789963)
              ·
                refine ⟨39906308237234059156184945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26604205491489372770789963 39906308237234059156184945)
                ·
                  refine ⟨29929731177925544367138709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39906308237234059156184945 29929731177925544367138709)
                  ·
                    refine ⟨1402956148965259892209627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29929731177925544367138709 1402956148965259892209627)
                    ·
                      rfl

theorem cell22_4098371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 6].length) (baseStart_4098371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098371 prefixEnd_4098371 := by exact prefixLift 4098371
  have htrace : WordTrace (prefixWord ++ tailWord_4098371) baseStart_4098371 baseEnd_4098371 := by
    simpa [prefixWord, tailWord_4098371, baseEnd_4098371] using wordTrace_append hprefix tailTrace_4098371
  have hstable : (prefixWord ++ tailWord_4098371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098371).length < 2 ^ (prefixWord ++ tailWord_4098371).sum := by decide
  have hdescent : baseEnd_4098371 < baseStart_4098371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098398 : List Nat := [4, 4, 2, 1, 1, 1, 2, 3, 4]
def baseStart_4098398 : Nat := 118140960795 + 4098398 * 2 ^ 59
def prefixEnd_4098398 : Nat := 4983230072969 + 3 ^ 40 * 4098398 * 2
def baseEnd_4098398 : Nat := 467655130539013607261515

theorem tailTrace_4098398 : CollatzResearch.WordTrace tailWord_4098398 prefixEnd_4098398 467655130539013607261515 := by
  unfold tailWord_4098398
  simp only [CollatzResearch.WordTrace]
  refine ⟨18685106925776433937198981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99653903604140980998394565 18685106925776433937198981)
  ·
    refine ⟨3503457548583081363224809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18685106925776433937198981 3503457548583081363224809)
    ·
      refine ⟨2627593161437311022418607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3503457548583081363224809 2627593161437311022418607)
      ·
        refine ⟨3941389742155966533627911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2627593161437311022418607 3941389742155966533627911)
        ·
          refine ⟨5912084613233949800441867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3941389742155966533627911 5912084613233949800441867)
          ·
            refine ⟨8868126919850924700662801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5912084613233949800441867 8868126919850924700662801)
            ·
              refine ⟨6651095189888193525497101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8868126919850924700662801 6651095189888193525497101)
              ·
                refine ⟨2494160696208072572061413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6651095189888193525497101 2494160696208072572061413)
                ·
                  refine ⟨467655130539013607261515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2494160696208072572061413 467655130539013607261515)
                  ·
                    rfl

theorem cell22_4098398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_4098398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098398 prefixEnd_4098398 := by exact prefixLift 4098398
  have htrace : WordTrace (prefixWord ++ tailWord_4098398) baseStart_4098398 baseEnd_4098398 := by
    simpa [prefixWord, tailWord_4098398, baseEnd_4098398] using wordTrace_append hprefix tailTrace_4098398
  have hstable : (prefixWord ++ tailWord_4098398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098398).length < 2 ^ (prefixWord ++ tailWord_4098398).sum := by decide
  have hdescent : baseEnd_4098398 < baseStart_4098398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098407 : List Nat := [1, 1, 5, 1, 3, 1, 1, 5, 1, 3]
def baseStart_4098407 : Nat := 118140960795 + 4098407 * 2 ^ 59
def prefixEnd_4098407 : Nat := 4983230072969 + 3 ^ 40 * 4098407 * 2
def baseEnd_4098407 : Nat := 1402968472500967798309517

theorem tailTrace_4098407 : CollatzResearch.WordTrace tailWord_4098407 prefixEnd_4098407 1402968472500967798309517 := by
  unfold tailWord_4098407
  simp only [CollatzResearch.WordTrace]
  refine ⟨149481183663178866034669475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99654122442119244023112983 149481183663178866034669475)
  ·
    refine ⟨224221775494768299052004213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149481183663178866034669475 224221775494768299052004213)
    ·
      refine ⟨21020791452634528036125395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224221775494768299052004213 21020791452634528036125395)
      ·
        refine ⟨31531187178951792054188093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21020791452634528036125395 31531187178951792054188093)
        ·
          refine ⟨11824195192106922020320535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31531187178951792054188093 11824195192106922020320535)
          ·
            refine ⟨17736292788160383030480803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11824195192106922020320535 17736292788160383030480803)
            ·
              refine ⟨26604439182240574545721205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17736292788160383030480803 26604439182240574545721205)
              ·
                refine ⟨2494166173335053863661363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26604439182240574545721205 2494166173335053863661363)
                ·
                  refine ⟨3741249260002580795492045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2494166173335053863661363 3741249260002580795492045)
                  ·
                    refine ⟨1402968472500967798309517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3741249260002580795492045 1402968472500967798309517)
                    ·
                      rfl

theorem cell22_4098407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_4098407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098407 prefixEnd_4098407 := by exact prefixLift 4098407
  have htrace : WordTrace (prefixWord ++ tailWord_4098407) baseStart_4098407 baseEnd_4098407 := by
    simpa [prefixWord, tailWord_4098407, baseEnd_4098407] using wordTrace_append hprefix tailTrace_4098407
  have hstable : (prefixWord ++ tailWord_4098407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098407).length < 2 ^ (prefixWord ++ tailWord_4098407).sum := by decide
  have hdescent : baseEnd_4098407 < baseStart_4098407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098418 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_4098418 : Nat := 118140960795 + 4098418 * 2 ^ 59
def prefixEnd_4098418 : Nat := 4983230072969 + 3 ^ 40 * 4098418 * 2
def baseEnd_4098418 : Nat := 1402972238025767436284483

theorem tailTrace_4098418 : CollatzResearch.WordTrace tailWord_4098418 prefixEnd_4098418 1402972238025767436284483 := by
  unfold tailWord_4098418
  simp only [CollatzResearch.WordTrace]
  refine ⟨37370396216534753728329977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99654389910759343275546605 37370396216534753728329977)
  ·
    refine ⟨28027797162401065296247483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37370396216534753728329977 28027797162401065296247483)
    ·
      refine ⟨42041695743601597944371225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28027797162401065296247483 42041695743601597944371225)
      ·
        refine ⟨31531271807701198458278419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42041695743601597944371225 31531271807701198458278419)
        ·
          refine ⟨47296907711551797687417629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31531271807701198458278419 47296907711551797687417629)
          ·
            refine ⟨17736340391831924132781611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47296907711551797687417629 17736340391831924132781611)
            ·
              refine ⟨26604510587747886199172417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17736340391831924132781611 26604510587747886199172417)
              ·
                refine ⟨19953382940810914649379313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26604510587747886199172417 19953382940810914649379313)
                ·
                  refine ⟨14965037205608185987034485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19953382940810914649379313 14965037205608185987034485)
                  ·
                    refine ⟨1402972238025767436284483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14965037205608185987034485 1402972238025767436284483)
                    ·
                      rfl

theorem cell22_4098418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_4098418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098418 prefixEnd_4098418 := by exact prefixLift 4098418
  have htrace : WordTrace (prefixWord ++ tailWord_4098418) baseStart_4098418 baseEnd_4098418 := by
    simpa [prefixWord, tailWord_4098418, baseEnd_4098418] using wordTrace_append hprefix tailTrace_4098418
  have hstable : (prefixWord ++ tailWord_4098418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098418).length < 2 ^ (prefixWord ++ tailWord_4098418).sum := by decide
  have hdescent : baseEnd_4098418 < baseStart_4098418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098431 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 10]
def baseStart_4098431 : Nat := 118140960795 + 4098431 * 2 ^ 59
def prefixEnd_4098431 : Nat := 4983230072969 + 3 ^ 40 * 4098431 * 2
def baseEnd_4098431 : Nat := 467658896063813245236481

theorem tailTrace_4098431 : CollatzResearch.WordTrace tailWord_4098431 prefixEnd_4098431 467658896063813245236481 := by
  unfold tailWord_4098431
  simp only [CollatzResearch.WordTrace]
  refine ⟨149482059015091918133543147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99654706010061278755695431 149482059015091918133543147)
  ·
    refine ⟨224223088522637877200314721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149482059015091918133543147 224223088522637877200314721)
    ·
      refine ⟨168167316391978407900236041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224223088522637877200314721 168167316391978407900236041)
      ·
        refine ⟨126125487293983805925177031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168167316391978407900236041 126125487293983805925177031)
        ·
          refine ⟨189188230940975708887765547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126125487293983805925177031 189188230940975708887765547)
          ·
            refine ⟨283782346411463563331648321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189188230940975708887765547 283782346411463563331648321)
            ·
              refine ⟨212836759808597672498736241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283782346411463563331648321 212836759808597672498736241)
              ·
                refine ⟨159627569856448254374052181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212836759808597672498736241 159627569856448254374052181)
                ·
                  refine ⟨467658896063813245236481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 159627569856448254374052181 467658896063813245236481)
                  ·
                    rfl

theorem cell22_4098431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 10].length) (baseStart_4098431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098431 prefixEnd_4098431 := by exact prefixLift 4098431
  have htrace : WordTrace (prefixWord ++ tailWord_4098431) baseStart_4098431 baseEnd_4098431 := by
    simpa [prefixWord, tailWord_4098431, baseEnd_4098431] using wordTrace_append hprefix tailTrace_4098431
  have hstable : (prefixWord ++ tailWord_4098431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098431).length < 2 ^ (prefixWord ++ tailWord_4098431).sum := by decide
  have hdescent : baseEnd_4098431 < baseStart_4098431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098463 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 3, 5]
def baseStart_4098463 : Nat := 118140960795 + 4098463 * 2 ^ 59
def prefixEnd_4098463 : Nat := 4983230072969 + 3 ^ 40 * 4098463 * 2
def baseEnd_4098463 : Nat := 1402987642445402318909345

theorem tailTrace_4098463 : CollatzResearch.WordTrace tailWord_4098463 prefixEnd_4098463 1402987642445402318909345 := by
  unfold tailWord_4098463
  simp only [CollatzResearch.WordTrace]
  refine ⟨149483226150975987598708043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99655484100650658399138695 149483226150975987598708043)
  ·
    refine ⟨224224839226463981398062065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149483226150975987598708043 224224839226463981398062065)
    ·
      refine ⟨168168629419847986048546549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224224839226463981398062065 168168629419847986048546549)
      ·
        refine ⟨15765809008110748692051239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168168629419847986048546549 15765809008110748692051239)
        ·
          refine ⟨23648713512166123038076859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15765809008110748692051239 23648713512166123038076859)
          ·
            refine ⟨35473070268249184557115289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23648713512166123038076859 35473070268249184557115289)
            ·
              refine ⟨26604802701186888417836467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35473070268249184557115289 26604802701186888417836467)
              ·
                refine ⟨39907204051780332626754701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26604802701186888417836467 39907204051780332626754701)
                ·
                  refine ⟨14965201519417624735033013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39907204051780332626754701 14965201519417624735033013)
                  ·
                    refine ⟨1402987642445402318909345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14965201519417624735033013 1402987642445402318909345)
                    ·
                      rfl

theorem cell22_4098463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_4098463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098463 prefixEnd_4098463 := by exact prefixLift 4098463
  have htrace : WordTrace (prefixWord ++ tailWord_4098463) baseStart_4098463 baseEnd_4098463 := by
    simpa [prefixWord, tailWord_4098463, baseEnd_4098463] using wordTrace_append hprefix tailTrace_4098463
  have hstable : (prefixWord ++ tailWord_4098463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098463).length < 2 ^ (prefixWord ++ tailWord_4098463).sum := by decide
  have hdescent : baseEnd_4098463 < baseStart_4098463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098482 : List Nat := [3, 2, 1, 1, 1, 1, 7, 2, 4]
def baseStart_4098482 : Nat := 118140960795 + 4098482 * 2 ^ 59
def prefixEnd_4098482 : Nat := 4983230072969 + 3 ^ 40 * 4098482 * 2
def baseEnd_4098482 : Nat := 467664715511230867561429

theorem tailTrace_4098482 : CollatzResearch.WordTrace tailWord_4098482 prefixEnd_4098482 467664715511230867561429 := by
  unfold tailWord_4098482
  simp only [CollatzResearch.WordTrace]
  refine ⟨37370979784476788460912425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99655946091938102562433133 37370979784476788460912425)
  ·
    refine ⟨28028234838357591345684319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37370979784476788460912425 28028234838357591345684319)
    ·
      refine ⟨42042352257536387018526479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28028234838357591345684319 42042352257536387018526479)
      ·
        refine ⟨63063528386304580527789719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42042352257536387018526479 63063528386304580527789719)
        ·
          refine ⟨94595292579456870791684579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63063528386304580527789719 94595292579456870791684579)
          ·
            refine ⟨141892938869185306187526869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94595292579456870791684579 141892938869185306187526869)
            ·
              refine ⟨3325615754746530613770161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 141892938869185306187526869 3325615754746530613770161)
              ·
                refine ⟨2494211816059897960327621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3325615754746530613770161 2494211816059897960327621)
                ·
                  refine ⟨467664715511230867561429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2494211816059897960327621 467664715511230867561429)
                  ·
                    rfl

theorem cell22_4098482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_4098482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098482 prefixEnd_4098482 := by exact prefixLift 4098482
  have htrace : WordTrace (prefixWord ++ tailWord_4098482) baseStart_4098482 baseEnd_4098482 := by
    simpa [prefixWord, tailWord_4098482, baseEnd_4098482] using wordTrace_append hprefix tailTrace_4098482
  have hstable : (prefixWord ++ tailWord_4098482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098482).length < 2 ^ (prefixWord ++ tailWord_4098482).sum := by decide
  have hdescent : baseEnd_4098482 < baseStart_4098482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098493 : List Nat := [1, 4, 1, 2, 2, 2, 1, 9]
def baseStart_4098493 : Nat := 118140960795 + 4098493 * 2 ^ 59
def prefixEnd_4098493 : Nat := 4983230072969 + 3 ^ 40 * 4098493 * 2
def baseEnd_4098493 : Nat := 155888656895388026739917

theorem tailTrace_4098493 : CollatzResearch.WordTrace tailWord_4098493 prefixEnd_4098493 155888656895388026739917 := by
  unfold tailWord_4098493
  simp only [CollatzResearch.WordTrace]
  refine ⟨149484320340867302722300133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99656213560578201814866755 149484320340867302722300133)
  ·
    refine ⟨28028310063912619260431275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149484320340867302722300133 28028310063912619260431275)
    ·
      refine ⟨42042465095868928890646913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28028310063912619260431275 42042465095868928890646913)
      ·
        refine ⟨31531848821901696667985185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42042465095868928890646913 31531848821901696667985185)
        ·
          refine ⟨23648886616426272500988889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31531848821901696667985185 23648886616426272500988889)
          ·
            refine ⟨17736664962319704375741667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23648886616426272500988889 17736664962319704375741667)
            ·
              refine ⟨26604997443479556563612501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17736664962319704375741667 26604997443479556563612501)
              ·
                refine ⟨155888656895388026739917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26604997443479556563612501 155888656895388026739917)
                ·
                  rfl

theorem cell22_4098493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 9].length) (baseStart_4098493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098493 prefixEnd_4098493 := by exact prefixLift 4098493
  have htrace : WordTrace (prefixWord ++ tailWord_4098493) baseStart_4098493 baseEnd_4098493 := by
    simpa [prefixWord, tailWord_4098493, baseEnd_4098493] using wordTrace_append hprefix tailTrace_4098493
  have hstable : (prefixWord ++ tailWord_4098493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098493).length < 2 ^ (prefixWord ++ tailWord_4098493).sum := by decide
  have hdescent : baseEnd_4098493 < baseStart_4098493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098553 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 1, 7]
def baseStart_4098553 : Nat := 118140960795 + 4098553 * 2 ^ 59
def prefixEnd_4098553 : Nat := 4983230072969 + 3 ^ 40 * 4098553 * 2
def baseEnd_4098553 : Nat := 1403018451284672084159069

theorem tailTrace_4098553 : CollatzResearch.WordTrace tailWord_4098553 prefixEnd_4098553 1403018451284672084159069 := by
  unfold tailWord_4098553
  simp only [CollatzResearch.WordTrace]
  refine ⟨149486508720649932969484313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99657672480433288646322875 149486508720649932969484313)
  ·
    refine ⟨112114881540487449727113235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149486508720649932969484313 112114881540487449727113235)
    ·
      refine ⟨168172322310731174590669853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112114881540487449727113235 168172322310731174590669853)
      ·
        refine ⟨63064620866524190471501195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168172322310731174590669853 63064620866524190471501195)
        ·
          refine ⟨94596931299786285707251793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63064620866524190471501195 94596931299786285707251793)
          ·
            refine ⟨70947698474839714280438845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94596931299786285707251793 70947698474839714280438845)
            ·
              refine ⟨26605386928064892855164567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70947698474839714280438845 26605386928064892855164567)
              ·
                refine ⟨39908080392097339282746851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26605386928064892855164567 39908080392097339282746851)
                ·
                  refine ⟨59862120588146008924120277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39908080392097339282746851 59862120588146008924120277)
                  ·
                    refine ⟨1403018451284672084159069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59862120588146008924120277 1403018451284672084159069)
                    ·
                      rfl

theorem cell22_4098553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_4098553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098553 prefixEnd_4098553 := by exact prefixLift 4098553
  have htrace : WordTrace (prefixWord ++ tailWord_4098553) baseStart_4098553 baseEnd_4098553 := by
    simpa [prefixWord, tailWord_4098553, baseEnd_4098553] using wordTrace_append hprefix tailTrace_4098553
  have hstable : (prefixWord ++ tailWord_4098553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098553).length < 2 ^ (prefixWord ++ tailWord_4098553).sum := by decide
  have hdescent : baseEnd_4098553 < baseStart_4098553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098585 : List Nat := [1, 2, 1, 2, 1, 1, 2, 7, 1, 4]
def baseStart_4098585 : Nat := 118140960795 + 4098585 * 2 ^ 59
def prefixEnd_4098585 : Nat := 4983230072969 + 3 ^ 40 * 4098585 * 2
def baseEnd_4098585 : Nat := 1403029405538634667358971

theorem tailTrace_4098585 : CollatzResearch.WordTrace tailWord_4098585 prefixEnd_4098585 1403029405538634667358971 := by
  unfold tailWord_4098585
  simp only [CollatzResearch.WordTrace]
  refine ⟨149487675856534002434649209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99658450571022668289766139 149487675856534002434649209)
  ·
    refine ⟨112115756892400501825986907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149487675856534002434649209 112115756892400501825986907)
    ·
      refine ⟨168173635338600752738980361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112115756892400501825986907 168173635338600752738980361)
      ·
        refine ⟨126130226503950564554235271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168173635338600752738980361 126130226503950564554235271)
        ·
          refine ⟨189195339755925846831352907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126130226503950564554235271 189195339755925846831352907)
          ·
            refine ⟨283793009633888770247029361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189195339755925846831352907 283793009633888770247029361)
            ·
              refine ⟨212844757225416577685272021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283793009633888770247029361 212844757225416577685272021)
              ·
                refine ⟨4988548997470701039498563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 212844757225416577685272021 4988548997470701039498563)
                ·
                  refine ⟨7482823496206051559247845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988548997470701039498563 7482823496206051559247845)
                  ·
                    refine ⟨1403029405538634667358971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7482823496206051559247845 1403029405538634667358971)
                    ·
                      rfl

theorem cell22_4098585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_4098585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098585 prefixEnd_4098585 := by exact prefixLift 4098585
  have htrace : WordTrace (prefixWord ++ tailWord_4098585) baseStart_4098585 baseEnd_4098585 := by
    simpa [prefixWord, tailWord_4098585, baseEnd_4098585] using wordTrace_append hprefix tailTrace_4098585
  have hstable : (prefixWord ++ tailWord_4098585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098585).length < 2 ^ (prefixWord ++ tailWord_4098585).sum := by decide
  have hdescent : baseEnd_4098585 < baseStart_4098585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098634 : List Nat := [3, 1, 2, 1, 1, 6, 1, 3, 4]
def baseStart_4098634 : Nat := 118140960795 + 4098634 * 2 ^ 59
def prefixEnd_4098634 : Nat := 4983230072969 + 3 ^ 40 * 4098634 * 2
def baseEnd_4098634 : Nat := 467682059746671624294607

theorem tailTrace_4098634 : CollatzResearch.WordTrace tailWord_4098634 prefixEnd_4098634 467682059746671624294607 := by
  unfold tailWord_4098634
  simp only [CollatzResearch.WordTrace]
  refine ⟨37372365758339120950795739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99659642022237655868788637 37372365758339120950795739)
  ·
    refine ⟨56058548637508681426193609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37372365758339120950795739 56058548637508681426193609)
    ·
      refine ⟨42043911478131511069645207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56058548637508681426193609 42043911478131511069645207)
      ·
        refine ⟨63065867217197266604467811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42043911478131511069645207 63065867217197266604467811)
        ·
          refine ⟨94598800825795899906701717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63065867217197266604467811 94598800825795899906701717)
          ·
            refine ⟨4434318788709182808126643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94598800825795899906701717 4434318788709182808126643)
            ·
              refine ⟨6651478183063774212189965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4434318788709182808126643 6651478183063774212189965)
              ·
                refine ⟨2494304318648915329571237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6651478183063774212189965 2494304318648915329571237)
                ·
                  refine ⟨467682059746671624294607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2494304318648915329571237 467682059746671624294607)
                  ·
                    rfl

theorem cell22_4098634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_4098634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098634 prefixEnd_4098634 := by exact prefixLift 4098634
  have htrace : WordTrace (prefixWord ++ tailWord_4098634) baseStart_4098634 baseEnd_4098634 := by
    simpa [prefixWord, tailWord_4098634, baseEnd_4098634] using wordTrace_append hprefix tailTrace_4098634
  have hstable : (prefixWord ++ tailWord_4098634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098634).length < 2 ^ (prefixWord ++ tailWord_4098634).sum := by decide
  have hdescent : baseEnd_4098634 < baseStart_4098634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098735 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 8]
def baseStart_4098735 : Nat := 118140960795 + 4098735 * 2 ^ 59
def prefixEnd_4098735 : Nat := 4983230072969 + 3 ^ 40 * 4098735 * 2
def baseEnd_4098735 : Nat := 467693584534694758702837

theorem tailTrace_4098735 : CollatzResearch.WordTrace tailWord_4098735 prefixEnd_4098735 467693584534694758702837 := by
  unfold tailWord_4098735
  simp only [CollatzResearch.WordTrace]
  refine ⟨149493146805990578052609659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99662097870660385368406439 149493146805990578052609659)
  ·
    refine ⟨224239720208985867078914489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149493146805990578052609659 224239720208985867078914489)
    ·
      refine ⟨168179790156739400309185867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224239720208985867078914489 168179790156739400309185867)
      ·
        refine ⟨252269685235109100463778801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168179790156739400309185867 252269685235109100463778801)
        ·
          refine ⟨189202263926331825347834101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252269685235109100463778801 189202263926331825347834101)
          ·
            refine ⟨17737712243093608626359447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189202263926331825347834101 17737712243093608626359447)
            ·
              refine ⟨26606568364640412939539171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17737712243093608626359447 26606568364640412939539171)
              ·
                refine ⟨39909852546960619409308757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26606568364640412939539171 39909852546960619409308757)
                ·
                  refine ⟨467693584534694758702837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39909852546960619409308757 467693584534694758702837)
                  ·
                    rfl

theorem cell22_4098735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 8].length) (baseStart_4098735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098735 prefixEnd_4098735 := by exact prefixLift 4098735
  have htrace : WordTrace (prefixWord ++ tailWord_4098735) baseStart_4098735 baseEnd_4098735 := by
    simpa [prefixWord, tailWord_4098735, baseEnd_4098735] using wordTrace_append hprefix tailTrace_4098735
  have hstable : (prefixWord ++ tailWord_4098735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098735).length < 2 ^ (prefixWord ++ tailWord_4098735).sum := by decide
  have hdescent : baseEnd_4098735 < baseStart_4098735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098795 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 1, 9]
def baseStart_4098795 : Nat := 118140960795 + 4098795 * 2 ^ 59
def prefixEnd_4098795 : Nat := 4983230072969 + 3 ^ 40 * 4098795 * 2
def baseEnd_4098795 : Nat := 1403101292830264119608327

theorem tailTrace_4098795 : CollatzResearch.WordTrace tailWord_4098795 prefixEnd_4098795 1403101292830264119608327 := by
  unfold tailWord_4098795
  simp only [CollatzResearch.WordTrace]
  refine ⟨149495335185773208299793839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99663556790515472199862559 149495335185773208299793839)
  ·
    refine ⟨224243002778659812449690759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149495335185773208299793839 224243002778659812449690759)
    ·
      refine ⟨336364504167989718674536139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224243002778659812449690759 336364504167989718674536139)
      ·
        refine ⟨504546756251984578011804209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336364504167989718674536139 504546756251984578011804209)
        ·
          refine ⟨378410067188988433508853157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504546756251984578011804209 378410067188988433508853157)
          ·
            refine ⟨70951887597935331282909967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 378410067188988433508853157 70951887597935331282909967)
            ·
              refine ⟨106427831396902996924364951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70951887597935331282909967 106427831396902996924364951)
              ·
                refine ⟨159641747095354495386547427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106427831396902996924364951 159641747095354495386547427)
                ·
                  refine ⟨239462620643031743079821141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159641747095354495386547427 239462620643031743079821141)
                  ·
                    refine ⟨1403101292830264119608327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 239462620643031743079821141 1403101292830264119608327)
                    ·
                      rfl

theorem cell22_4098795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 9].length) (baseStart_4098795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098795 prefixEnd_4098795 := by exact prefixLift 4098795
  have htrace : WordTrace (prefixWord ++ tailWord_4098795) baseStart_4098795 baseEnd_4098795 := by
    simpa [prefixWord, tailWord_4098795, baseEnd_4098795] using wordTrace_append hprefix tailTrace_4098795
  have hstable : (prefixWord ++ tailWord_4098795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098795).length < 2 ^ (prefixWord ++ tailWord_4098795).sum := by decide
  have hdescent : baseEnd_4098795 < baseStart_4098795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098797 : List Nat := [1, 5, 1, 2, 1, 1, 3, 8]
def baseStart_4098797 : Nat := 118140960795 + 4098797 * 2 ^ 59
def prefixEnd_4098797 : Nat := 4983230072969 + 3 ^ 40 * 4098797 * 2
def baseEnd_4098797 : Nat := 155900219719015197895369

theorem tailTrace_4098797 : CollatzResearch.WordTrace tailWord_4098797 prefixEnd_4098797 155900219719015197895369 := by
  unfold tailWord_4098797
  simp only [CollatzResearch.WordTrace]
  refine ⟨149495408131765962641366645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99663605421177308427577763 149495408131765962641366645)
  ·
    refine ⟨14015194512353058997628123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149495408131765962641366645 14015194512353058997628123)
    ·
      refine ⟨21022791768529588496442185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14015194512353058997628123 21022791768529588496442185)
      ·
        refine ⟨15767093826397191372331639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21022791768529588496442185 15767093826397191372331639)
        ·
          refine ⟨23650640739595787058497459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15767093826397191372331639 23650640739595787058497459)
          ·
            refine ⟨35475961109393680587746189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23650640739595787058497459 35475961109393680587746189)
            ·
              refine ⟨13303485416022630220404821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35475961109393680587746189 13303485416022630220404821)
              ·
                refine ⟨155900219719015197895369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13303485416022630220404821 155900219719015197895369)
                ·
                  rfl

theorem cell22_4098797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 8].length) (baseStart_4098797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098797 prefixEnd_4098797 := by exact prefixLift 4098797
  have htrace : WordTrace (prefixWord ++ tailWord_4098797) baseStart_4098797 baseEnd_4098797 := by
    simpa [prefixWord, tailWord_4098797, baseEnd_4098797] using wordTrace_append hprefix tailTrace_4098797
  have hstable : (prefixWord ++ tailWord_4098797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098797).length < 2 ^ (prefixWord ++ tailWord_4098797).sum := by decide
  have hdescent : baseEnd_4098797 < baseStart_4098797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098814 : List Nat := [4, 2, 2, 1, 2, 3, 8]
def baseStart_4098814 : Nat := 118140960795 + 4098814 * 2 ^ 59
def prefixEnd_4098814 : Nat := 4983230072969 + 3 ^ 40 * 4098814 * 2
def baseEnd_4098814 : Nat := 51966955441427940866047

theorem tailTrace_4098814 : CollatzResearch.WordTrace tailWord_4098814 prefixEnd_4098814 51966955441427940866047 := by
  unfold tailWord_4098814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18687003521588046818091937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99664018781802916363156997 18687003521588046818091937)
  ·
    refine ⟨14015252641191035113568953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18687003521588046818091937 14015252641191035113568953)
    ·
      refine ⟨10511439480893276335176715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14015252641191035113568953 10511439480893276335176715)
      ·
        refine ⟨15767159221339914502765073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10511439480893276335176715 15767159221339914502765073)
        ·
          refine ⟨11825369416004935877073805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15767159221339914502765073 11825369416004935877073805)
          ·
            refine ⟨4434513531001850953902677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11825369416004935877073805 4434513531001850953902677)
            ·
              refine ⟨51966955441427940866047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4434513531001850953902677 51966955441427940866047)
              ·
                rfl

theorem cell22_4098814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 8].length) (baseStart_4098814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098814 prefixEnd_4098814 := by exact prefixLift 4098814
  have htrace : WordTrace (prefixWord ++ tailWord_4098814) baseStart_4098814 baseEnd_4098814 := by
    simpa [prefixWord, tailWord_4098814, baseEnd_4098814] using wordTrace_append hprefix tailTrace_4098814
  have hstable : (prefixWord ++ tailWord_4098814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098814).length < 2 ^ (prefixWord ++ tailWord_4098814).sum := by decide
  have hdescent : baseEnd_4098814 < baseStart_4098814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098887 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 6]
def baseStart_4098887 : Nat := 118140960795 + 4098887 * 2 ^ 59
def prefixEnd_4098887 : Nat := 4983230072969 + 3 ^ 40 * 4098887 * 2
def baseEnd_4098887 : Nat := 467710928770135515436015

theorem tailTrace_4098887 : CollatzResearch.WordTrace tailWord_4098887 prefixEnd_4098887 467710928770135515436015 := by
  unfold tailWord_4098887
  simp only [CollatzResearch.WordTrace]
  refine ⟨149498690701439908012142915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99665793800959938674761943 149498690701439908012142915)
  ·
    refine ⟨224248036052159862018214373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149498690701439908012142915 224248036052159862018214373)
    ·
      refine ⟨42046506759779974128415195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224248036052159862018214373 42046506759779974128415195)
      ·
        refine ⟨63069760139669961192622793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42046506759779974128415195 63069760139669961192622793)
        ·
          refine ⟨47302320104752470894467095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63069760139669961192622793 47302320104752470894467095)
          ·
            refine ⟨70953480157128706341700643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47302320104752470894467095 70953480157128706341700643)
            ·
              refine ⟨106430220235693059512550965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70953480157128706341700643 106430220235693059512550965)
              ·
                refine ⟨9977833147096224329301653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106430220235693059512550965 9977833147096224329301653)
                ·
                  refine ⟨467710928770135515436015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9977833147096224329301653 467710928770135515436015)
                  ·
                    rfl

theorem cell22_4098887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 6].length) (baseStart_4098887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098887 prefixEnd_4098887 := by exact prefixLift 4098887
  have htrace : WordTrace (prefixWord ++ tailWord_4098887) baseStart_4098887 baseEnd_4098887 := by
    simpa [prefixWord, tailWord_4098887, baseEnd_4098887] using wordTrace_append hprefix tailTrace_4098887
  have hstable : (prefixWord ++ tailWord_4098887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098887).length < 2 ^ (prefixWord ++ tailWord_4098887).sum := by decide
  have hdescent : baseEnd_4098887 < baseStart_4098887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098919 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 1, 5]
def baseStart_4098919 : Nat := 118140960795 + 4098919 * 2 ^ 59
def prefixEnd_4098919 : Nat := 4983230072969 + 3 ^ 40 * 4098919 * 2
def baseEnd_4098919 : Nat := 1403143740564369129507947

theorem tailTrace_4098919 : CollatzResearch.WordTrace tailWord_4098919 prefixEnd_4098919 1403143740564369129507947 := by
  unfold tailWord_4098919
  simp only [CollatzResearch.WordTrace]
  refine ⟨149499857837323977477307811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99666571891549318318205207 149499857837323977477307811)
  ·
    refine ⟨224249786755985966215961717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149499857837323977477307811 224249786755985966215961717)
    ·
      refine ⟨21023417508373684332746411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224249786755985966215961717 21023417508373684332746411)
      ·
        refine ⟨31535126262560526499119617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21023417508373684332746411 31535126262560526499119617)
        ·
          refine ⟨23651344696920394874339713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31535126262560526499119617 23651344696920394874339713)
          ·
            refine ⟨17738508522690296155754785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23651344696920394874339713 17738508522690296155754785)
            ·
              refine ⟨13303881392017722116816089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17738508522690296155754785 13303881392017722116816089)
              ·
                refine ⟨9977911044013291587612067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13303881392017722116816089 9977911044013291587612067)
                ·
                  refine ⟨14966866566019937381418101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9977911044013291587612067 14966866566019937381418101)
                  ·
                    refine ⟨1403143740564369129507947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14966866566019937381418101 1403143740564369129507947)
                    ·
                      rfl

theorem cell22_4098919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_4098919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098919 prefixEnd_4098919 := by exact prefixLift 4098919
  have htrace : WordTrace (prefixWord ++ tailWord_4098919) baseStart_4098919 baseEnd_4098919 := by
    simpa [prefixWord, tailWord_4098919, baseEnd_4098919] using wordTrace_append hprefix tailTrace_4098919
  have hstable : (prefixWord ++ tailWord_4098919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098919).length < 2 ^ (prefixWord ++ tailWord_4098919).sum := by decide
  have hdescent : baseEnd_4098919 < baseStart_4098919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098953 : List Nat := [1, 2, 1, 1, 5, 3, 3, 1, 2, 3]
def baseStart_4098953 : Nat := 118140960795 + 4098953 * 2 ^ 59
def prefixEnd_4098953 : Nat := 4983230072969 + 3 ^ 40 * 4098953 * 2
def baseEnd_4098953 : Nat := 1403155379459204374157843

theorem tailTrace_4098953 : CollatzResearch.WordTrace tailWord_4098953 prefixEnd_4098953 1403155379459204374157843 := by
  unfold tailWord_4098953
  simp only [CollatzResearch.WordTrace]
  refine ⟨149501097919200801284045513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99667398612800534189363675 149501097919200801284045513)
  ·
    refine ⟨112125823439400600963034135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149501097919200801284045513 112125823439400600963034135)
    ·
      refine ⟨168188735159100901444551203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112125823439400600963034135 168188735159100901444551203)
      ·
        refine ⟨252283102738651352166826805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168188735159100901444551203 252283102738651352166826805)
        ·
          refine ⟨23651540881748564265640013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252283102738651352166826805 23651540881748564265640013)
          ·
            refine ⟨8869327830655711599615005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23651540881748564265640013 8869327830655711599615005)
            ·
              refine ⟨3325997936495891849855627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8869327830655711599615005 3325997936495891849855627)
              ·
                refine ⟨4988996904743837774783441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3325997936495891849855627 4988996904743837774783441)
                ·
                  refine ⟨3741747678557878331087581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4988996904743837774783441 3741747678557878331087581)
                  ·
                    refine ⟨1403155379459204374157843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3741747678557878331087581 1403155379459204374157843)
                    ·
                      rfl

theorem cell22_4098953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 2, 3].length) (baseStart_4098953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098953 prefixEnd_4098953 := by exact prefixLift 4098953
  have htrace : WordTrace (prefixWord ++ tailWord_4098953) baseStart_4098953 baseEnd_4098953 := by
    simpa [prefixWord, tailWord_4098953, baseEnd_4098953] using wordTrace_append hprefix tailTrace_4098953
  have hstable : (prefixWord ++ tailWord_4098953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098953).length < 2 ^ (prefixWord ++ tailWord_4098953).sum := by decide
  have hdescent : baseEnd_4098953 < baseStart_4098953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4098964 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_4098964 : Nat := 118140960795 + 4098964 * 2 ^ 59
def prefixEnd_4098964 : Nat := 4983230072969 + 3 ^ 40 * 4098964 * 2
def baseEnd_4098964 : Nat := 1403159144984004012132809

theorem tailTrace_4098964 : CollatzResearch.WordTrace tailWord_4098964 prefixEnd_4098964 1403159144984004012132809 := by
  unfold tailWord_4098964
  simp only [CollatzResearch.WordTrace]
  refine ⟨74750749561080475081347973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99667666081440633441797297 74750749561080475081347973)
  ·
    refine ⟨14015765542702589077752745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74750749561080475081347973 14015765542702589077752745)
    ·
      refine ⟨10511824157026941808314559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14015765542702589077752745 10511824157026941808314559)
      ·
        refine ⟨15767736235540412712471839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10511824157026941808314559 15767736235540412712471839)
        ·
          refine ⟨23651604353310619068707759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15767736235540412712471839 23651604353310619068707759)
          ·
            refine ⟨35477406529965928603061639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23651604353310619068707759 35477406529965928603061639)
            ·
              refine ⟨53216109794948892904592459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35477406529965928603061639 53216109794948892904592459)
              ·
                refine ⟨79824164692423339356888689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53216109794948892904592459 79824164692423339356888689)
                ·
                  refine ⟨59868123519317504517666517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79824164692423339356888689 59868123519317504517666517)
                  ·
                    refine ⟨1403159144984004012132809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59868123519317504517666517 1403159144984004012132809)
                    ·
                      rfl

theorem cell22_4098964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_4098964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4098964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4098964 prefixEnd_4098964 := by exact prefixLift 4098964
  have htrace : WordTrace (prefixWord ++ tailWord_4098964) baseStart_4098964 baseEnd_4098964 := by
    simpa [prefixWord, tailWord_4098964, baseEnd_4098964] using wordTrace_append hprefix tailTrace_4098964
  have hstable : (prefixWord ++ tailWord_4098964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4098964).length < 2 ^ (prefixWord ++ tailWord_4098964).sum := by decide
  have hdescent : baseEnd_4098964 < baseStart_4098964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4098964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099069 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_4099069 : Nat := 118140960795 + 4099069 * 2 ^ 59
def prefixEnd_4099069 : Nat := 4983230072969 + 3 ^ 40 * 4099069 * 2
def baseEnd_4099069 : Nat := 1403195088629818738257487

theorem tailTrace_4099069 : CollatzResearch.WordTrace tailWord_4099069 prefixEnd_4099069 1403195088629818738257487 := by
  unfold tailWord_4099069
  simp only [CollatzResearch.WordTrace]
  refine ⟨149505328786780553095268261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99670219191187035396845507 149505328786780553095268261)
  ·
    refine ⟨28032249147521353705362799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149505328786780553095268261 28032249147521353705362799)
    ·
      refine ⟨42048373721282030558044199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28032249147521353705362799 42048373721282030558044199)
      ·
        refine ⟨63072560581923045837066299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42048373721282030558044199 63072560581923045837066299)
        ·
          refine ⟨94608840872884568755599449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63072560581923045837066299 94608840872884568755599449)
          ·
            refine ⟨70956630654663426566699587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94608840872884568755599449 70956630654663426566699587)
            ·
              refine ⟨106434945981995139850049381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70956630654663426566699587 106434945981995139850049381)
              ·
                refine ⟨19956552371624088721884259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106434945981995139850049381 19956552371624088721884259)
                ·
                  refine ⟨29934828557436133082826389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19956552371624088721884259 29934828557436133082826389)
                  ·
                    refine ⟨1403195088629818738257487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29934828557436133082826389 1403195088629818738257487)
                    ·
                      rfl

theorem cell22_4099069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_4099069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099069 prefixEnd_4099069 := by exact prefixLift 4099069
  have htrace : WordTrace (prefixWord ++ tailWord_4099069) baseStart_4099069 baseEnd_4099069 := by
    simpa [prefixWord, tailWord_4099069, baseEnd_4099069] using wordTrace_append hprefix tailTrace_4099069
  have hstable : (prefixWord ++ tailWord_4099069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099069).length < 2 ^ (prefixWord ++ tailWord_4099069).sum := by decide
  have hdescent : baseEnd_4099069 < baseStart_4099069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099086 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_4099086 : Nat := 118140960795 + 4099086 * 2 ^ 59
def prefixEnd_4099086 : Nat := 4983230072969 + 3 ^ 40 * 4099086 * 2
def baseEnd_4099086 : Nat := 1403200908077236360582435

theorem tailTrace_4099086 : CollatzResearch.WordTrace tailWord_4099086 prefixEnd_4099086 1403200908077236360582435 := by
  unfold tailWord_4099086
  simp only [CollatzResearch.WordTrace]
  refine ⟨18688243603464870624829639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99670632551812643332424741 18688243603464870624829639)
  ·
    refine ⟨28032365405197305937244459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18688243603464870624829639 28032365405197305937244459)
    ·
      refine ⟨42048548107795958905866689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28032365405197305937244459 42048548107795958905866689)
      ·
        refine ⟨31536411080846969179400017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42048548107795958905866689 31536411080846969179400017)
        ·
          refine ⟨23652308310635226884550013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31536411080846969179400017 23652308310635226884550013)
          ·
            refine ⟨8869615616488210081706255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23652308310635226884550013 8869615616488210081706255)
            ·
              refine ⟨13304423424732315122559383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8869615616488210081706255 13304423424732315122559383)
              ·
                refine ⟨19956635137098472683839075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13304423424732315122559383 19956635137098472683839075)
                ·
                  refine ⟨29934952705647709025758613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19956635137098472683839075 29934952705647709025758613)
                  ·
                    refine ⟨1403200908077236360582435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29934952705647709025758613 1403200908077236360582435)
                    ·
                      rfl

theorem cell22_4099086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_4099086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099086 prefixEnd_4099086 := by exact prefixLift 4099086
  have htrace : WordTrace (prefixWord ++ tailWord_4099086) baseStart_4099086 baseEnd_4099086 := by
    simpa [prefixWord, tailWord_4099086, baseEnd_4099086] using wordTrace_append hprefix tailTrace_4099086
  have hstable : (prefixWord ++ tailWord_4099086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099086).length < 2 ^ (prefixWord ++ tailWord_4099086).sum := by decide
  have hdescent : baseEnd_4099086 < baseStart_4099086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099101 : List Nat := [1, 4, 2, 2, 3, 1, 9]
def baseStart_4099101 : Nat := 118140960795 + 4099101 * 2 ^ 59
def prefixEnd_4099101 : Nat := 4983230072969 + 3 ^ 40 * 4099101 * 2
def baseEnd_4099101 : Nat := 51970594180880789683607

theorem tailTrace_4099101 : CollatzResearch.WordTrace tailWord_4099101 prefixEnd_4099101 51970594180880789683607 := by
  unfold tailWord_4099101
  simp only [CollatzResearch.WordTrace]
  refine ⟨149506495922664622560433157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99670997281776415040288771 149506495922664622560433157)
  ·
    refine ⟨28032467985499616730081217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149506495922664622560433157 28032467985499616730081217)
    ·
      refine ⟨21024350989124712547560913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28032467985499616730081217 21024350989124712547560913)
      ·
        refine ⟨15768263241843534410670685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21024350989124712547560913 15768263241843534410670685)
        ·
          refine ⟨5913098715691325404001507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15768263241843534410670685 5913098715691325404001507)
          ·
            refine ⟨8869648073536988106002261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5913098715691325404001507 8869648073536988106002261)
            ·
              refine ⟨51970594180880789683607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8869648073536988106002261 51970594180880789683607)
              ·
                rfl

theorem cell22_4099101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 9].length) (baseStart_4099101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099101 prefixEnd_4099101 := by exact prefixLift 4099101
  have htrace : WordTrace (prefixWord ++ tailWord_4099101) baseStart_4099101 baseEnd_4099101 := by
    simpa [prefixWord, tailWord_4099101, baseEnd_4099101] using wordTrace_append hprefix tailTrace_4099101
  have hstable : (prefixWord ++ tailWord_4099101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099101).length < 2 ^ (prefixWord ++ tailWord_4099101).sum := by decide
  have hdescent : baseEnd_4099101 < baseStart_4099101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099105 : List Nat := [1, 2, 3, 2, 3, 3, 1, 2, 2, 3]
def baseStart_4099105 : Nat := 118140960795 + 4099105 * 2 ^ 59
def prefixEnd_4099105 : Nat := 4983230072969 + 3 ^ 40 * 4099105 * 2
def baseEnd_4099105 : Nat := 1403207412165526644357377

theorem tailTrace_4099105 : CollatzResearch.WordTrace tailWord_4099105 prefixEnd_4099105 1403207412165526644357377 := by
  unfold tailWord_4099105
  simp only [CollatzResearch.WordTrace]
  refine ⟨149506641814650131243578769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99671094543100087495719179 149506641814650131243578769)
  ·
    refine ⟨112129981360987598432684077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149506641814650131243578769 112129981360987598432684077)
    ·
      refine ⟨42048743010370349412256529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112129981360987598432684077 42048743010370349412256529)
      ·
        refine ⟨31536557257777762059192397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42048743010370349412256529 31536557257777762059192397)
        ·
          refine ⟨11826208971666660772197149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31536557257777762059192397 11826208971666660772197149)
          ·
            refine ⟨4434828364374997789573931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11826208971666660772197149 4434828364374997789573931)
            ·
              refine ⟨6652242546562496684360897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4434828364374997789573931 6652242546562496684360897)
              ·
                refine ⟨4989181909921872513270673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6652242546562496684360897 4989181909921872513270673)
                ·
                  refine ⟨3741886432441404384953005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4989181909921872513270673 3741886432441404384953005)
                  ·
                    refine ⟨1403207412165526644357377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3741886432441404384953005 1403207412165526644357377)
                    ·
                      rfl

theorem cell22_4099105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_4099105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099105 prefixEnd_4099105 := by exact prefixLift 4099105
  have htrace : WordTrace (prefixWord ++ tailWord_4099105) baseStart_4099105 baseEnd_4099105 := by
    simpa [prefixWord, tailWord_4099105, baseEnd_4099105] using wordTrace_append hprefix tailTrace_4099105
  have hstable : (prefixWord ++ tailWord_4099105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099105).length < 2 ^ (prefixWord ++ tailWord_4099105).sum := by decide
  have hdescent : baseEnd_4099105 < baseStart_4099105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099133 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 3, 3]
def baseStart_4099133 : Nat := 118140960795 + 4099133 * 2 ^ 59
def prefixEnd_4099133 : Nat := 4983230072969 + 3 ^ 40 * 4099133 * 2
def baseEnd_4099133 : Nat := 1403216997137743904657291

theorem tailTrace_4099133 : CollatzResearch.WordTrace tailWord_4099133 prefixEnd_4099133 1403216997137743904657291 := by
  unfold tailWord_4099133
  simp only [CollatzResearch.WordTrace]
  refine ⟨149507663058548692025598053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99671775372365794683732035 149507663058548692025598053)
  ·
    refine ⟨28032686823477879754799635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149507663058548692025598053 28032686823477879754799635)
    ·
      refine ⟨42049030235216819632199453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28032686823477879754799635 42049030235216819632199453)
      ·
        refine ⟨15768386338206307362074795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42049030235216819632199453 15768386338206307362074795)
        ·
          refine ⟨23652579507309461043112193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15768386338206307362074795 23652579507309461043112193)
          ·
            refine ⟨17739434630482095782334145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23652579507309461043112193 17739434630482095782334145)
            ·
              refine ⟨13304575972861571836750609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17739434630482095782334145 13304575972861571836750609)
              ·
                refine ⟨9978431979646178877562957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13304575972861571836750609 9978431979646178877562957)
                ·
                  refine ⟨3741911992367317079086109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9978431979646178877562957 3741911992367317079086109)
                  ·
                    refine ⟨1403216997137743904657291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3741911992367317079086109 1403216997137743904657291)
                    ·
                      rfl

theorem cell22_4099133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_4099133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099133 prefixEnd_4099133 := by exact prefixLift 4099133
  have htrace : WordTrace (prefixWord ++ tailWord_4099133) baseStart_4099133 baseEnd_4099133 := by
    simpa [prefixWord, tailWord_4099133, baseEnd_4099133] using wordTrace_append hprefix tailTrace_4099133
  have hstable : (prefixWord ++ tailWord_4099133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099133).length < 2 ^ (prefixWord ++ tailWord_4099133).sum := by decide
  have hdescent : baseEnd_4099133 < baseStart_4099133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099193 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 3, 4]
def baseStart_4099193 : Nat := 118140960795 + 4099193 * 2 ^ 59
def prefixEnd_4099193 : Nat := 4983230072969 + 3 ^ 40 * 4099193 * 2
def baseEnd_4099193 : Nat := 1403237536363923748157107

theorem tailTrace_4099193 : CollatzResearch.WordTrace tailWord_4099193 prefixEnd_4099193 1403237536363923748157107 := by
  unfold tailWord_4099193
  simp only [CollatzResearch.WordTrace]
  refine ⟨149509851438331322272782233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99673234292220881515188155 149509851438331322272782233)
  ·
    refine ⟨112132388578748491704586675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149509851438331322272782233 112132388578748491704586675)
    ·
      refine ⟨168198582868122737556880013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112132388578748491704586675 168198582868122737556880013)
      ·
        refine ⟨63074468575546026583830005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168198582868122737556880013 63074468575546026583830005)
        ·
          refine ⟨5913231428957439992234063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63074468575546026583830005 5913231428957439992234063)
          ·
            refine ⟨8869847143436159988351095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5913231428957439992234063 8869847143436159988351095)
            ·
              refine ⟨13304770715154239982526643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8869847143436159988351095 13304770715154239982526643)
              ·
                refine ⟨19957156072731359973789965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13304770715154239982526643 19957156072731359973789965)
                ·
                  refine ⟨7483933527274259990171237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19957156072731359973789965 7483933527274259990171237)
                  ·
                    refine ⟨1403237536363923748157107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7483933527274259990171237 1403237536363923748157107)
                    ·
                      rfl

theorem cell22_4099193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_4099193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099193 prefixEnd_4099193 := by exact prefixLift 4099193
  have htrace : WordTrace (prefixWord ++ tailWord_4099193) baseStart_4099193 baseEnd_4099193 := by
    simpa [prefixWord, tailWord_4099193, baseEnd_4099193] using wordTrace_append hprefix tailTrace_4099193
  have hstable : (prefixWord ++ tailWord_4099193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099193).length < 2 ^ (prefixWord ++ tailWord_4099193).sum := by decide
  have hdescent : baseEnd_4099193 < baseStart_4099193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099210 : List Nat := [3, 1, 2, 3, 1, 1, 5, 1, 1, 4]
def baseStart_4099210 : Nat := 118140960795 + 4099210 * 2 ^ 59
def prefixEnd_4099210 : Nat := 4983230072969 + 3 ^ 40 * 4099210 * 2
def baseEnd_4099210 : Nat := 1403243355811341370482055

theorem tailTrace_4099210 : CollatzResearch.WordTrace tailWord_4099210 prefixEnd_4099210 1403243355811341370482055 := by
  unfold tailWord_4099210
  simp only [CollatzResearch.WordTrace]
  refine ⟨37377617869817433544037771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99673647652846489450767389 37377617869817433544037771)
  ·
    refine ⟨56066426804726150316056657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37377617869817433544037771 56066426804726150316056657)
    ·
      refine ⟨42049820103544612737042493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56066426804726150316056657 42049820103544612737042493)
      ·
        refine ⟨15768682538829229776390935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42049820103544612737042493 15768682538829229776390935)
        ·
          refine ⟨23653023808243844664586403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15768682538829229776390935 23653023808243844664586403)
          ·
            refine ⟨35479535712365766996879605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23653023808243844664586403 35479535712365766996879605)
            ·
              refine ⟨3326206473034290655957463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35479535712365766996879605 3326206473034290655957463)
              ·
                refine ⟨4989309709551435983936195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3326206473034290655957463 4989309709551435983936195)
                ·
                  refine ⟨7483964564327153975904293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989309709551435983936195 7483964564327153975904293)
                  ·
                    refine ⟨1403243355811341370482055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7483964564327153975904293 1403243355811341370482055)
                    ·
                      rfl

theorem cell22_4099210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_4099210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099210 prefixEnd_4099210 := by exact prefixLift 4099210
  have htrace : WordTrace (prefixWord ++ tailWord_4099210) baseStart_4099210 baseEnd_4099210 := by
    simpa [prefixWord, tailWord_4099210, baseEnd_4099210] using wordTrace_append hprefix tailTrace_4099210
  have hstable : (prefixWord ++ tailWord_4099210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099210).length < 2 ^ (prefixWord ++ tailWord_4099210).sum := by decide
  have hdescent : baseEnd_4099210 < baseStart_4099210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099221 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 4, 4]
def baseStart_4099221 : Nat := 118140960795 + 4099221 * 2 ^ 59
def prefixEnd_4099221 : Nat := 4983230072969 + 3 ^ 40 * 4099221 * 2
def baseEnd_4099221 : Nat := 1403247121336141008457021

theorem tailTrace_4099221 : CollatzResearch.WordTrace tailWord_4099221 prefixEnd_4099221 1403247121336141008457021 := by
  unfold tailWord_4099221
  simp only [CollatzResearch.WordTrace]
  refine ⟨149510872682229883054801517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99673915121486588703201011 149510872682229883054801517)
  ·
    refine ⟨56066577255836206145550569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149510872682229883054801517 56066577255836206145550569)
    ·
      refine ⟨42049932941877154609162927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56066577255836206145550569 42049932941877154609162927)
      ·
        refine ⟨63074899412815731913744391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42049932941877154609162927 63074899412815731913744391)
        ·
          refine ⟨94612349119223597870616587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63074899412815731913744391 94612349119223597870616587)
          ·
            refine ⟨141918523678835396805924881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94612349119223597870616587 141918523678835396805924881)
            ·
              refine ⟨106438892759126547604443661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141918523678835396805924881 106438892759126547604443661)
              ·
                refine ⟨39914584784672455351666373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106438892759126547604443661 39914584784672455351666373)
                ·
                  refine ⟨7483984647126085378437445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39914584784672455351666373 7483984647126085378437445)
                  ·
                    refine ⟨1403247121336141008457021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7483984647126085378437445 1403247121336141008457021)
                    ·
                      rfl

theorem cell22_4099221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_4099221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099221 prefixEnd_4099221 := by exact prefixLift 4099221
  have htrace : WordTrace (prefixWord ++ tailWord_4099221) baseStart_4099221 baseEnd_4099221 := by
    simpa [prefixWord, tailWord_4099221, baseEnd_4099221] using wordTrace_append hprefix tailTrace_4099221
  have hstable : (prefixWord ++ tailWord_4099221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099221).length < 2 ^ (prefixWord ++ tailWord_4099221).sum := by decide
  have hdescent : baseEnd_4099221 < baseStart_4099221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099285 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 3, 3]
def baseStart_4099285 : Nat := 118140960795 + 4099285 * 2 ^ 59
def prefixEnd_4099285 : Nat := 4983230072969 + 3 ^ 40 * 4099285 * 2
def baseEnd_4099285 : Nat := 1403269029844066174856825

theorem tailTrace_4099285 : CollatzResearch.WordTrace tailWord_4099285 prefixEnd_4099285 1403269029844066174856825 := by
  unfold tailWord_4099285
  simp only [CollatzResearch.WordTrace]
  refine ⟨149513206953998021985131309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99675471302665347990087539 149513206953998021985131309)
  ·
    refine ⟨56067452607749258244424241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149513206953998021985131309 56067452607749258244424241)
    ·
      refine ⟨42050589455811943683318181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56067452607749258244424241 42050589455811943683318181)
      ·
        refine ⟨7884485522964739440622159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42050589455811943683318181 7884485522964739440622159)
        ·
          refine ⟨11826728284447109160933239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7884485522964739440622159 11826728284447109160933239)
          ·
            refine ⟨17740092426670663741399859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11826728284447109160933239 17740092426670663741399859)
            ·
              refine ⟨26610138640005995612099789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17740092426670663741399859 26610138640005995612099789)
              ·
                refine ⟨9978801990002248354537421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26610138640005995612099789 9978801990002248354537421)
                ·
                  refine ⟨3742050746250843132951533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9978801990002248354537421 3742050746250843132951533)
                  ·
                    refine ⟨1403269029844066174856825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3742050746250843132951533 1403269029844066174856825)
                    ·
                      rfl

theorem cell22_4099285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_4099285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099285 prefixEnd_4099285 := by exact prefixLift 4099285
  have htrace : WordTrace (prefixWord ++ tailWord_4099285) baseStart_4099285 baseEnd_4099285 := by
    simpa [prefixWord, tailWord_4099285, baseEnd_4099285] using wordTrace_append hprefix tailTrace_4099285
  have hstable : (prefixWord ++ tailWord_4099285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099285).length < 2 ^ (prefixWord ++ tailWord_4099285).sum := by decide
  have hdescent : baseEnd_4099285 < baseStart_4099285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099390 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_4099390 : Nat := 118140960795 + 4099390 * 2 ^ 59
def prefixEnd_4099390 : Nat := 4983230072969 + 3 ^ 40 * 4099390 * 2
def baseEnd_4099390 : Nat := 1403304973489880900981503

theorem tailTrace_4099390 : CollatzResearch.WordTrace tailWord_4099390 prefixEnd_4099390 1403304973489880900981503 := by
  unfold tailWord_4099390
  simp only [CollatzResearch.WordTrace]
  refine ⟨18689629577327203114712953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99678024412411749945135749 18689629577327203114712953)
  ·
    refine ⟨14017222182995402336034715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18689629577327203114712953 14017222182995402336034715)
    ·
      refine ⟨21025833274493103504052073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14017222182995402336034715 21025833274493103504052073)
      ·
        refine ⟨15769374955869827628039055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21025833274493103504052073 15769374955869827628039055)
        ·
          refine ⟨23654062433804741442058583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15769374955869827628039055 23654062433804741442058583)
          ·
            refine ⟨35481093650707112163087875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23654062433804741442058583 35481093650707112163087875)
            ·
              refine ⟨53221640476060668244631813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35481093650707112163087875 53221640476060668244631813)
              ·
                refine ⟨9979057589261375295868465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53221640476060668244631813 9979057589261375295868465)
                ·
                  refine ⟨7484293191946031471901349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9979057589261375295868465 7484293191946031471901349)
                  ·
                    refine ⟨1403304973489880900981503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7484293191946031471901349 1403304973489880900981503)
                    ·
                      rfl

theorem cell22_4099390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_4099390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099390 prefixEnd_4099390 := by exact prefixLift 4099390
  have htrace : WordTrace (prefixWord ++ tailWord_4099390) baseStart_4099390 baseEnd_4099390 := by
    simpa [prefixWord, tailWord_4099390, baseEnd_4099390] using wordTrace_append hprefix tailTrace_4099390
  have hstable : (prefixWord ++ tailWord_4099390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099390).length < 2 ^ (prefixWord ++ tailWord_4099390).sum := by decide
  have hdescent : baseEnd_4099390 < baseStart_4099390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099523 : List Nat := [1, 1, 1, 3, 1, 1, 5, 9]
def baseStart_4099523 : Nat := 118140960795 + 4099523 * 2 ^ 59
def prefixEnd_4099523 : Nat := 4983230072969 + 3 ^ 40 * 4099523 * 2
def baseEnd_4099523 : Nat := 155927833567545876378455

theorem tailTrace_4099523 : CollatzResearch.WordTrace tailWord_4099523 prefixEnd_4099523 155927833567545876378455 := by
  unfold tailWord_4099523
  simp only [CollatzResearch.WordTrace]
  refine ⟨149521887527135788632295223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99681258351423859088196815 149521887527135788632295223)
  ·
    refine ⟨224282831290703682948442835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149521887527135788632295223 224282831290703682948442835)
    ·
      refine ⟨336424246936055524422664253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224282831290703682948442835 336424246936055524422664253)
      ·
        refine ⟨126159092601020821658499095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336424246936055524422664253 126159092601020821658499095)
        ·
          refine ⟨189238638901531232487748643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126159092601020821658499095 189238638901531232487748643)
          ·
            refine ⟨283857958352296848731622965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189238638901531232487748643 283857958352296848731622965)
            ·
              refine ⟨26611683595527829568589653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283857958352296848731622965 26611683595527829568589653)
              ·
                refine ⟨155927833567545876378455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26611683595527829568589653 155927833567545876378455)
                ·
                  rfl

theorem cell22_4099523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 9].length) (baseStart_4099523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099523 prefixEnd_4099523 := by exact prefixLift 4099523
  have htrace : WordTrace (prefixWord ++ tailWord_4099523) baseStart_4099523 baseEnd_4099523 := by
    simpa [prefixWord, tailWord_4099523, baseEnd_4099523] using wordTrace_append hprefix tailTrace_4099523
  have hstable : (prefixWord ++ tailWord_4099523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099523).length < 2 ^ (prefixWord ++ tailWord_4099523).sum := by decide
  have hdescent : baseEnd_4099523 < baseStart_4099523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099527 : List Nat := [1, 1, 4, 1, 1, 3, 3, 3, 2, 3]
def baseStart_4099527 : Nat := 118140960795 + 4099527 * 2 ^ 59
def prefixEnd_4099527 : Nat := 4983230072969 + 3 ^ 40 * 4099527 * 2
def baseEnd_4099527 : Nat := 1403351871389658210306083

theorem tailTrace_4099527 : CollatzResearch.WordTrace tailWord_4099527 prefixEnd_4099527 1403351871389658210306083 := by
  unfold tailWord_4099527
  simp only [CollatzResearch.WordTrace]
  refine ⟨149522033419121297315440835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99681355612747531543627223 149522033419121297315440835)
  ·
    refine ⟨224283050128681945973161253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149522033419121297315440835 224283050128681945973161253)
    ·
      refine ⟨42053071899127864869967735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224283050128681945973161253 42053071899127864869967735)
      ·
        refine ⟨63079607848691797304951603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42053071899127864869967735 63079607848691797304951603)
        ·
          refine ⟨94619411773037695957427405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63079607848691797304951603 94619411773037695957427405)
          ·
            refine ⟨35482279414889135984035277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94619411773037695957427405 35482279414889135984035277)
            ·
              refine ⟨13305854780583425994013229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35482279414889135984035277 13305854780583425994013229)
              ·
                refine ⟨4989695542718784747754961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13305854780583425994013229 4989695542718784747754961)
                ·
                  refine ⟨3742271657039088560816221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4989695542718784747754961 3742271657039088560816221)
                  ·
                    refine ⟨1403351871389658210306083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3742271657039088560816221 1403351871389658210306083)
                    ·
                      rfl

theorem cell22_4099527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_4099527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099527 prefixEnd_4099527 := by exact prefixLift 4099527
  have htrace : WordTrace (prefixWord ++ tailWord_4099527) baseStart_4099527 baseEnd_4099527 := by
    simpa [prefixWord, tailWord_4099527, baseEnd_4099527] using wordTrace_append hprefix tailTrace_4099527
  have hstable : (prefixWord ++ tailWord_4099527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099527).length < 2 ^ (prefixWord ++ tailWord_4099527).sum := by decide
  have hdescent : baseEnd_4099527 < baseStart_4099527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
